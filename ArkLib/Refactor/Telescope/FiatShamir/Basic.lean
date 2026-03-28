/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Telescope.Basic

/-!
# Telescope Fiat-Shamir Basics

Typed replay-oracle infrastructure for messages-only Fiat-Shamir over `ProtocolCtx`.

The key replacement for list-based `FSIdx` is a typed cursor that points to "the next
challenge after this dependent prefix". Earlier prover messages and verifier challenges
are carried in the cursor so the suffix protocol remains well-typed, while the cursor's
`MessageData` view erases those earlier verifier challenges from the hash payload.
-/

namespace ProtocolCtx
namespace FiatShamir

/-- Typed cursor to a verifier-challenge node of a telescopic protocol. A challenge node
is represented by either the current node (`here`) or a concrete challenge value together
with a cursor into the selected suffix. -/
def ChallengeCursor : ProtocolCtx → Type
  | .nil => PEmpty
  | .P_to_V T _ rest => (msg : T) × ChallengeCursor (rest msg)
  | .V_to_P T rest => PUnit ⊕ ((chal : T) × ChallengeCursor (rest chal))

namespace ChallengeCursor

/-- Cursor for the current verifier-challenge node. -/
def here {T : Type} {rest : T → ProtocolCtx} : ChallengeCursor (.V_to_P T rest) :=
  Sum.inl PUnit.unit

/-- Extend a cursor past a prover message. -/
def message {T : Type} {oi : OracleInterface T} {rest : T → ProtocolCtx}
    (msg : T) (tail : ChallengeCursor (rest msg)) :
    ChallengeCursor (.P_to_V T oi rest) :=
  ⟨msg, tail⟩

/-- Extend a cursor past a verifier challenge. -/
def challenge {T : Type} {rest : T → ProtocolCtx}
    (chal : T) (tail : ChallengeCursor (rest chal)) :
    ChallengeCursor (.V_to_P T rest) :=
  Sum.inr ⟨chal, tail⟩

/-- The challenge type selected by a cursor. -/
def Response : {ctx : ProtocolCtx} → ChallengeCursor ctx → Type
  | .nil, q => nomatch q
  | .P_to_V _ _ _, ⟨_, tail⟩ => Response tail
  | .V_to_P T _, .inl _ => T
  | .V_to_P _ _, .inr ⟨_, tail⟩ => Response tail

/-- Number of exchanged values in the prefix preceding the queried challenge. -/
def depth : {ctx : ProtocolCtx} → ChallengeCursor ctx → Nat
  | .nil, q => nomatch q
  | .P_to_V _ _ _, ⟨_, tail⟩ => depth tail + 1
  | .V_to_P _ _, .inl _ => 0
  | .V_to_P _ _, .inr ⟨_, tail⟩ => depth tail + 1

/-- The full dependent prefix transcript preceding the queried challenge. -/
def partialTranscript :
    {ctx : ProtocolCtx} → (q : ChallengeCursor ctx) → PartialTranscript ctx q.depth
  | .nil, q => nomatch q
  | .P_to_V _ _ _, ⟨msg, tail⟩ => ⟨msg, partialTranscript tail⟩
  | .V_to_P _ _, .inl _ => PUnit.unit
  | .V_to_P _ _, .inr ⟨chal, tail⟩ => ⟨chal, partialTranscript tail⟩

/-- Challenge-erased view of the prover-message data contained in a cursor prefix. -/
def MessageData : {ctx : ProtocolCtx} → ChallengeCursor ctx → Type
  | .nil, q => nomatch q
  | .P_to_V T _ _, ⟨_, tail⟩ => T × MessageData tail
  | .V_to_P _ _, .inl _ => PUnit
  | .V_to_P _ _, .inr ⟨_, tail⟩ => MessageData tail

/-- Reify the prover-message data contained in a cursor prefix. -/
def messageData : {ctx : ProtocolCtx} → (q : ChallengeCursor ctx) → MessageData q
  | .nil, q => nomatch q
  | .P_to_V _ _ _, ⟨msg, tail⟩ => ⟨msg, messageData tail⟩
  | .V_to_P _ _, .inl _ => PUnit.unit
  | .V_to_P _ _, .inr ⟨_, tail⟩ => messageData tail

instance instMessageDataOracleInterface :
    {ctx : ProtocolCtx} → (q : ChallengeCursor ctx) → OracleInterface (MessageData q)
  | .nil, q => nomatch q
  | .P_to_V T oi _, ⟨_, tail⟩ => by
      let _ : OracleInterface T := oi
      let _ : OracleInterface (MessageData tail) := instMessageDataOracleInterface tail
      simpa [MessageData] using
        (inferInstance : OracleInterface (T × MessageData tail))
  | .V_to_P _ _, .inl _ => OracleInterface.instDefault
  | .V_to_P _ _, .inr ⟨_, tail⟩ => instMessageDataOracleInterface tail

/-- Lift a challenge cursor on a dependent suffix back to the root protocol by
prepending a concrete prefix transcript. -/
def lift :
    {ctx : ProtocolCtx} → (n : Nat) → (ptr : PartialTranscript ctx n) →
    ChallengeCursor (PartialTranscript.remaining n ctx ptr) → ChallengeCursor ctx
  | _, 0, _, q => q
  | .nil, _ + 1, _, q => nomatch q
  | .P_to_V _ _ _, n + 1, ⟨msg, ptr⟩, q => message msg (lift n ptr q)
  | .V_to_P _ _, n + 1, ⟨chal, ptr⟩, q => challenge chal (lift n ptr q)

end ChallengeCursor

/-- Abstract replay oracle for the challenge nodes of a fixed telescopic protocol. -/
@[ext] structure ReplayOracle (ctx : ProtocolCtx) where
  lookup : (q : ChallengeCursor ctx) → ChallengeCursor.Response q

namespace ReplayOracle

instance {ctx : ProtocolCtx} : OracleInterface (ReplayOracle ctx) where
  Query := ChallengeCursor ctx
  toOC.spec := fun q => ULift (ChallengeCursor.Response q)
  toOC.impl q := do
    return ULift.up ((← read).lookup q)

/-- Restrict a replay oracle after observing a prover message. -/
def afterMessage
    {T : Type} {oi : OracleInterface T} {rest : T → ProtocolCtx}
    (rho : ReplayOracle (.P_to_V T oi rest))
    (msg : T) :
    ReplayOracle (rest msg) where
  lookup := fun q => rho.lookup (.message msg q)

/-- Restrict a replay oracle after fixing a verifier challenge. -/
def afterChallenge
    {T : Type} {rest : T → ProtocolCtx}
    (rho : ReplayOracle (.V_to_P T rest))
    (chal : T) :
    ReplayOracle (rest chal) where
  lookup := fun q => rho.lookup (.challenge chal q)

/-- Restrict a replay oracle to a dependent suffix selected by a concrete prefix. -/
def restrict
    {ctx : ProtocolCtx}
    (rho : ReplayOracle ctx) :
    (n : Nat) → (ptr : PartialTranscript ctx n) →
    ReplayOracle (PartialTranscript.remaining n ctx ptr)
  | 0, _ => rho
  | n + 1, ptr => by
      cases ctx with
      | nil =>
          cases ptr
          exact {
            lookup := fun q => nomatch q
          }
      | P_to_V T oi rest =>
          rcases ptr with ⟨msg, ptr⟩
          exact restrict (rho.afterMessage msg) n ptr
      | V_to_P T rest =>
          rcases ptr with ⟨chal, ptr⟩
          exact restrict (rho.afterChallenge chal) n ptr

/-- The current challenge selected by a replay oracle at the head challenge node. -/
def head
    {T : Type} {rest : T → ProtocolCtx}
    (rho : ReplayOracle (.V_to_P T rest)) : T :=
  rho.lookup .here

end ReplayOracle

/-- Generic messages-only proof family indexed by a concrete replay oracle. Prover
messages are stored explicitly, while verifier challenges are recovered from the
ambient replay oracle and therefore contribute no proof data. -/
def MessagesOnly : (ctx : ProtocolCtx) → ReplayOracle ctx → Type
  | .nil, _ => PUnit
  | .P_to_V T _ rest, rho =>
      (msg : T) × MessagesOnly (rest msg) (rho.afterMessage msg)
  | .V_to_P T rest, rho =>
      let chal : T := rho.head
      MessagesOnly (rest chal) (rho.afterChallenge chal)

namespace MessagesOnly

/-- Reconstruct the full dependent interactive transcript from a messages-only proof
and a replay oracle. -/
def deriveTranscript : {ctx : ProtocolCtx} → (rho : ReplayOracle ctx) →
    MessagesOnly ctx rho → Transcript ctx
  | .nil, _, _ => PUnit.unit
  | .P_to_V _ _ _, rho, ⟨msg, proof⟩ =>
      ⟨msg, deriveTranscript (rho.afterMessage msg) proof⟩
  | .V_to_P T _, rho, proof =>
      let chal : T := rho.head
      ⟨chal, deriveTranscript (rho.afterChallenge chal) proof⟩

/-- Trivial oracle interface for a bundled messages-only proof. -/
def trivialOracleInterface
    (ctx : ProtocolCtx) (rho : ReplayOracle ctx) :
    OracleInterface (MessagesOnly ctx rho) where
  Query := PEmpty
  toOC.spec := fun q => PEmpty.elim q
  toOC.impl := fun q => PEmpty.elim q

end MessagesOnly

end FiatShamir
end ProtocolCtx
