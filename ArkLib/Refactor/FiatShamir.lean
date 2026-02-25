/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Reduction

/-!
# The Fiat-Shamir Transformation (List-Based Refactored)

The Fiat-Shamir transform converts a public-coin interactive reduction into a
non-interactive reduction in the random oracle model.

## Design

The FS oracle is defined by structural recursion on `pSpec` with an accumulator
`acc : List Type` tracking message types seen so far:
- `P_to_V T` rounds extend `acc` without adding an oracle entry.
- `V_to_P T` rounds add a challenge oracle: `(StmtIn × HVector id acc) → T`.

The `V_to_P` case uses `Sum.elim` (= `OracleSpec.add`) so VCVio's `SubSpec`
instances (`subSpec_add_right`) resolve automatically for oracle lifting.

## Main definitions

- `FSIdx` / `fsOracleSpec` / `fsChallengeOracle` — per-round FS challenge oracle
- `Prover.runFS` — run a prover deriving challenges from the FS oracle
- `Messages.deriveTranscript` — reconstruct transcript from messages + FS oracle
- `fsProtocolSpec` — single-message non-interactive protocol spec
- `Reduction.fiatShamir` — the full Fiat-Shamir transformation
-/

open OracleComp OracleSpec

namespace ProtocolSpec

/-! ## Fiat-Shamir Oracle Specification -/

/-- Index type for FS oracle queries: nested sum with one entry per `V_to_P` round.
`P_to_V` rounds simply extend the accumulator without adding a query index. -/
@[reducible]
def FSIdx (StmtIn : Type) : List Type → ProtocolSpec → Type
  | _, [] => PEmpty
  | acc, (.P_to_V T _) :: tl => FSIdx StmtIn (acc ++ [T]) tl
  | acc, (.V_to_P _) :: tl => (StmtIn × HVector id acc) ⊕ FSIdx StmtIn acc tl

/-- FS oracle spec: maps each `V_to_P` round's query to its challenge type.
The `V_to_P` case is `Sum.elim`, which is definitionally `OracleSpec.add`. -/
@[reducible]
def fsOracleSpec (StmtIn : Type) : (acc : List Type) → (pSpec : ProtocolSpec) →
    OracleSpec (FSIdx StmtIn acc pSpec)
  | _, [] => (PEmpty.elim ·)
  | acc, (.P_to_V T _) :: tl => fsOracleSpec StmtIn (acc ++ [T]) tl
  | acc, (.V_to_P T) :: tl =>
    Sum.elim (fun (_ : StmtIn × HVector id acc) => T) (fsOracleSpec StmtIn acc tl)

/-- Top-level FS challenge oracle (accumulator starts empty). -/
abbrev fsChallengeOracle (StmtIn : Type) (pSpec : ProtocolSpec) :=
  fsOracleSpec StmtIn [] pSpec

/-! ## Lifting Helper

In the `V_to_P` recursive case, the tail oracle spec `fsOracleSpec acc tl` must be
lifted into the full spec `fsOracleSpec acc (.V_to_P T :: tl)`. Since the latter
unfolds to `Sum.elim (fun _ => T) (fsOracleSpec acc tl)`, the tail spec embeds as
the right summand. We lift the *combined* `oSpec + fsOracleSpec acc tl` into
`oSpec + fsOracleSpec acc (.V_to_P T :: tl)` by routing `oSpec` queries to `Sum.inl`
and `fsOracleSpec acc tl` queries to `Sum.inr ∘ Sum.inr`. -/

private def liftFSTail {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) (acc : List Type) (T : Type) (tl : ProtocolSpec) :
    QueryImpl (oSpec + fsOracleSpec StmtIn acc tl)
      (OracleComp (oSpec + fsOracleSpec StmtIn acc ((.V_to_P T) :: tl))) :=
  fun
    | .inl q => liftM (query (.inl q) :
        OracleQuery (oSpec + fsOracleSpec StmtIn acc ((.V_to_P T) :: tl)) _)
    | .inr q => liftM (query (.inr (.inr q)) :
        OracleQuery (oSpec + fsOracleSpec StmtIn acc ((.V_to_P T) :: tl)) _)

/-! ## Prover FS Execution -/

/-- Run a prover with Fiat-Shamir challenge derivation.

At each `P_to_V` round the message is extracted normally and added to the
accumulator. At each `V_to_P` round the FS oracle is queried with
`(stmt, accumulated messages)` to derive the challenge. -/
def Prover.runFS {ι : Type} {oSpec : OracleSpec ι}
    {Output StmtIn : Type} (stmt : StmtIn) :
    (acc : List Type) → (pSpec : ProtocolSpec) →
    Prover (OracleComp oSpec) Output pSpec →
    HVector id acc →
    OracleComp (oSpec + fsOracleSpec StmtIn acc pSpec) (Messages pSpec × Output)
  | _, [], output, _ => pure (HVector.nil, output)
  | acc, (.P_to_V T _) :: tl, prover, accMsgs => do
    let (msg, cont) := prover
    let next ← liftM cont
    let (msgs, out) ← Prover.runFS stmt (acc ++ [T]) tl next (HVector.snoc accMsgs msg)
    return (msg ::ₕ msgs, out)
  | acc, (.V_to_P T) :: tl, prover, accMsgs => do
    let chal : T ← liftM (query
      (spec := oSpec + fsOracleSpec StmtIn acc ((.V_to_P T) :: tl))
      (.inr (.inl (stmt, accMsgs))))
    let next ← liftM (prover chal)
    let (msgs, out) ← simulateQ (liftFSTail oSpec StmtIn acc T tl)
      (Prover.runFS stmt acc tl next accMsgs)
    return (msgs, out)

/-! ## Transcript Derivation -/

/-- Derive the full transcript from messages by querying the FS oracle for
each challenge. The verifier-side counterpart to `Prover.runFS`. -/
def Messages.deriveTranscript {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} (stmt : StmtIn) :
    (acc : List Type) → (pSpec : ProtocolSpec) →
    HVector id acc → Messages pSpec →
    OracleComp (oSpec + fsOracleSpec StmtIn acc pSpec) (Transcript pSpec)
  | _, [], _, _ => pure HVector.nil
  | acc, (.P_to_V T _) :: tl, accMsgs, msgs => do
    let msg := msgs.head
    let rest ← Messages.deriveTranscript stmt (acc ++ [T]) tl
      (HVector.snoc accMsgs msg) msgs.tail
    return msg ::ₕ rest
  | acc, (.V_to_P T) :: tl, accMsgs, msgs => do
    let chal : T ← liftM (query
      (spec := oSpec + fsOracleSpec StmtIn acc ((.V_to_P T) :: tl))
      (.inr (.inl (stmt, accMsgs))))
    let rest ← simulateQ (liftFSTail oSpec StmtIn acc T tl)
      (Messages.deriveTranscript stmt acc tl accMsgs msgs)
    return chal ::ₕ rest

/-! ## Non-Interactive Protocol Spec -/

/-- Trivial `OracleInterface` for the bundled message type (no meaningful queries). -/
instance Messages.trivialOracleInterface (pSpec : ProtocolSpec) :
    OracleInterface (Messages pSpec) where
  Query := PEmpty
  toOC := { spec := (PEmpty.elim ·), impl := (PEmpty.elim ·) }

/-- The FS protocol spec: a single prover-to-verifier message round. -/
def fsProtocolSpec (pSpec : ProtocolSpec) : ProtocolSpec :=
  [.P_to_V (Messages pSpec) (Messages.trivialOracleInterface pSpec)]

/-! ## Fiat-Shamir Prover -/

/-- The FS honest prover: runs the original prover with FS challenge derivation,
then packages all messages into a single non-interactive message. -/
def HonestProver.fiatShamir {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    (prover : HonestProver (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec) :
    HonestProver (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      StmtIn WitIn StmtOut WitOut (fsProtocolSpec pSpec) :=
  fun (stmt, wit) => do
    let p ← liftM (prover (stmt, wit))
    let (msgs, out) ← Prover.runFS stmt [] pSpec p (HVector.nil : HVector id [])
    return (msgs, pure out)

/-! ## Fiat-Shamir Verifier -/

/-- The FS verifier: receives all messages in one round, derives challenges from
the FS oracle to reconstruct the full transcript, then runs the original verifier. -/
def Verifier.fiatShamir {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {pSpec : ProtocolSpec}
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec) :
    Verifier (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      StmtIn StmtOut (fsProtocolSpec pSpec) :=
  fun stmt tr => OptionT.mk do
    let msgs : Messages pSpec := tr.head
    let fullTr ← Messages.deriveTranscript stmt [] pSpec (HVector.nil : HVector id []) msgs
    liftM (verifier stmt fullTr).run

/-! ## Fiat-Shamir Reduction -/

/-- The Fiat-Shamir transformation for an interactive reduction. -/
def Reduction.fiatShamir {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    (reduction : Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec) :
    Reduction (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      StmtIn WitIn StmtOut WitOut (fsProtocolSpec pSpec) where
  prover := HonestProver.fiatShamir reduction.prover
  verifier := Verifier.fiatShamir reduction.verifier

end ProtocolSpec
