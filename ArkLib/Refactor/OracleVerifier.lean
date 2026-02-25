/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Verifier

/-!
# Oracle Verifier

`OracleVerifier` is the oracle-access counterpart of `Verifier`. It receives
only the verifier challenges and queries prover messages and input oracle
statements through the `OracleComp` monad.

The prover messages' oracle spec (`oracleSpecOfMessages`) is built directly
from the `OracleInterface` bundled in each `P_to_V` round, eliminating instance
synthesis through `List.get ∘ messageTypes`.

Oracle statements use the existing VCVio `[v]ₒ` infrastructure (function-indexed
with typeclass `OracleInterface`) for compatibility with `SubSpec` and `QueryImpl`.

## Main definitions

- `MessageOracleIdx` — nested-sum index type for message oracle spec
- `oracleSpecOfMessages` — oracle spec from bundled OracleInterface
- `oracleImplOfMessages` — pure oracle implementation from message data
- `OracleVerifier` — structure with `verify`, `simulate`, `reify`
- `OracleVerifier.comp` — sequential composition of two oracle verifiers
- `OracleVerifier.compNth` — `n`-fold composition
- `OracleVerifier.toVerifier` — bridge to plain `Verifier`
-/

open OracleComp OracleSpec

namespace ProtocolSpec

/-- Index type for the oracle spec of prover messages, as a nested sum of query types.
Each `P_to_V` round contributes its bundled `OracleInterface`'s query type;
`V_to_P` rounds are skipped. -/
def MessageOracleIdx : ProtocolSpec → Type
  | [] => PEmpty
  | (.P_to_V _ oi) :: tl => oi.Query ⊕ MessageOracleIdx tl
  | (.V_to_P _) :: tl => MessageOracleIdx tl

@[simp]
theorem MessageOracleIdx_nil : MessageOracleIdx [] = PEmpty := rfl

@[simp]
theorem MessageOracleIdx_cons_P_to_V {T : Type} {oi : OracleInterface T}
    {tl : ProtocolSpec} :
    MessageOracleIdx ((.P_to_V T oi) :: tl) = (oi.Query ⊕ MessageOracleIdx tl) := rfl

@[simp]
theorem MessageOracleIdx_cons_V_to_P {T : Type} {tl : ProtocolSpec} :
    MessageOracleIdx ((.V_to_P T) :: tl) = MessageOracleIdx tl := rfl

/-- Oracle spec for prover messages, built from the bundled `OracleInterface` in each
`P_to_V` round. Produces a nested-sum oracle spec compatible with VCVio's `SubSpec`. -/
def oracleSpecOfMessages : (pSpec : ProtocolSpec) → OracleSpec (MessageOracleIdx pSpec)
  | [] => []ₒ
  | (.P_to_V _ oi) :: tl => @OracleInterface.spec _ oi + oracleSpecOfMessages tl
  | (.V_to_P _) :: tl => oracleSpecOfMessages tl

/-- Build a pure oracle implementation for message queries from actual message data.
Each `P_to_V` query is answered using `OracleInterface.answer` on the corresponding
message. -/
def oracleImplOfMessages :
    (pSpec : ProtocolSpec) → Messages pSpec → QueryImpl (oracleSpecOfMessages pSpec) Id
  | [], _ => fun q => PEmpty.elim q
  | (.P_to_V _ oi) :: tl, msgs => fun
    | .inl q => @OracleInterface.answer _ oi msgs.head q
    | .inr q => oracleImplOfMessages tl msgs.tail q
  | (.V_to_P _) :: tl, msgs => oracleImplOfMessages tl msgs

/-- Oracle verifier with oracle access to input statements and prover messages.

Oracle statements use function-indexed types (`OStmtIn : ιₛᵢ → Type`) for
compatibility with VCVio's `[v]ₒ` notation and existing `SubSpec` / `QueryImpl`
infrastructure. Message oracles use the new list-based `oracleSpecOfMessages`. -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    (pSpec : ProtocolSpec)
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)] where
  /-- Verify: given input statement and challenges, decide to accept/reject
  with oracle access to input statements and messages. -/
  verify : StmtIn → Challenges pSpec →
    OptionT (OracleComp (oSpec + [OStmtIn]ₒ + oracleSpecOfMessages pSpec)) StmtOut
  /-- Simulate output oracle queries using input oracles and message oracles.
  Used in query-level security proofs. -/
  simulate : QueryImpl [OStmtOut]ₒ
    (OracleComp ([OStmtIn]ₒ + oracleSpecOfMessages pSpec))
  /-- Compute output oracle data deterministically from input oracle data and messages.
  Used in completeness proofs and execution. -/
  reify : (∀ i, OStmtIn i) → Messages pSpec → Option (∀ i, OStmtOut i)

namespace OracleVerifier

/-- Compose two oracle verifiers sequentially.
The `verify` and `simulate` fields require oracle routing between the composed
message specs; these use `sorry` pending VCVio SubSpec infrastructure.
The `reify` field is fully implemented. -/
def comp
    {ι : Type} {oSpec : OracleSpec ι}
    {S₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    {S₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    {S₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [∀ i, OracleInterface (OStmt₁ i)]
    [∀ i, OracleInterface (OStmt₂ i)]
    [∀ i, OracleInterface (OStmt₃ i)]
    (ov₁ : OracleVerifier oSpec S₁ OStmt₁ S₂ OStmt₂ pSpec₁)
    (ov₂ : OracleVerifier oSpec S₂ OStmt₂ S₃ OStmt₃ pSpec₂)
    : OracleVerifier oSpec S₁ OStmt₁ S₃ OStmt₃ (pSpec₁ ++ pSpec₂) where
  verify := sorry
  simulate := sorry
  reify := fun oStmtInData msgs => do
    let (msgs₁, msgs₂) := Messages.split msgs
    let oStmtMidData ← ov₁.reify oStmtInData msgs₁
    ov₂.reify oStmtMidData msgs₂

/-- Compose an oracle verifier with itself `n` times over the replicated protocol spec. -/
def compNth
    {ι : Type} {oSpec : OracleSpec ι}
    {S : Type} {ιₛ : Type} {OStmt : ιₛ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmt i)] : (n : Nat) →
    OracleVerifier oSpec S OStmt S OStmt pSpec →
    OracleVerifier oSpec S OStmt S OStmt (pSpec.replicate n)
  | 0, _ => { verify := fun stmt _ => pure stmt,
              simulate := sorry,
              reify := fun oStmtData _ => some oStmtData }
  | n + 1, ov => comp ov (compNth n ov)

/-- Convert an oracle verifier to a plain verifier by simulating all oracle queries
with actual data. Takes explicit oracle statement data as input.

The implementation extracts challenges and messages from the transcript, builds
oracle implementations from the data, and runs the oracle verifier in a
simulated context. -/
def toVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)]
    (ov : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (oStmtData : ∀ i, OStmtIn i) :
    Verifier (OracleComp oSpec) StmtIn StmtOut pSpec :=
  fun stmt tr => sorry

end OracleVerifier

end ProtocolSpec
