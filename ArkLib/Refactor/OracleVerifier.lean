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
    {pSpec : ProtocolSpec} → Messages pSpec → QueryImpl (oracleSpecOfMessages pSpec) Id
  | [], .nil => fun q => PEmpty.elim q
  | (.P_to_V _ oi) :: _, .cons msg msgs => fun
    | .inl q => @OracleInterface.answer _ oi msg q
    | .inr q => oracleImplOfMessages msgs q
  | (.V_to_P _) :: _, msgs => oracleImplOfMessages msgs

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
