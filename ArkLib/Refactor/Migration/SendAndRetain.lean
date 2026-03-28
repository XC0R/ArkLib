/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Reduction

/-!
# Send-And-Retain

Minimal migration helper for the common pattern "send one oracle-capable message and
retain it as output oracle data alongside the existing input oracle family."

This is intentionally smaller than the legacy component catalog. It is the shared
primitive behind `SendWitness`/`SendClaim`-style ports; any input-claim checking
should be modeled separately via a zero-round verifier.
-/

open OracleComp OracleSpec

namespace ProtocolSpec
namespace SendAndRetain

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn StmtOut WitIn WitOut : Type}
variable {ιₛ : Type} {OStmtIn : ιₛ → Type} [∀ i, OracleInterface (OStmtIn i)]
variable {Msg : Type} [OracleInterface Msg]

/-- Single-message protocol spec for the send-and-retain primitive. -/
@[reducible] def pSpec : ProtocolSpec := [ProtocolSpec.msg Msg]

/-- Output oracle family: keep every input oracle and append the sent message as one
new retained oracle. -/
abbrev OStmtOut : Sum ιₛ Unit → Type :=
  Sum.elim OStmtIn (fun _ => Msg)

instance : ∀ i, OracleInterface (OStmtOut (OStmtIn := OStmtIn) (Msg := Msg) i) := by
  intro i
  cases i with
  | inl j => simpa [OStmtOut] using (inferInstance : OracleInterface (OStmtIn j))
  | inr _ => simpa [OStmtOut] using (inferInstance : OracleInterface Msg)

/-- Honest prover for the send-and-retain primitive. -/
def oracleProver
    (sendMsg : ((StmtIn × (∀ i, OStmtIn i)) × WitIn) → OracleComp oSpec Msg)
    (mapStmt : StmtIn → StmtOut)
    (mapWit : ((StmtIn × (∀ i, OStmtIn i)) × WitIn) → WitOut) :
    OracleProver oSpec StmtIn OStmtIn WitIn
      StmtOut (OStmtOut (OStmtIn := OStmtIn) (Msg := Msg)) WitOut
      (pSpec (Msg := Msg)) :=
  fun ctx => do
    let msg ← sendMsg ctx
    pure
      (msg, pure
        ((mapStmt ctx.1.1, fun
          | Sum.inl i => ctx.1.2 i
          | Sum.inr _ => msg), mapWit ctx))

/-- Oracle verifier for the send-and-retain primitive.

The verifier only maps the public statement; all retained-oracle routing is derived
once here rather than reintroduced ad hoc in each port. -/
def oracleVerifier
    (mapStmt : StmtIn → StmtOut) :
    OracleVerifier oSpec StmtIn OStmtIn
      StmtOut (OStmtOut (OStmtIn := OStmtIn) (Msg := Msg))
      (pSpec (Msg := Msg)) where
  verify := fun stmt _ => pure (mapStmt stmt)
  simulate := fun
    | ⟨Sum.inl i, q⟩ =>
        by
          simpa [OStmtOut] using
            (liftM (query (spec := [OStmtIn]ₒ + oracleSpecOfMessages (pSpec (Msg := Msg)))
              (Sum.inl ⟨i, q⟩)))
    | ⟨Sum.inr u, q⟩ =>
        by
          cases u
          simpa [OStmtOut, pSpec] using
            (liftM (query (spec := [OStmtIn]ₒ + oracleSpecOfMessages (pSpec (Msg := Msg)))
              (Sum.inr (Sum.inl q))))
  reify := fun oStmtInData msgs => some (fun
    | Sum.inl i => oStmtInData i
    | Sum.inr u =>
        by
          cases u
          simpa [OStmtOut, pSpec] using HVector.head msgs)

/-- Oracle reduction pairing the generic send-and-retain prover and verifier. -/
def oracleReduction
    (sendMsg : ((StmtIn × (∀ i, OStmtIn i)) × WitIn) → OracleComp oSpec Msg)
    (mapStmt : StmtIn → StmtOut)
    (mapWit : ((StmtIn × (∀ i, OStmtIn i)) × WitIn) → WitOut) :
    OracleReduction oSpec StmtIn OStmtIn WitIn
      StmtOut (OStmtOut (OStmtIn := OStmtIn) (Msg := Msg)) WitOut
      (pSpec (Msg := Msg)) where
  prover := oracleProver (oSpec := oSpec) (OStmtIn := OStmtIn)
    (Msg := Msg) sendMsg mapStmt mapWit
  verifier := oracleVerifier (oSpec := oSpec) (OStmtIn := OStmtIn)
    (Msg := Msg) mapStmt

end SendAndRetain
end ProtocolSpec
