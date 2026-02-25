/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Prover
import ArkLib.Refactor.OracleVerifier

/-!
# Reductions

`Reduction` and `OracleReduction` pair a prover with a verifier, forming the
basic unit of interactive proof composition.

- `Reduction` — plain prover + plain verifier (for Fiat-Shamir, BCS output)
- `OracleReduction` — oracle prover + oracle verifier (for IOPs)

## Main definitions

- `Reduction` — plain reduction structure
- `OracleProver` — honest prover with oracle statement data
- `OracleReduction` — oracle reduction structure
- `Proof` / `OracleProof` — specializations with `Bool` output
- `Reduction.run` — execute a reduction with pre-sampled challenges
- `OracleReduction.toReduction` — bridge via `OracleVerifier.toVerifier`
-/

open OracleComp OracleSpec

namespace ProtocolSpec

/-- A plain reduction: pairs an honest prover with a plain verifier. -/
structure Reduction (m : Type → Type)
    (StmtIn WitIn StmtOut WitOut : Type)
    (pSpec : ProtocolSpec) where
  prover : HonestProver m StmtIn WitIn StmtOut WitOut pSpec
  verifier : Verifier m StmtIn StmtOut pSpec

/-- An oracle prover: an honest prover whose input/output statement includes oracle data.
The prover receives `(StmtIn × (∀ i, OStmtIn i), WitIn)` and produces
`(StmtOut × (∀ i, OStmtOut i), WitOut)`. -/
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    (pSpec : ProtocolSpec) :=
  HonestProver (OracleComp oSpec)
    (StmtIn × (∀ i, OStmtIn i)) WitIn
    (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

/-- An oracle reduction: pairs an oracle prover with an oracle verifier. -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    (pSpec : ProtocolSpec)
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)] where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec

/-- An interactive proof: a reduction with `Bool` output and trivial witness output. -/
abbrev Proof (m : Type → Type) (StmtIn WitIn : Type) (pSpec : ProtocolSpec) :=
  Reduction m StmtIn WitIn Bool Unit pSpec

namespace Reduction

/-- Run a reduction: execute the prover with pre-sampled challenges, then run the
verifier on the resulting transcript. Returns the verifier's decision (as `Option`)
and the prover's output statement/witness. -/
def run [Monad m]
    (red : Reduction m StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (challenges : Challenges pSpec)
    : m (Option StmtOut × (StmtOut × WitOut)) := do
  let prover ← red.prover (stmt, wit)
  let (tr, proverOut) ← prover.run challenges
  let verResult ← red.verifier stmt tr
  return (verResult, proverOut)

end Reduction

namespace OracleReduction

/-- Convert an oracle reduction to a plain reduction by providing oracle statement
data and simulating oracle access via `OracleVerifier.toVerifier`. -/
def toReduction
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)]
    (red : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (oStmtData : ∀ i, OStmtIn i) :
    Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec :=
  sorry

end OracleReduction

end ProtocolSpec
