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
- `Reduction.comp` — sequential composition of two reductions
- `Reduction.compNth` — `n`-fold composition
- `OracleProver` — honest prover with oracle statement data
- `OracleReduction` — oracle reduction structure
- `OracleReduction.comp` — sequential composition of two oracle reductions
- `OracleReduction.compNth` — `n`-fold composition
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
def run {m : Type → Type} [Monad m]
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    (red : Reduction m StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (challenges : Challenges pSpec)
    : m (Option StmtOut × (StmtOut × WitOut)) := do
  let prover ← red.prover (stmt, wit)
  let (tr, proverOut) ← Prover.run pSpec prover challenges
  let verResult ← red.verifier stmt tr
  return (verResult, proverOut)

/-- The identity reduction for the empty protocol: prover passes through, verifier accepts. -/
def id {m : Type → Type} [Monad m] {S W : Type} :
    Reduction m S W S W [] where
  prover := fun sw => pure sw
  verifier := fun stmt _ => pure stmt

/-- Compose two reductions sequentially. -/
def comp {m : Type → Type} [Monad m]
    {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (r₁ : Reduction m S₁ W₁ S₂ W₂ pSpec₁)
    (r₂ : Reduction m S₂ W₂ S₃ W₃ pSpec₂)
    : Reduction m S₁ W₁ S₃ W₃ (pSpec₁ ++ pSpec₂) where
  prover := HonestProver.comp r₁.prover r₂.prover
  verifier := Verifier.comp r₁.verifier r₂.verifier

/-- Compose a reduction with itself `n` times over the replicated protocol spec. -/
def compNth {m : Type → Type} [Monad m]
    {S W : Type} {pSpec : ProtocolSpec} : (n : Nat) →
    Reduction m S W S W pSpec →
    Reduction m S W S W (pSpec.replicate n)
  | 0, _ => Reduction.id
  | n + 1, r => comp r (compNth n r)

end Reduction

namespace OracleReduction

/-- Compose two oracle reductions sequentially. -/
def comp
    {ι : Type} {oSpec : OracleSpec ι}
    {S₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} {W₁ : Type}
    {S₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} {W₂ : Type}
    {S₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} {W₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [∀ i, OracleInterface (OStmt₁ i)]
    [∀ i, OracleInterface (OStmt₂ i)]
    [∀ i, OracleInterface (OStmt₃ i)]
    (r₁ : OracleReduction oSpec S₁ OStmt₁ W₁ S₂ OStmt₂ W₂ pSpec₁)
    (r₂ : OracleReduction oSpec S₂ OStmt₂ W₂ S₃ OStmt₃ W₃ pSpec₂)
    : OracleReduction oSpec S₁ OStmt₁ W₁ S₃ OStmt₃ W₃ (pSpec₁ ++ pSpec₂) where
  prover := HonestProver.comp r₁.prover r₂.prover
  verifier := OracleVerifier.comp r₁.verifier r₂.verifier

/-- Compose an oracle reduction with itself `n` times over the replicated protocol spec. -/
def compNth
    {ι : Type} {oSpec : OracleSpec ι}
    {S : Type} {ιₛ : Type} {OStmt : ιₛ → Type} {W : Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmt i)] : (n : Nat) →
    OracleReduction oSpec S OStmt W S OStmt W pSpec →
    OracleReduction oSpec S OStmt W S OStmt W (pSpec.replicate n)
  | 0, _ => { prover := fun sw => pure sw,
              verifier := { verify := fun stmt _ => pure stmt,
                            simulate := sorry,
                            reify := fun oStmtData _ => some oStmtData } }
  | n + 1, r => comp r (compNth n r)

/-- Convert an oracle reduction to a plain reduction by providing oracle statement
data and simulating oracle access via `OracleVerifier.toVerifier`. -/
def toReduction
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)]
    (red : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (oStmtData : ∀ i, OStmtIn i) :
    Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec :=
  sorry

end OracleReduction

end ProtocolSpec
