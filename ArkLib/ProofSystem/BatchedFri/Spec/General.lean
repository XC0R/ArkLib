/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Spec.General


namespace BatchedFri

namespace Spec

open OracleSpec OracleComp ProtocolSpec NNReal BatchingRound

/- Batched FRI parameters:
   - `F` a non-binary finite field.
   - `ω` the smooth coset FFT domain encoding the evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `l`, the number of round consistency checks to be run by the query round.
  - `m`, number of batched polynomials.
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ} {ω : ReedSolomon.SmoothCosetFftDomain n F}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l m : ℕ)

-- /- Input/Output relations for the Batched FRI protocol. -/
def inputRelation (δ : ℝ≥0) :
    Set
      (
        Unit × (∀ j, OracleStatement (ω := ω) m j) × (Witness F s d m)
      ) := sorry


/- Lifting FRI to include using `liftingLens`:
    - RLC in statement
    - Simulate batched polynomial oracle using oracles of
      batched polynomials
-/
def liftingLens :
  OracleContext.Lens
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
    (Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
    (OracleStatement (ω := ω) m) (Fri.Spec.FinalOracleStatement s ω)
    (Fri.Spec.OracleStatement s ω 0) (Fri.Spec.FinalOracleStatement s ω)
    (Fri.Spec.Witness F s d 0) (Fri.Spec.Witness F s d (Fin.last (k + 1)))
    (Fri.Spec.Witness F s d 0) (Fri.Spec.Witness F s d (Fin.last (k + 1))) := sorry

noncomputable def liftedFRI :
  OracleReduction []ₒ
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
      (OracleStatement (ω := ω) m) (Fri.Spec.Witness F s d 0)
    (Fri.Spec.FinalStatement F k)
      (Fri.Spec.FinalOracleStatement s ω) (Fri.Spec.Witness F s d (Fin.last (k + 1)))
    (
      Fri.Spec.pSpecFold (ω := ω) k s ++ₚ
      Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
      Fri.Spec.QueryRound.pSpec (ω := ω) l
    ) :=
    OracleReduction.liftContext
      (liftingLens k s d m)
      (Fri.Spec.reduction (ω := ω) k s d dom_size_cond l)

instance instBatchFRIreductionMessageOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold (ω := ω) k s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Message j) := fun j ↦ by
      apply instOracleInterfaceMessageAppend

instance instBatchFRIreductionChallengeOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold (ω := ω) k s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Challenge j) :=
  ProtocolSpec.challengeOracleInterface


/- Oracle reduction of the batched FRI protocol. -/
@[reducible]
noncomputable def batchedFRIreduction
 :=
  OracleReduction.append
    (BatchingRound.batchOracleReduction (ω := ω) s d m)
    (liftedFRI (ω := ω) k s d dom_size_cond l m)

end Spec

end BatchedFri
