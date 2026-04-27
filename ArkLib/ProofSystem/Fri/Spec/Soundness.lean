/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ReedSolomonGap
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.OracleReduction.Security.Basic

/-!
# FRI single-round soundness

The single-round soundness theorem for the FRI protocol: if the initial oracle
is NOT δ-close to the Reed-Solomon code, then the FRI verifier accepts with
probability at most `totalError δ` (sum of per-round proximity gap error bounds).

## Main results

* `Fri.Spec.fri_soundness` — soundness of the full FRI reduction.

## References

* [Ben-Sasson, I., Chiesa, A., Goldberg, L., Gur, T., Riabzev, M., Spooner, N.,
  *Proximity Gaps for Reed-Solomon Codes*, FOCS 2020][BCIKS20]
-/

namespace Fri

open Polynomial OracleSpec OracleComp ProtocolSpec Finset NNReal ProximityGap

namespace Spec

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ) [NeZero l]
variable {ω : ReedSolomon.SmoothCosetFftDomain n F}

/-- The per-round error bound for the `i`-th FRI folding round, derived from the
    BCIKS20 proximity gap error bound for the round-`i` Reed-Solomon code. -/
noncomputable def roundError (δ : ℝ≥0) (i : Fin k) : ℝ≥0 :=
  let N := ∑ j' ∈ finRangeTo (k + 1) (Fin.last i.castSucc.val).val, (s j').1
  let dom : ReedSolomon.SmoothCosetFftDomain (n - N) F := ω.subdomainNatReversed N
  let degBound := 2 ^ ((∑ j', (s j').1) - N) * d.1
  errorBound δ degBound (↑dom : Fin (2 ^ (n - N)) ↪ F)

/-- The total soundness error for the FRI protocol, summing per-round proximity
    gap error bounds over all `k` non-final folding rounds. -/
noncomputable def totalError (δ : ℝ≥0) : ℝ≥0 :=
  ∑ i : Fin k, roundError k s d (ω := ω) δ i

section Soundness

variable [∀ i, SampleableType
  ((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F
    ++ₚ QueryRound.pSpec (ω := ω) l).Challenge i)]

/-- **FRI soundness.** If the initial oracle is not δ-close to the Reed-Solomon
    code (i.e., the input statement is not in the input language), then the
    probability that the FRI verifier outputs a statement in the output language
    is at most `totalError δ`.

    The proof composes:
    - `FoldPhase.inputRelation` / `outputRelation` (δ-proximity to RS code)
    - `proximity_gap_RSCodes` (BCIKS20 Thm 1.2, Xor' dichotomy)
    - `correlatedAgreement_affine_spaces` (BCIKS20 Thm 1.6, used transitively)

    Each folding round contributes at most `roundError δ i` via the proximity
    gap: the Xor' dichotomy forces either Pr[δ-close] = 1 (oracle is close)
    or Pr[δ-close] ≤ ε (oracle is far). A union bound over rounds gives the
    total error. -/
theorem fri_soundness (δ : ℝ≥0)
    (hδ : ∀ i : Fin k,
      let N := ∑ j' ∈ finRangeTo (k + 1) (Fin.last i.castSucc.val).val, (s j').1
      δ ≤ 1 - ReedSolomon.sqrtRate
        (2 ^ ((∑ j', (s j').1) - N) * d.1)
        (↑(ω.subdomainNatReversed N) : Fin (2 ^ (n - N)) ↪ F))
    (hε : ∀ i : Fin k, roundError k s d (ω := ω) δ i < 1) :
    Verifier.soundness (σ := Unit) (pure ()) isEmptyElim
      (inputRelation k s d dom_size_cond (ω := ω) δ).language
      (outputRelation k s d dom_size_cond (ω := ω) δ).language
      (reduction k s d dom_size_cond l (ω := ω)).toReduction.verifier
      (totalError k s d (ω := ω) δ) := by
  sorry

end Soundness

end Spec

end Fri
