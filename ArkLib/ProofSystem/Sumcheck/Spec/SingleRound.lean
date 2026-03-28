/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Refactor.Sumcheck.PartialEval

/-!
# Legacy Sumcheck Single-Round Compatibility Surface

The supported sumcheck substrate now lives under `ArkLib.Refactor.Sumcheck.*`.
This legacy module is kept only for the degree lemma still consumed by Binius
during the cutover.
-/

namespace Sumcheck

open CompPoly Polynomial MvPolynomial Finset

noncomputable section

namespace Spec
namespace SingleRound

variable (R : Type) [CommSemiring R] (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- The round polynomial obtained by fixing prior challenges, leaving the current
variable free, and summing over the remaining domain points still has degree at
most `deg` when the original multivariate polynomial has individual degree at
most `deg`. Kept at the legacy path while downstream callers are migrated. -/
theorem sumcheck_roundPoly_degreeLE (i : Fin (n + 1)) {challenges : Fin i.castSucc → R}
    {poly : R[X Fin (n + 1)]} (hp : poly ∈ R⦃≤ deg⦄[X Fin (n + 1)]) :
    ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩'
      (by simp; omega) ∈ R⦃≤ deg⦄[X] := by
  refine mem_degreeLE.mpr (le_trans (degree_sum_le ((univ.map D) ^ᶠ (n - i)) _) ?_)
  simp only [Finset.sup_le_iff, Fintype.mem_piFinset, mem_map, mem_univ, true_and]
  intro x hx
  refine le_trans (degree_map_le) (natDegree_le_iff_degree_le.mp ?_)
  rw [natDegree_finSuccEquivNth]
  exact degreeOf_le_iff.mpr fun m a => hp a i

end SingleRound
end Spec

end

end Sumcheck
