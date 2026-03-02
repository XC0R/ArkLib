/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

open NNReal ProximityGap

/-!
  # Definitions and Theorems about Divergence of Sets

  ## Main Definitions and Statements

  - divergence of sets
  - statement of Corollary 1.3 (Concentration bounds) from [BCIKS20].
-/

namespace DivergenceOfSets

open Code ReedSolomon ProbabilityTheory

section Defs

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [DecidableEq F]
         {U V : Set (ι → F)} [Nonempty V] [Fintype V]

/-- The set of possible relative Hamming distances between two sets. -/
def possibleDeltas (U V : Set (ι → F)) [Nonempty V] [Fintype V] : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ u ∈ U, δᵣ'(u,V) = d}

/-- The set of possible relative Hamming distances between two sets is well-defined. -/
@[simp]
lemma possibleDeltas_subset_relHammingDistRange :
  possibleDeltas U V ⊆ relHammingDistRange ι :=
  fun x hx_mem_deltas ↦ by
    simp only [possibleDeltas, Set.mem_setOf_eq] at hx_mem_deltas
    rcases hx_mem_deltas with ⟨u, hu_mem, h_dist_eq⟩
    rw [←h_dist_eq]
    unfold relDistFromCode'
    have h_mem : (Finset.univ.image (fun (c : V) => relHammingDist u c)).min'
      (Finset.univ_nonempty.image _) ∈ Finset.univ.image (fun (c : V) => relHammingDist u c) :=
      Finset.min'_mem _ (Finset.univ_nonempty.image _)
    obtain ⟨c, _, h_eq⟩ := Finset.mem_image.mp h_mem
    rw [←h_eq]
    exact relHammingDist_mem_relHammingDistRange

/-- The set of possible relative Hamming distances between two sets is finite. -/
@[simp]
lemma finite_possibleDeltas : (possibleDeltas U V).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDeltas_subset_relHammingDistRange

open Classical in
/-- Definition of divergence of two sets from Section 1.2 in [BCIKS20].

For two sets `U` and `V`, the divergence of `U` from `V` is the maximum of the possible
relative Hamming distances between elements of `U` and the set `V`. -/
noncomputable def divergence (U V : Set (ι → F)) [Nonempty V] [Fintype V] : ℚ≥0 :=
  haveI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
  if h : (possibleDeltas U V).Nonempty
  then (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

end Defs

section Theorems

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Fintype F] [Field F]
         {U V : Set (ι → F)}

open Classical in
/-- Corollary 1.3 (Concentration bounds) from [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space `U` inside `F^ι`. Let `δ'` denote the divergence of `U` from the
Reed-Solomon code (`δ^*` in [BCIKS20]). If `δ' ∈ (0, 1 − √ρ)`, then nearly all elements of `U` are
at distance exactly `δ'` from the Reed-Solomon code. -/
lemma concentration_bounds {deg : ℕ} {domain : ι ↪ F}
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  (hdiv_pos : 0 < (divergence U (RScodeSet domain deg) : ℝ≥0))
  (hdiv_lt : (divergence U (RScodeSet domain deg) : ℝ≥0) < 1 - ReedSolomon.sqrtRate deg domain)
  : let δ' := divergence U (RScodeSet domain deg)
    Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (RScodeSet domain deg) ≠ δ']
    ≤ errorBound δ' deg domain := by sorry

end Theorems

end DivergenceOfSets
