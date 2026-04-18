import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
import ArkLib.Data.Probability.Notation

open NNReal Finset Function ProbabilityTheory Code Affine
open scoped BigOperators LinearCode ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {m : ℕ} {C : Fin (m + 2) → ι → F}

noncomputable def u' (C : Fin (m + 2) → ι → F) : Fin (m + 2) → ι → F :=
  fun j => if j = 0 then C 0 else C j - C 0

example : (affineSubspaceAtOrigin (F := F) (u' C 0) (Fin.tail (u' C)) :
    AffineSubspace F (ι → F)) =
    affineSpan F (↑(univ.image C) : Set (ι → F)) := by
  unfold u' affineSubspaceAtOrigin
  simp only [ite_true]
  have hp0 : C 0 ∈ affineSpan F (↑(univ.image C) : Set (ι → F)) := by
    apply subset_affineSpan; simp
  rw [← AffineSubspace.mk'_eq hp0, direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right (k := F) (by simp : C 0 ∈ ↑(univ.image C))]
  congr 1
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hvsub : (· -ᵥ C 0) '' Set.range C =
      Set.range (fun j : Fin (m + 2) => C j - C 0) := by
    ext v; simp [vsub_eq_sub]
  rw [hvsub]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv; obtain ⟨j, rfl⟩ := hv
    exact Submodule.subset_span ⟨j.succ,
      by simp [Fin.tail, if_neg (Fin.succ_ne_zero _)]⟩
  · apply Submodule.span_le.mpr
    intro v hv; obtain ⟨j, rfl⟩ := hv
    by_cases hj0 : j = 0
    · simp only [hj0, sub_self]; exact Submodule.zero_mem _
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
      apply Submodule.subset_span
      exact ⟨j', by simp [Fin.tail, if_neg (Fin.succ_ne_zero _)]⟩

-- Now: use the AffineSubspace equality to transfer probability.
-- If two AffineSubspaces are equal, their subtypes are equiv, so uniform probs are equal.
example (A B : AffineSubspace F (ι → F)) (h : A = B) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (P : (ι → F) → Prop) [DecidablePred P] :
    Pr_{let y ← $ᵖ A}[P y.1] = Pr_{let y ← $ᵖ B}[P y.1] := by
  subst h; rfl
