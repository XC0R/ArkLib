import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
import ArkLib.Data.Probability.Notation

open NNReal Finset Function ProbabilityTheory Code Affine
open scoped BigOperators LinearCode ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma pr_affSubspace_eq_pr_finset
    {A : AffineSubspace F (ι → F)} [Fintype A] [Nonempty A]
    {S : Finset (ι → F)} [Nonempty S]
    (hset : (A : Set (ι → F)) = ↑S)
    (P : (ι → F) → Prop) [DecidablePred P] :
    Pr_{let y ← $ᵖ A}[P y.1] = Pr_{let x ← $ᵖ S}[P x.val] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card (F := ↥A) (P := fun y => P y.1),
    prob_uniform_eq_card_filter_div_card (F := ↥S) (P := fun x => P x.val)]
  let e : ↥(A : Set (ι → F)) ≃ ↥(S : Set (ι → F)) := Equiv.setCongr hset
  have hcard : Fintype.card ↥A = Fintype.card ↥S :=
    Fintype.card_of_bijective e.bijective
  have hfilt : (univ.filter (fun y : ↥A => P y.1)).card =
      (univ.filter (fun x : ↥S => P x.val)).card := by
    refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ha
    · intro a₁ _ a₂ _ h; exact e.injective h
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      exact ⟨e.symm b, hb, e.apply_symm_apply b⟩
  rw [hcard, hfilt]
