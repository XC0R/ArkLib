/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.Probability.Notation
/-! # BCIKS20 Reed-Solomon Proximity Gaps

## Main results

* `proximity_gap_RSCodes` — Theorem 1.2 from [BCIKS20]: Reed-Solomon codes display a
  `(δ, ε)`-proximity gap for affine-space collections.
-/


namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

private lemma pr_uniform_surj_const_fiber {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [DecidableEq β]
    (f : α → β) (hf : Function.Surjective f)
    {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hfib : ∀ b ∈ Finset.univ.image f,
      (Finset.univ.filter (f · = b)).card = k₀)
    (P : β → Prop) :
    Pr_{let a ← $ᵖ α}[P (f a)] = Pr_{let b ← $ᵖ β}[P b] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card]
  have himg : Finset.univ.image f = Finset.univ := by
    ext b; simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact hf b
  have htotal : Fintype.card α = k₀ * Fintype.card β := by
    have := Finset.card_eq_sum_card_image f (Finset.univ : Finset α)
    rw [Finset.sum_const_nat (fun b hb => hfib b hb), himg,
      show (Finset.univ : Finset β).card = Fintype.card β from rfl] at this
    rw [show (Finset.univ : Finset α).card = Fintype.card α from rfl] at this
    linarith [mul_comm k₀ (Fintype.card β)]
  have hfilter : (Finset.univ.filter (fun a => P (f a))).card =
      k₀ * (Finset.univ.filter P).card := by
    have h1 := Finset.card_eq_sum_card_image f (Finset.univ.filter (fun a => P (f a)))
    have h2 : ∀ b ∈ (Finset.univ.filter (fun a => P (f a))).image f,
        ((Finset.univ.filter (fun a => P (f a))).filter (f · = b)).card = k₀ := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hPfa : P (f a) := (Finset.mem_filter.mp ha).2
      have : (Finset.univ.filter (fun a => P (f a))).filter (f · = f a) =
          Finset.univ.filter (f · = f a) := by
        ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ hPfa, h⟩⟩
      rw [this]; exact hfib (f a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    rw [Finset.sum_const_nat h2] at h1
    have h3 : (Finset.univ.filter (fun a => P (f a))).image f = Finset.univ.filter P := by
      ext b; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨a, hPfa, hab⟩ => hab ▸ hPfa,
        fun hPb => ⟨(hf b).choose, (hf b).choose_spec.symm ▸ hPb, (hf b).choose_spec⟩⟩
    rw [h3] at h1; linarith
  rw [hfilter, htotal]
  push_cast
  exact ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hk₀.ne' : (k₀ : ENNReal) ≠ 0)
    (ENNReal.natCast_ne_top k₀)

/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].

The `hε` hypothesis is required for `Xor'` exclusivity: without `ε < 1`, both branches
could hold simultaneously.

Depends on `correlatedAgreement_affine_spaces` (Theorem 1.6, currently `sorry`'d). -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
    (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C)
      δ
      (errorBound δ deg domain) := by
  classical
  intro S hS _inst
  obtain ⟨i, rfl⟩ := hS
  set S : Finset (ι → F) := Affine.AffSpanFinset (C i) with hS_def
  by_cases hcase :
      Pr_{let x ← $ᵖ S}[δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ] ≤
        (errorBound δ deg domain : ℝ≥0)
  · -- Right Xor' branch: Pr ≤ ε
    refine Or.inr ⟨hcase, ?_⟩
    intro hPeq1
    rw [hPeq1] at hcase
    exact (not_lt_of_ge hcase) (by exact_mod_cast hε)
  · -- Left Xor' branch: Pr = 1
    push Not at hcase
    refine Or.inl ⟨?_, not_le.mpr hcase⟩
    suffices h_all : ∀ x : ↥S,
        δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ by
      rw [prob_uniform_eq_card_filter_div_card (F := ↥S)
            (P := fun x => δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ)]
      have hfilter :
          Finset.filter (fun x : ↥S =>
              δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ) Finset.univ =
            (Finset.univ : Finset ↥S) := by
        ext x; simpa using h_all x
      rw [hfilter, Finset.card_univ]
      exact_mod_cast div_self (show (Fintype.card ↥S : ℝ≥0) ≠ 0 from by
        exact_mod_cast Fintype.card_ne_zero)
    intro xS
    have hx_mem_aff : xS.val ∈ Affine.AffSpanSet (C i) :=
      (Affine.AffSpanSet.instFinite (u := C i)).mem_toFinset.mp xS.property
    suffices hja :
        jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F)))
          (δ := δ) (W := C i) by
      have hx_in_span : xS.val ∈ (Submodule.span F (Set.range (C i)) : Set (ι → F)) := by
        have : (Finset.univ.image (C i) : Set (ι → F)) = Set.range (C i) := by
          simp [Set.range, Finset.coe_image, Finset.coe_univ]
        rw [← this]
        exact affineSpan_subset_span hx_mem_aff
      convert jointAgreement_implies_linSpan_proximity
        (C := ReedSolomon.code domain deg) hja xS.val hx_in_span using 2
      simp [ReedSolomon.toFinset]
    -- Obtain jointAgreement via Thm 1.6.
    by_cases hk1 : k = 1
    · -- k = 1: singleton case
      subst hk1
      have himg : (Finset.univ : Finset (Fin 1)).image (C i) = {C i 0} := by
        ext y; simp [Fin.eq_zero]
      have hmem_eq : ∀ x ∈ Affine.AffSpanSet (C i), x = C i 0 := by
        intro x hx
        simp only [Affine.AffSpanSet] at hx
        have hmem : x ∈ (affineSpan F (↑(Finset.univ.image (C i)) : Set (ι → F))) := hx
        rw [himg, Finset.coe_singleton] at hmem
        rwa [AffineSubspace.mem_affineSpan_singleton] at hmem
      have hCi0_close :
          δᵣ(C i 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
        by_contra hnotclose
        push Not at hnotclose
        have hPr_eq :
            Pr_{let x ← $ᵖ S}[δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ] = 0 := by
          rw [prob_uniform_eq_card_filter_div_card (F := ↥S)
            (P := fun x => δᵣ(x.val, (ReedSolomon.toFinset domain deg : Set _)) ≤ δ)]
          have : (Finset.univ : Finset ↥S).filter
              (fun x : ↥S => δᵣ(x.val,
                (ReedSolomon.toFinset domain deg : Set _)) ≤ δ) = ∅ := by
            apply Finset.filter_false_of_mem
            intro ⟨x, hx⟩ _
            have hx_eq := hmem_eq x
              ((Affine.AffSpanSet.instFinite (u := C i)).mem_toFinset.mp hx)
            subst hx_eq
            intro hclose
            exact absurd (by convert hclose using 2; simp [ReedSolomon.toFinset])
              (not_le.mpr hnotclose)
          rw [this, Finset.card_empty, Nat.cast_zero]; simp
        rw [hPr_eq] at hcase
        exact absurd hcase (not_lt.mpr (zero_le _))
      obtain ⟨v₀, hv₀_mem, hv₀_dist⟩ :=
        (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (C i 0) δ).mp hCi0_close
      obtain ⟨S', hS'_card, hS'_agree⟩ :=
        (Code.relCloseToWord_iff_exists_agreementCols (C i 0) v₀ δ).mp hv₀_dist
      exact ⟨S',
        (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S'.card δ).mp hS'_card,
        fun _ => v₀, fun j => ⟨hv₀_mem, fun col hcol =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [show j = 0 from Fin.eq_zero j]
            exact ((hS'_agree col).1 hcol).symm⟩⟩⟩
    · -- k ≥ 2: Apply Thm 1.6 via reindexing + sampling bridge.
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by have := NeZero.pos k; omega⟩
      let u' : Fin (m + 2) → ι → F := fun j =>
        if j = 0 then C i 0 else C i j - C i 0
      -- Need: Pr over coefficient space > errorBound.
      -- hcase gives Pr over AffSpanFinset S > errorBound.
      -- The map r ↦ u' 0 + ∑ r i • u' i.succ bijects (Fin (m+1) → F) ↔ S.
      -- Bridge: show affineSubspaceAtOrigin u' = affineSpan of C i image.
      have haff_eq : Affine.affineSubspaceAtOrigin (F := F) (u' 0) (Fin.tail u') =
          affineSpan F (↑(Finset.univ.image (C i)) : Set (ι → F)) := by
        unfold Affine.affineSubspaceAtOrigin u'
        simp only [ite_true]
        have hp0 : C i 0 ∈ affineSpan F
            (↑(Finset.univ.image (C i)) : Set (ι → F)) := by
          apply subset_affineSpan; simp
        rw [← AffineSubspace.mk'_eq hp0, direction_affineSpan,
          vectorSpan_eq_span_vsub_set_right (k := F)
            (by simp : C i 0 ∈ ↑(Finset.univ.image (C i)))]
        congr 1
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
          Finset.coe_image, Finset.coe_univ, Set.image_univ]
        have hvsub : (· -ᵥ C i 0) '' Set.range (C i) =
            Set.range (fun j : Fin (m + 2) => C i j - C i 0) := by
          ext v; simp [vsub_eq_sub]
        rw [hvsub]
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro v hv; obtain ⟨j, rfl⟩ := hv
          exact Submodule.subset_span ⟨j.succ, by simp [Fin.tail]⟩
        · apply Submodule.span_le.mpr
          intro v hv; obtain ⟨j, rfl⟩ := hv
          by_cases hj0 : j = 0
          · simp only [hj0, sub_self]; exact Submodule.zero_mem _
          · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
            exact Submodule.subset_span ⟨j', by simp [Fin.tail]⟩
      -- Carrier equality: affineSubspaceAtOrigin = ↑S as sets.
      have hcarrier_eq : (Affine.affineSubspaceAtOrigin (F := F)
          (u' 0) (Fin.tail u') : Set (ι → F)) = ↑S := by
        rw [haff_eq, hS_def]; unfold Affine.AffSpanFinset
        exact (Affine.AffSpanSet.instFinite (u := C i)).coe_toFinset.symm
      -- Transfer hcase to the affine subspace type.
      have hPr_aff :
          Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F)
            (u' 0) (Fin.tail u'))}[
            δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] >
          (errorBound δ deg domain : ℝ≥0) := by
        have hcase_code : (errorBound δ deg domain : ℝ≥0) <
            Pr_{let x ← $ᵖ S}[δᵣ(x.val,
              (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] := by
          convert hcase using 3; simp [ReedSolomon.toFinset]
        rw [prob_uniform_eq_card_filter_div_card] at hcase_code
        rw [prob_uniform_eq_card_filter_div_card
          (F := ↥(Affine.affineSubspaceAtOrigin (F := F) (u' 0) (Fin.tail u')))]
        let e := Equiv.setCongr hcarrier_eq
        have hcard : Fintype.card ↥(Affine.affineSubspaceAtOrigin (F := F)
            (u' 0) (Fin.tail u')) = Fintype.card ↥S :=
          Fintype.card_of_bijective e.bijective
        have hfilt : (Finset.univ.filter (fun (y : ↥(Affine.affineSubspaceAtOrigin
            (F := F) (u' 0) (Fin.tail u'))) =>
            δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ)).card =
          (Finset.univ.filter (fun (x : ↥S) =>
            δᵣ(x.val, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ)).card :=
          Finset.card_bij (fun a _ => e a)
            (fun a ha => by simpa using ha)
            (fun a₁ _ a₂ _ h => e.injective h)
            (fun b hb => ⟨e.symm b, by simpa using hb, e.apply_symm_apply b⟩)
        rw [hcard, hfilt]; exact hcase_code
      -- Convert Pr over affineSubspaceAtOrigin to Pr over coefficient space.
      -- φ(r) = u' 0 + ∑ r i • (Fin.tail u') i parametrizes the affine subspace.
      -- Both Pr are card(filter)/card ratios; φ has constant fibers so ratios match.
      let φ : (Fin (m + 1) → F) → (ι → F) := fun r =>
        u' 0 + ∑ i : Fin (m + 1), r i • Fin.tail u' i
      have hPr_coeff :
          Pr_{let r ← $ᵖ (Fin (m + 1) → F)}[
            δᵣ(u' 0 + ∑ i : Fin (m + 1), r i • u' i.succ,
              (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] >
          (errorBound δ deg domain : ℝ≥0) := by
        -- The predicate on coefficients equals the predicate on the affine subspace.
        -- φ(r) is in the affine subspace for all r, and every affine subspace element
        -- has a preimage. Fibers are cosets of ker(linear part), hence constant size.
        -- We show the two Pr are equal, then apply hPr_aff.
        -- φ maps into the affine subspace.
        have hφ_mem : ∀ r : Fin (m + 1) → F,
            φ r ∈ Affine.affineSubspaceAtOrigin (F := F) (u' 0) (Fin.tail u') := by
          intro r
          rw [Affine.mem_affineSubspaceFrom_iff]
          exact ⟨r, rfl⟩
        -- Lift φ to the affine subspace subtype.
        let φ' : (Fin (m + 1) → F) → ↥(Affine.affineSubspaceAtOrigin (F := F)
            (u' 0) (Fin.tail u')) := fun r => ⟨φ r, hφ_mem r⟩
        -- φ' is surjective.
        have hφ'_surj : Function.Surjective φ' := by
          intro ⟨x, hx⟩
          rw [Affine.mem_affineSubspaceFrom_iff] at hx
          obtain ⟨β, rfl⟩ := hx
          exact ⟨β, rfl⟩
        -- Use pr_uniform_surj_const_fiber with f = φ' to equate the two Pr.
        -- Need: constant fiber size for φ'.
        set k₀ := (Finset.univ.filter (fun r : Fin (m + 1) → F =>
          φ' r = φ' 0)).card
        have hk₀_pos : 0 < k₀ := Finset.card_pos.mpr
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        have hfib_const : ∀ b ∈ Finset.univ.image φ',
            (Finset.univ.filter (φ' · = b)).card = k₀ := by
          intro b hb
          obtain ⟨r₁, _, rfl⟩ := Finset.mem_image.mp hb
          apply Finset.card_bij (fun r _ => r - r₁)
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            have h := congr_arg Subtype.val hr
            change φ' (r - r₁) = φ' 0
            ext1; change φ (r - r₁) = φ 0
            change u' 0 + ∑ j, (r - r₁) j • Fin.tail u' j =
              u' 0 + ∑ j, (0 : Fin (m + 1) → F) j • Fin.tail u' j
            simp only [Pi.sub_apply, sub_smul, Pi.zero_apply, zero_smul,
              Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib]
            have h' : ∑ j, r j • Fin.tail u' j = ∑ j, r₁ j • Fin.tail u' j :=
              add_left_cancel h
            simp [h']
          · intro a₁ _ a₂ _ h; have := congr_arg (· + r₁) h; simpa using this
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            have h := congr_arg Subtype.val hr
            have h' : ∑ j, r j • Fin.tail u' j = ∑ j, (0 : Fin (m + 1) → F) j • Fin.tail u' j :=
              add_left_cancel h
            exact ⟨r + r₁, by
              ext1; change φ (r + r₁) = φ r₁
              change u' 0 + ∑ j, (r + r₁) j • Fin.tail u' j =
                u' 0 + ∑ j, r₁ j • Fin.tail u' j
              simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
              simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h'
              congr 1; rw [h', zero_add],
              by ext; simp⟩
        -- Apply the helper lemma.
        have hPr_eq := pr_uniform_surj_const_fiber φ' hφ'_surj hk₀_pos hfib_const
          (fun y => δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ)
        -- hPr_eq : Pr_{r}[P(φ' r)] = Pr_{y}[P(y)]
        -- Goal: Pr_{r}[δᵣ(u'0 + ∑ r i • u' i.succ, RS) ≤ δ] > errorBound
        -- hPr_aff: Pr_{y}[δᵣ(y.1, RS) ≤ δ] > errorBound
        -- Need: show the goal's Pr = hPr_eq's LHS.
        -- (φ' r).1 = φ r = u' 0 + ∑ r i • Fin.tail u' i = u' 0 + ∑ r i • u' i.succ.
        exact hPr_eq ▸ hPr_aff
      have hja_u' : jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F)))
          (δ := δ) (W := u') :=
        correlatedAgreement_affine_spaces (k := m + 1) hδ u' hPr_coeff
      -- Convert jointAgreement (W := u') → jointAgreement (W := C i).
      obtain ⟨S_ja, hS_card, v', hv'⟩ := hja_u'
      refine ⟨S_ja, hS_card, fun j => if j = 0 then v' 0 else v' j + v' 0, fun j => ?_⟩
      by_cases hj0 : j = 0
      · subst hj0; simp only [ite_true]; exact hv' 0
      · simp only [hj0, ite_false]
        constructor
        · exact (ReedSolomon.code domain deg).add_mem (hv' j).1 (hv' 0).1
        · intro col hcol
          have hv'j := (Finset.mem_filter.mp ((hv' j).2 hcol)).2
          have hv'0 := (Finset.mem_filter.mp ((hv' 0).2 hcol)).2
          have hu'0 : u' 0 = C i 0 := if_pos rfl
          rw [hu'0] at hv'0
          simp only [u', hj0, ite_false, Pi.sub_apply] at hv'j
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [Pi.add_apply, hv'j, hv'0, sub_add_cancel]⟩

end CoreResults

end ProximityGap
