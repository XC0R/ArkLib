/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

import Mathlib.Data.Fintype.Sets
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Logic.Equiv.Basic
/-!
  # Definitions and Theorems about Proximity Gaps

  We state the main results from [BCIKS20] about proximity gap properties of Reed-Solomon codes.

  ## References

  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
      * NB we use version 20210703:203025

  ## Main Definitions and Statements

  - statement of Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].
  - statements of all the correlated agreement theorems from [BCIKS20]:
  Theorem 1.4 (Main Theorem — Correlated agreement over affine lines),
  Theorem 4.1 (Correlated agreement over affine lines in the unique decoding regime),
  Theorem 1.5 (Correlated agreement for low-degree parameterised curves)
  Theorem 1.6 (Correlated agreement over affine spaces).

-/

namespace ProximityGap

open NNReal Finset Function
open scoped BigOperators
open NNReal Finset Function ProbabilityTheory Finset
open scoped BigOperators LinearCode
open Code

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ (0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ ((1-ρ)/2 , 1 - √ρ)`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := ρ (ReedSolomon.code domain deg)
  if δ ∈ Set.Icc 0 ((1 - ρ)/2)
  then Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ)/2) (1 - ρ.sqrt)
       then letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0

noncomputable instance instFintype_affineSpan_image {k : ℕ} [NeZero k]
  (U : Fin k → (ι → F)) :
  Fintype (SetLike.coe (affineSpan F (Finset.univ.image U : Set (ι → F)))) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance instFintype_spanPoints_image {k : ℕ} [NeZero k]
  (U : Fin k → (ι → F)) :
  Fintype (spanPoints F (Finset.univ.image U : Set (ι → F))) := by
  classical
  exact Fintype.ofFinite _


theorem affSpanFinset_eq_toFinset_affineSpan_image {k : ℕ} [NeZero k] (U : Fin k → (ι → F)) :
  (SetLike.coe (affineSpan F (Finset.univ.image U : Set (ι → F))) |>.toFinset) =
    (Affine.AffSpanFinset (F := F) (ι := ι) U) := by
  classical
  ext x
  simp [Affine.AffSpanFinset, Affine.AffSpanSet]
  rfl

theorem affSpanFinset_eq_toFinset_spanPoints_image {k : ℕ} [NeZero k] (U : Fin k → (ι → F)) :
  (spanPoints F (Finset.univ.image U : Set (ι → F))).toFinset =
    (Affine.AffSpanFinset (F := F) (ι := ι) U) := by
  classical
  simpa using
    (affSpanFinset_eq_toFinset_affineSpan_image (F := F) (ι := ι) (U := U))

theorem affineSpan_range_eq_mk'_span_vsub {k : ℕ} [NeZero k] (U : Fin k → (ι → F)) :
  let u0 : (ι → F) := U 0
  affineSpan F (Set.range U) =
    AffineSubspace.mk' u0 (Submodule.span F (Set.range fun i : Fin k => U i - u0)) := by
  classical
  -- unfold the `let u0 := U 0`
  simp
  have hu0 : U 0 ∈ affineSpan F (Set.range U) :=
    mem_affineSpan (k := F) (hp := Set.mem_range_self (0 : Fin k))
  have hu0' :
      U 0 ∈
        AffineSubspace.mk' (U 0)
          (Submodule.span F (Set.range fun i : Fin k => U i - U 0)) := by
    simp
  apply (AffineSubspace.eq_iff_direction_eq_of_mem hu0 hu0').2
  -- compare directions
  simpa [direction_affineSpan, vsub_eq_sub] using
    (vectorSpan_range_eq_span_range_vsub_right (k := F) (p := U) (i0 := (0 : Fin k)))

theorem finset_univ_image_fin_cases_eq {α : Type} [DecidableEq α] {k : ℕ} [NeZero k] (U : Fin k → α) :
  (Finset.univ.image (fun i : Fin (k + 1) => Fin.cases (U 0) U i)) = Finset.univ.image U := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨i, hi, rfl⟩
    -- hi : i ∈ (Finset.univ : Finset (Fin (k+1)))
    -- goal: Fin.cases (U 0) U i ∈ Finset.univ.image U
    -- split i by cases
    refine Fin.cases ?h0 ?hs i
    · -- i = 0
      -- show U 0 in image U
      refine Finset.mem_image.2 ?_
      refine ⟨0, by simp, rfl⟩
    · intro j
      -- i = succ j
      refine Finset.mem_image.2 ?_
      refine ⟨j, by simp, rfl⟩
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨j, hj, rfl⟩
    -- show U j in image of cases
    refine Finset.mem_image.2 ?_
    refine ⟨Fin.succ j, by simp, ?_⟩
    simp


open scoped ProbabilityTheory in
theorem prob_uniform_eq_of_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
  (e : α ≃ β) (P : β → Prop) [DecidablePred P] :
  Pr_{let a ← $ᵖ α}[P (e a)] = Pr_{let b ← $ᵖ β}[P b] := by
  classical
  -- Expand the probability expressions to explicit finite sums.
  simp [Bind.bind, Pure.pure, PMF.bind_apply, PMF.pure_apply, PMF.uniformOfFintype_apply,
    tsum_fintype]

  -- Rewrite the left sum over `α` as a sum over `β` using the equivalence `e`.
  have hsum : (∑ a : α, if P (e a) then (↑(Fintype.card α) : ENNReal)⁻¹ else 0) =
      ∑ b : β, if P b then (↑(Fintype.card α) : ENNReal)⁻¹ else 0 := by
    refine Fintype.sum_equiv e
      (fun a : α => if P (e a) then (↑(Fintype.card α) : ENNReal)⁻¹ else 0)
      (fun b : β => if P b then (↑(Fintype.card α) : ENNReal)⁻¹ else 0) ?_
    intro a
    rfl

  -- The uniform weights agree since `e` is a bijection.
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hc : ((↑(Fintype.card α) : ENNReal)⁻¹) = ((↑(Fintype.card β) : ENNReal)⁻¹) := by
    simpa [hcard]

  -- Finish.
  calc
    (∑ a : α, if P (e a) then (↑(Fintype.card α) : ENNReal)⁻¹ else 0)
        = ∑ b : β, if P b then (↑(Fintype.card α) : ENNReal)⁻¹ else 0 := hsum
    _ = ∑ b : β, if P b then (↑(Fintype.card β) : ENNReal)⁻¹ else 0 := by
      simp [hc]


open scoped ProbabilityTheory in
theorem prob_uniform_eq_one_of_forall {α : Type} [Fintype α] [Nonempty α]
  (P : α → Prop) [DecidablePred P]
  (hP : ∀ a, P a) :
  Pr_{let a ← $ᵖ α}[P a] = (1 : ENNReal) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card (F := α) (P := P)]
  have hfilter : (Finset.filter (α := α) P Finset.univ) = Finset.univ := by
    ext a
    simp [hP a]
  -- after rewriting the filter to `univ`, the ratio is `|α| / |α|`
  simp [hfilter, ENNReal.div_self, Fintype.card_ne_zero]

theorem relDistFromCode_smul_eq {C : Submodule F (ι → F)} {z : F} (hz : z ≠ 0) (x : ι → F) :
  δᵣ(z • x, (C : Set (ι → F))) = δᵣ(x, (C : Set (ι → F))) := by
  classical
  -- `hammingDist` (hence `relHammingDist`) is invariant under scaling by a nonzero scalar.
  have hzregF : IsSMulRegular F z := by
    intro a b hab
    -- On `F`, scalar multiplication is just multiplication.
    exact mul_left_cancel₀ hz (by simpa [smul_eq_mul] using hab)

  have hrel : ∀ a b : ι → F, Code.relHammingDist (z • a) (z • b) = Code.relHammingDist a b := by
    intro a b
    unfold Code.relHammingDist
    have hHam : hammingDist (z • a) (z • b) = hammingDist a b := by
      simpa using
        (hammingDist_smul (α := F) (β := fun _ : ι => F) (k := z) (x := a) (y := b)
          (hk := fun _ => hzregF))
    simpa [hHam]

  -- Unfold the definition of distance-to-code and show the sets of admissible upper bounds coincide.
  unfold Code.relDistFromCode
  congr 1
  ext d
  constructor
  · rintro ⟨v, hvC, hvdist⟩
    refine ⟨z⁻¹ • v, C.smul_mem z⁻¹ hvC, ?_⟩
    -- Rewrite the distance using scaling-invariance.
    have hcast : (Code.relHammingDist (z • x) (z • (z⁻¹ • v)) : ENNReal) =
        Code.relHammingDist x (z⁻¹ • v) :=
      congrArg (fun q : ℚ≥0 => (q : ENNReal)) (hrel x (z⁻¹ • v))
    have hdist_eq : (Code.relHammingDist x (z⁻¹ • v) : ENNReal) =
        Code.relHammingDist (z • x) v := by
      -- use `z • (z⁻¹ • v) = v`
      simpa [smul_inv_smul₀ hz] using hcast.symm
    simpa [hdist_eq] using hvdist
  · rintro ⟨v, hvC, hvdist⟩
    refine ⟨z • v, C.smul_mem z hvC, ?_⟩
    have hdist_eq : (Code.relHammingDist (z • x) (z • v) : ENNReal) =
        Code.relHammingDist x v :=
      congrArg (fun q : ℚ≥0 => (q : ENNReal)) (hrel x v)
    simpa [hdist_eq] using hvdist

open scoped Pointwise in
theorem zero_vadd_finset (s : Finset (ι → F)) : (0 : ι → F) +ᵥ s = s := by
  classical
  ext x
  simp [Finset.mem_vadd_finset]

section
open NNReal Finset Function

open scoped BigOperators
open scoped ReedSolomonCode

variable {l : ℕ} [NeZero l]
         {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped Pointwise in
open scoped ProbabilityTheory in
open Uniform in
/--
Lemma 6.3 in [BCIKS20].

Let `V` be a Reed–Solomon code of rate `ρ`, and let `U` be an affine subspace obtained by
translating a linear subspace `U'`.  For a proximity parameter `δ` below the Johnson/Guruswami–Sudan
list-decoding bound (`0 < δ < 1 - √ρ`), suppose that a random point `u` sampled uniformly from `U`
is `δ`-close to `V` with probability strictly larger than the proximity-gap error bound `ε`.  Then
every point of the underlying linear subspace `U'` is also `δ`-close to `V`.
-/
theorem average_proximity_implies_proximity_of_linear_subspace [DecidableEq ι] [DecidableEq F]
  {u : Fin (l + 2) → ι → F} {k : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ∈ Set.Ioo 0 (1 - (ReedSolomonCode.sqrtRate (k + 1) domain))) :
  letI U' : Finset (ι → F) :=
    SetLike.coe (affineSpan F (Finset.univ.image (Fin.tail u))) |>.toFinset
  letI U : Finset (ι → F) := u 0 +ᵥ U'
  haveI : Nonempty U := by
    apply Finset.Nonempty.to_subtype
    apply Finset.Nonempty.vadd_finset
    rw [Set.toFinset_nonempty]
    exact Set.Nonempty.mono (subset_affineSpan F _)
      (Finset.coe_nonempty.mpr (Finset.univ_nonempty.image _))
  letI ε : ℝ≥0 := ProximityGap.errorBound δ (k + 1) domain
  letI V := ReedSolomon.code domain (k + 1)
  Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε → ∀ u' ∈ U', δᵣ(u', V) ≤ δ := by
  sorry

end

open scoped ProbabilityTheory in
open scoped Pointwise in
theorem affSpanFinset_all_close_of_prob_gt {k : ℕ} [NeZero k] {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  (U : Fin k → (ι → F)) {δ : ℝ≥0}
  [Nonempty (Affine.AffSpanFinset (F := F) (ι := ι) U)]
  (hδ : δ ∈ Set.Ioo 0 (1 - (ReedSolomonCode.sqrtRate deg domain)))
  (hprob :
    Pr_{let x ← $ᵖ (Affine.AffSpanFinset (F := F) (ι := ι) U)}[
      δᵣ(x.val, (ReedSolomonCode.toFinset domain deg)) ≤ δ
    ] > (errorBound δ deg domain)) :
  ∀ x ∈ (Affine.AffSpanFinset (F := F) (ι := ι) U),
    δᵣ(x, (ReedSolomonCode.toFinset domain deg)) ≤ δ := by
  classical
  -- Define an auxiliary family `u : Fin (k+2) → ι → F` whose tail has the same image as `U`.
  let u : Fin (k + 2) → (ι → F) :=
    fun i =>
      Fin.cases (0 : ι → F)
        (fun j : Fin (k + 1) => Fin.cases (U 0) U j) i

  -- The finset `U'` from Lemma 6.3 in BCIKS20, specialized to our `u`.
  let U' : Finset (ι → F) :=
    (SetLike.coe (affineSpan F (Finset.univ.image (Fin.tail u) : Set (ι → F))) |>.toFinset)

  -- The translated affine space `u 0 +ᵥ U'`; here `u 0 = 0` so this is just `U'`.
  let Uspace : Finset (ι → F) := u 0 +ᵥ U'

  -- First, show that `Finset.univ.image (Fin.tail u)` is the same as `Finset.univ.image U`.
  have htail : (Fin.tail u) = (fun i : Fin (k + 1) => Fin.cases (U 0) U i) := by
    funext i
    rfl
  have himage : (Finset.univ.image (Fin.tail u)) = Finset.univ.image U := by
    simpa [htail] using (finset_univ_image_fin_cases_eq (U := U))

  -- Rewrite `U'` as the affine span finset of `U`.
  have hU' : U' = (Affine.AffSpanFinset (F := F) (ι := ι) U) := by
    have :
        (SetLike.coe (affineSpan F (Finset.univ.image (Fin.tail u) : Set (ι → F))) |>.toFinset) =
          (SetLike.coe (affineSpan F (Finset.univ.image U : Set (ι → F))) |>.toFinset) := by
      simpa [himage]
    calc
      U' = (SetLike.coe (affineSpan F (Finset.univ.image U : Set (ι → F))) |>.toFinset) := by
        simpa [U', this]
      _ = (Affine.AffSpanFinset (F := F) (ι := ι) U) := by
        simpa using (affSpanFinset_eq_toFinset_affineSpan_image (U := U))

  have hu0 : u 0 = (0 : ι → F) := by
    rfl

  have hUeq : Uspace = (Affine.AffSpanFinset (F := F) (ι := ι) U) := by
    simp [Uspace, hu0, zero_vadd_finset, hU']

  -- Provide `Nonempty` for `Uspace` by transporting it from `Affine.AffSpanFinset U`.
  haveI : Nonempty (Uspace : Type _) := by
    simpa [hUeq] using
      (inferInstance : Nonempty (Affine.AffSpanFinset (F := F) (ι := ι) U))

  -- Rewrite the original probability hypothesis to use the set `ReedSolomon.code`.
  have hprob_set :
      Pr_{let x ← $ᵖ (Affine.AffSpanFinset (F := F) (ι := ι) U)}[
        δᵣ(x.val, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ
      ] > (errorBound δ deg domain) := by
    simpa [ReedSolomonCode.toFinset, ReedSolomonCode.RScodeSet] using hprob

  -- Transport `hprob_set` from `Affine.AffSpanFinset U` to `Uspace` using an equivalence.
  have hprob' :
      Pr_{let x ← $ᵖ (Uspace)}[
        δᵣ(x.val, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ
      ] > (errorBound δ deg domain) := by
    -- Equivalence induced by the equality of the underlying finsets.
    let e : (Uspace : Type _) ≃ (Affine.AffSpanFinset (F := F) (ι := ι) U : Type _) :=
      Equiv.subtypeEquivRight
        (p := fun x : (ι → F) => x ∈ Uspace)
        (q := fun x : (ι → F) => x ∈ (Affine.AffSpanFinset (F := F) (ι := ι) U))
        (fun x => by simpa [hUeq])

    let P : (Affine.AffSpanFinset (F := F) (ι := ι) U : Type _) → Prop := fun x =>
      δᵣ(x.val, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ

    have hEq :
        Pr_{let a ← $ᵖ (Uspace : Type _)}[P (e a)] =
          Pr_{let b ← $ᵖ (Affine.AffSpanFinset (F := F) (ι := ι) U : Type _)}[P b] :=
      prob_uniform_eq_of_equiv (α := (Uspace : Type _))
        (β := (Affine.AffSpanFinset (F := F) (ι := ι) U : Type _)) e P

    have hRHS :
        Pr_{let b ← $ᵖ (Affine.AffSpanFinset (F := F) (ι := ι) U : Type _)}[P b]
          > (errorBound δ deg domain) := by
      simpa [P] using hprob_set

    have hLHS :
        Pr_{let a ← $ᵖ (Uspace : Type _)}[P (e a)] > (errorBound δ deg domain) :=
      lt_of_lt_of_eq hRHS hEq.symm

    -- `e` is the identity on underlying values, so `P (e a)` is the desired predicate on `a`.
    simpa [P, e] using hLHS

  -- Prepare the `hδ` hypothesis in the form expected by Lemma 6.3 (degree written as `k+1`).
  have hdeg1 : (deg - 1) + 1 = deg := by
    have h1 : 1 ≤ deg := Nat.succ_le_iff.mpr (NeZero.pos deg)
    simpa using (Nat.sub_add_cancel h1)

  have hδ' : δ ∈ Set.Ioo 0 (1 - (ReedSolomonCode.sqrtRate ((deg - 1) + 1) domain)) := by
    simpa [hdeg1] using hδ

  -- Apply Lemma 6.3 from BCIKS20.
  have hcloseU' : ∀ x ∈ U', δᵣ(x, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
    have hmain :=
      (average_proximity_implies_proximity_of_linear_subspace (F := F) (ι := ι)
        (l := k) (u := u) (k := deg - 1) (domain := domain) (δ := δ) hδ')

    have hprob'' :
        Pr_{let x ← $ᵖ (Uspace)}[
          δᵣ(x.val, (ReedSolomon.code domain ((deg - 1) + 1) : Set (ι → F))) ≤ δ
        ] > (errorBound δ ((deg - 1) + 1) domain) := by
      simpa [hdeg1] using hprob'

    have hres := hmain hprob''
    simpa [U', hdeg1] using hres

  -- Finish: rewrite `U'` back to `Affine.AffSpanFinset U`.
  intro x hx
  have hx' : x ∈ U' := by
    simpa [hU'] using hx
  have hxclose := hcloseU' x hx'
  simpa [ReedSolomonCode.toFinset, ReedSolomonCode.RScodeSet] using hxclose

open scoped ProbabilityTheory in
open scoped Pointwise in
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0}
  (hδ : δ ∈ Set.Ioo 0 (1 - (ReedSolomonCode.sqrtRate deg domain)))
  (hε : (errorBound δ deg domain : ENNReal) < 1) :
  δ_ε_proximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanFinsetCollection C)
    δ
    (errorBound δ deg domain) := by
  classical
  unfold δ_ε_proximityGap
  intro S hS
  intro hS_nonempty
  rcases hS with ⟨i, rfl⟩
  -- abbreviate
  set P : Finset (ι → F) := ReedSolomonCode.toFinset domain deg
  set ε : ℝ≥0 := errorBound δ deg domain
  set pr : ENNReal :=
    Pr_{let x ← $ᵖ (Affine.AffSpanFinset (F := F) (ι := ι) (C i))}[
      δᵣ(x.val, P) ≤ δ
    ]
  by_cases hpr : pr ≤ ε
  · -- small probability case
    rw [xor_def]
    refine Or.inr ?_
    refine ⟨hpr, ?_⟩
    intro hpr1
    have h1 : (1 : ENNReal) ≤ (ε : ENNReal) := by
      simpa [pr, ε, hpr1] using hpr
    exact (not_le_of_gt hε) h1
  · -- large probability case
    have hpr_gt : pr > ε := lt_of_not_ge hpr
    have hall :
        ∀ x ∈ (Affine.AffSpanFinset (F := F) (ι := ι) (C i)),
          δᵣ(x, P) ≤ δ := by
      -- apply proximity gap lemma
      have :=
        affSpanFinset_all_close_of_prob_gt (ι := ι) (F := F) (k := k) (deg := deg)
          (domain := domain) (U := C i) (δ := δ) (hδ := hδ)
          (hprob := by
            -- rewrite pr
            simpa [pr, P, ε] using hpr_gt)
      simpa [P] using this
    have hforall :
        ∀ x : (Affine.AffSpanFinset (F := F) (ι := ι) (C i)),
          δᵣ(x.val, P) ≤ δ := by
      intro x
      exact hall x.val x.property
    have pr_eq_one :
        Pr_{let x ← $ᵖ (Affine.AffSpanFinset (F := F) (ι := ι) (C i))}[
          δᵣ(x.val, P) ≤ δ
        ] = (1 : ENNReal) := by
      -- use uniform probability lemma
      -- define predicate
      let Q : (Affine.AffSpanFinset (F := F) (ι := ι) (C i)) → Prop :=
        fun x => δᵣ(x.val, P) ≤ δ
      have hQ : ∀ x, Q x := by
        intro x
        exact hforall x
      simpa [Q] using (prob_uniform_eq_one_of_forall (α := (Affine.AffSpanFinset (F := F) (ι := ι) (C i))) Q hQ)
    rw [xor_def]
    refine Or.inl ?_
    refine ⟨?_, hpr⟩
    · -- show pr = 1
      simpa [pr] using pr_eq_one



set_option linter.style.commandStart false

/-
Theorem 4.1. Suppose `δ ≤ (1-ρ) / 2`. Let `u_0, u_1: 𝒟 → 𝔽_q` be functions. Let
`S = {z ∈ 𝔽_q : Δ(u_0 + z u_1, V) ≤ δ}`
and suppose `|S| > n`. Then `S = 𝔽_q`. Furthermore there are `v_0, v_1 ∈ V` such that
for all `z ∈ 𝔽_q`, `Δ(u_0 + z u_1, v_0 + z v_1) ≤ δ`
and in fact `|{x ∈ 𝒟 : (u_0(x), u_1(x)) ≠ (v_0(x), v_1(x))}| ≤ δ|𝒟|.`
-/
theorem RS_correlatedAgreement_affineLines_uniqueDecodingRegime
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    : δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by sorry

/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and two words `u₀` and `u₁`, such that the probability that a random affine
line passing through `u₀` and `u₁` is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u₀` and `u₁` have correlated agreement. -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  -- Do casing analysis on `hδ`
  if hδ_uniqueDecodingRegime :
    δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)
  then
    RS_correlatedAgreement_affineLines_uniqueDecodingRegime (hδ := hδ_uniqueDecodingRegime)
  else
    -- TODO: theorem 5.1 for list-decoding regime
    sorry


/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the  probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by sorry

open Affine in
/-- Theorem 1.6 (Correlated agreement over affine spaces) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space with origin `u₀` and affine generting set `u₁, ..., uκ`
such that the probability a random point in the affine space is `δ`-close to the Reed-Solomon
code is at most `ε`. Then the words `u₀, ..., uκ` have correlated agreement.

Note that we have `k+2` vectors to form the affine space. This an intricacy needed us to be
able to isolate the affine origin from the affine span and to form a generating set of the
correct size. The reason for taking an extra vector is that after isolating the affine origin,
the affine span is formed as the span of the difference of the rest of the vector set. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin (k + 1) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  : δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by sorry

end CoreResults

section BCIKS20ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan
open Polynomial.Bivariate
open RatFunc

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√rhon.
-/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

open Classical in
noncomputable def proximity_gap_degree_bound (rho : ℚ) (m n : ℕ) : ℕ :=
  let b := D_X rho m n
  if h : ∃ n : ℕ, b = n
  then h.choose - 1
  else Nat.floor b

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(rho, m) = 1 - √rho - √rho/2m.
-/
noncomputable def proximity_gap_johnson (rho : ℚ) (m : ℕ) : ℝ :=
  (1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m)


/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition (k + 1) m ((proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n)) ωs f Q := by
  sorry

open Polynomial in
/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, rho] such that δᵣ(w, P) ≤ δ₀(rho, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. Note that in F[X][Y], the term X actually refers to
    the outer variable, Y.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {w : Fin n → F}
  {Q : F[X][Y]}
  (cond : Condition (k + 1) m (proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n) ωs w Q)
  {p : ReedSolomon.code ωs n}
  (h : δᵣ(w, p) ≤ proximity_gap_johnson ((k + 1 : ℚ) / n) m)
  :
  (X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q := by sorry


section

open Polynomial
open Polynomial.Bivariate

/-- Following [BCIKS20] this the Y-degree of
    a trivariate polynomial `Q`.
-/
def D_Y (Q : F[Z][X][Y]) : ℕ := Bivariate.natDegreeY Q

/-- The YZ-degree of a trivariate polynomial.
-/
def D_YZ (Q : F[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
            (
              fun j =>
                Option.getD (
                  Finset.max (
                    Finset.image
                      (fun k => j + (Bivariate.coeff Q j k).natDegree)
                      (Q.coeff j).support
                  )
                ) 0
            )
            Q.support
    )

end

/-- The Guruswami-Sudan condition as it is stated in
    [BCIKS20].
-/
structure ModifiedGuruswami
  (m n k : ℕ)
  (ωs : Fin n ↪ F)
  (Q : F[Z][X][Y])
  (u₀ u₁ : Fin n → F)
  where
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : natWeightedDegree Q 1 k < D_X ((k + 1) / (n : ℚ)) n m
  /-- Multiplicity of the roots is at least `m`. -/
  Q_multiplicity : ∀ i, rootMultiplicity Q
              (Polynomial.C <| ωs i)
              ((Polynomial.C <| u₀ i) + Polynomial.X * (Polynomial.C <| u₁ i))
            ≥ m
  /-- The X-degree bound. -/
  Q_deg_X :
    degreeX Q < D_X ((k + 1) / (n : ℚ)) n m
  /-- The Y-degree bound. -/
  Q_D_Y :
    D_Y Q < D_X (k + 1 / (n : ℚ)) n m / k
  /-- The YZ-degree bound. -/
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

/-- The claim 5.4 from [BCIKS20].
    It essentially claims that there exists
    a soultion to the Guruswami-Sudan constraints above.
-/
lemma modified_guruswami_has_a_solution
  {m n k : ℕ}
  {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
  :
  ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁
    := by sorry

end

variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

noncomputable instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s := Fintype.ofFinite _

/-- The set `S` (equation 5.2 of [BCIKS20]). -/
noncomputable def coeffs_of_close_proximity (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
  : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
/-- There exists a `δ`-close polynomial `P_z` for each `z`
    from the set `S`.
-/
lemma exists_Pz_of_coeffs_of_close_proximity
  {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁)
  :
  ∃ Pz : F[X], Pz.natDegree ≤ k ∧ δᵣ(u₀ + z • u₁, Pz.eval ∘ ωs) ≤ δ := by
    unfold coeffs_of_close_proximity at hS
    obtain ⟨w, hS, dist⟩ : ∃ a ∈ ReedSolomon.code ωs (k + 1), ↑δᵣ(u₀ + z • u₁, a) ≤ δ := by
      simpa using hS
    obtain ⟨p, hS⟩ : ∃ y ∈ degreeLT F (k + 1), (ReedSolomon.evalOnPoints ωs) y = w := by
      simpa using hS
    exact ⟨p, ⟨
      by if h : p = 0
         then simp [h]
         else rw [mem_degreeLT, degree_eq_natDegree h, Nat.cast_lt] at hS; grind,
      by convert dist; rw [←hS.2]; rfl
    ⟩⟩

/-- The `δ`-close polynomial `Pz` for each `z`
    from the set `S` (`coeffs_of_close_proximity`).
-/
noncomputable def Pz
  {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
  :
  F[X]
  := (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose

/-- Proposition 5.5 from [BCIKS20].
    There exists a subset `S'` of the set `S` and
    a bivariate polynomial `P(X, Z)` that matches
    `Pz` on that set.
-/
lemma exists_a_set_and_a_matching_polynomial
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ S', ∃ (h_sub : S' ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁), ∃ P : F[Z][X],
    #S' > #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (2 * D_Y Q) ∧
    ∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1) ∧
    P.natDegree ≤ k ∧
    Bivariate.degreeX P ≤ 1 := by sorry

/-- The subset `S'` extracted from the proprosition 5.5.
-/
noncomputable def matching_set
  (ωs : Fin n ↪ F)
  (δ : ℚ)
  (u₀ u₁ : Fin n → F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : Finset F := (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose

/-- `S'` is indeed a subset of `S` -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : matching_set k ωs δ u₀ u₁ h_gs ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁ :=
  (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose_spec.choose

/-- The equation 5.12 from [BCIKS20]. -/
lemma irreducible_factorization_of_gs_solution
  {k : ℕ}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (C : F[Z][X]) (R : List F[Z][X][Y]) (f : List ℕ) (e : List ℕ),
    R.length = f.length ∧
    f.length = e.length ∧
    ∀ eᵢ ∈ e, 1 ≤ eᵢ ∧
    ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
    ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
    Q = (Polynomial.C C) *
        ∏ (Rᵢ ∈ R.toFinset) (fᵢ ∈ f.toFinset) (eᵢ ∈ e.toFinset),
          (Rᵢ.comp ((Y : F[Z][X][Y]) ^ fᵢ))^eᵢ
  := sorry

/-- Claim 5.6 of [BCIKS20]. -/
lemma discr_of_irred_components_nonzero
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∃ x₀,
      ∀ R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose,
      Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

open Trivariate in
open Bivariate in
/-- Claim 5.7 of [BCIKS20]. -/
lemma exists_factors_with_large_common_root_set
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0} sorry)
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- Claim 5.7 establishes existens of a polynomial `R`.
    This is the extraction of this polynomial.
-/
noncomputable def R
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X][Y] := (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose

/-- Claim 5.7 establishes existens of a polynomial `H`.
    This is the extraction of this polynomial.
-/
noncomputable def H
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X] := (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose

/-- An important property of the polynomial
    `H` extracted from claim 5.7 is that it is
    irreducible.
-/
lemma irreducible_H
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  Irreducible (H k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.1

open BCIKS20AppendixA.ClaimA2 in
/-- The claim 5.8 from [BCIKS20].
    States that the approximate solution is
    actually a solution.
    This version of the claim is stated in terms
    of coefficients.
-/
lemma approximate_solution_is_exact_solution_coeffs
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∀ t ≥ k,
  α'
    x₀
    (R k δ x₀ h_gs)
    (irreducible_H k h_gs)
    t
  =
  (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
  := by sorry

open BCIKS20AppendixA.ClaimA2 in
/-- The claim 5.8 from [BCIKS20].
    States that the approximate solution is
    actually a solution.
    This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs))) := by
   sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.9 from [BCIKS20].
    States that the solution `γ` is linear in
    the variable `Z`.
-/
lemma solution_gamma_is_linear_in_Z
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear represenation of the solution `γ`
    extracted from the claim 5.9.
-/
noncomputable def P
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  F[Z][X] :=
  let v₀ := Classical.choose (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  let v₁ := Classical.choose
    (Classical.choose_spec <| solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open BCIKS20AppendixA.ClaimA2 in
/-- The extracted `P` from claim 5.9 equals `γ`.
-/
lemma gamma_eq_P
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
  BCIKS20AppendixA.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs) :=
  Classical.choose_spec
    (Classical.choose_spec (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs))

/-- The set `S'_x` from [BCIKS20] (just before claim 5.10).
    The set of all `z∈S'` such that `w(x,z)` matches `P_z(x)`.
-/
noncomputable def matching_set_at_x
  (δ : ℚ)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (x : Fin n)
  : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs,
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h)).eval (ωs x)} sorry

/-- Claim 5.10 of [BCIKS20].
    Needed to prove the claim 5.9.
    This claim states that `γ(x)=w(x,Z)` if
    the cardinality |S'_x| is big enough.
-/
lemma solution_gamma_matches_word_if_subset_large
  {ωs : Fin n ↪ F}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {x : Fin n}
  {D : ℕ}
  (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
  (hx : (matching_set_at_x k δ h_gs x).card >
    (2 * k + 1)
      * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
      * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
      * D)
  : (P k δ x₀ h_gs).eval (Polynomial.C (ωs x)) =
    (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X
  := by sorry

/-- Claim 5.11 from [BCIKS20].
    There exists a set of points `{x₀,...,x_{k+1}}`
    such that the sets S_{x_j} satisfy the condition
    in the claim 5.10.
-/
lemma exists_points_with_large_matching_subset
  {ωs : Fin n ↪ F}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {x : Fin n}
  {D : ℕ}
  (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
  :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by sorry

end BCIKS20ProximityGapSection5

section BCIKS20ProximityGapSection6
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ} [NeZero n]

/-- An affine curve parameterized by the field
    and whose defining vectors are the vectors
    `u 0, ..., u (n - 1)`.
-/
def curve {l : ℕ} (u : Fin l → Fin n → F) (z : F) : Fin n → F :=
    ∑ i, z ^ i.1 • u i

/-- The parameters for which the curve points are
    `δ`-close to a set `V` (typically, a linear code).
    The set `S` from the proximity gap paper.
-/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
  (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(curve u z, V) ≤ δ} := by infer_instance
  @Set.toFinset _ { z | δᵣ(curve u z, V) ≤ δ} this

/-- If the set of points `δ`-close to the code `V` has
    at least `n * l + 1` points then
    there exists a curve defined by vectors `v` from `V`
    such that the points of `curve u` and `curve v`
    are `δ`-close with the same parameters.
    Moreover, `u` and `v` differ at at most `δ * n`
    positions.
-/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ}
  {rho : ℚ≥0}
  {δ : ℚ≥0}
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ (1 - rho) / 2)
  {u : Fin l → Fin n → F}
  (hS : n * l < (coeffs_of_close_proximity_curve δ u V).card)
  :
  coeffs_of_close_proximity_curve δ u V = F ∧
  ∃ (v : Fin l → Fin n → F),
    ∀ z, δᵣ(curve u z, curve v z) ≤ δ ∧
    ({ x : Fin n | Finset.image u ≠ Finset.image v } : Finset _).card ≤ δ * n := by
  sorry

/-- The distance bound from the proximity gap paper.
-/
noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- If the set of points on the curve defined by `u`
    close to `V` has at least
    `((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ)))
    * n ^ 2 * l + 1` points then
    there exist vectors `v` from `V` that
    `(1 - δ) * n` close to vectors `u`.
-/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l : ℕ}
  [Finite F]
  {m : ℕ}
  {rho : ℚ≥0}
  {δ : ℚ≥0}
  (hm : 3 ≤ m)
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ δ₀ rho m)
  {u : Fin l → Fin n → F}
  (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ)))
    * n ^ 2 * l < (coeffs_of_close_proximity_curve δ u V).card)
  :
  ∃ (v : Fin l → Fin n → F),
  ∀ i, v i ∈ V ∧
  (1 - δ) * n ≤ ({x : Fin n | ∀ i, u i x = v i x} : Finset _).card := sorry

end BCIKS20ProximityGapSection6

section BCIKS20ProximityGapSection7

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ}

namespace WeightedAgreement

open NNReal Finset Function

open scoped BigOperators

section

variable {n : Type} [Fintype n] [DecidableEq n]

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]
         (μ : ι → Set.Icc (0 : ℚ) 1)

/-- Relative μ-agreement between words `u` and `v`. -/
noncomputable def agree (u v : ι → F) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ { i | u i = v i }, (μ i).1

/-- `μ`-agreement between a word and a set `V`. -/
noncomputable def agree_set (u : ι → F) (V : Finset (ι → F)) [Nonempty V] : ℝ :=
  (Finset.image (agree μ u) V).max' (nonempty_coe_sort.1 (by aesop))

/-- Weighted size of a subdomain. -/
noncomputable def mu_set (ι' : Finset ι) : ℝ :=
  1/(Fintype.card ι) * ∑ i ∈ ι', (μ i).1

/-- `μ`-weighted correlated agreement. -/
noncomputable def weightedCorrelatedAgreement
  (C : Set (ι → F)) [Nonempty C] {k : ℕ} (U : Fin k → ι → F) : ℝ :=
  sSup {x |
    ∃ D' ⊆ (Finset.univ (α := ι)),
      x = mu_set μ D' ∧
      ∃ v : Fin k → ι → F, ∀ i, v i ∈ C ∧ ∀ j ∈ D', v i j = U i j
  }

open ReedSolomonCode

instance {domain : ι ↪ F} {deg : ℕ} : Nonempty (finCarrier domain deg) := by
  unfold finCarrier
  apply Nonempty.to_subtype
  simp [ReedSolomon.code]
  exact Submodule.nonempty (Polynomial.degreeLT F deg)

open ProbabilityTheory in
/-- Weighted correlated agreement over curves.
    Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve generated by vectors `u`, such that the probability that a random
point on the curve is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.
-/
theorem weighted_correlated_agreement_for_parameterized_curves
  [DecidableEq ι] [Fintype ι] [DecidableEq F] [Fintype F]
  {l : ℕ}
  {k : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0}
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  letI ε := ProximityGap.errorBound δ deg domain
  letI pr :=
    let curve := Curve.polynomialCurveFinite (F := F) (A := F) u
    Pr_{let u ←$ᵖ curve}[agree_set μ u (finCarrier domain deg) ≥ α]
  (hproximity : pr > (l + 1 : NNReal) * ε) →
  (h_additionally : pr ≥
    ENNReal.ofReal (
      ((l + 1) * (M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
      *
      (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
    )
  ) →
  ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ ι' ≥ α ∧
    ∀ i, ∀ x ∈ ι', u i x = v i x := sorry

/-- Weighted correlated agreement over curves.
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve generated by vectors `u`, such that the probability that a random
point on the curve is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.

Version with different bounds.
-/
theorem weighted_correlated_agreement_for_parameterized_curves'
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M m : ℕ}
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {
    z : F | agree_set μ (fun i ↦ ∑ j, z ^ j.1 * u j i) (finCarrier domain deg) ≥ α
  }
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS :
    Finset.card S >
      max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)
    ) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := sorry

open Uniform in
open scoped Pointwise in
open ProbabilityTheory in
/-- Weighted correlated agreement over affine spaces.
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space generated by vectors `u`, such that the probability that a random
point from the space is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.
-/
theorem weighted_correlated_agreement_over_affine_spaces
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
  letI ε := ProximityGap.errorBound α deg domain
  letI pr :=
    Pr_{let u ←$ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
    }[agree_set μ u (finCarrier domain deg) ≥ α]
  pr > ε →
  pr ≥ ENNReal.ofReal (
         ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
         *
         (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
       ) →
  ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ ι' ≥ α ∧
    ∀ i, ∀ x ∈ ι', u i x = v i x := by sorry

open scoped ProbabilityTheory in
open scoped Pointwise in
open Uniform in
/-- Weighted correlated agreement over affine spaces.
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space generated by vectors `u`, such that the probability that a random
point from the space is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.

Version with different bounds.
-/
theorem weighted_correlated_agreement_over_affine_spaces'
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M m : ℕ}
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI pr :=
    Pr_{let u ←$ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
    }[agree_set μ u (finCarrier domain deg) ≥ α]
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  letI numeratorl : ℝ := (1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2
  letI denominatorl : ℝ := (3 * sqrtRate^3) * Fintype.card F
  letI numeratorr : ℝ := (2 * m + 1) * (M * Fintype.card ι + 1)
  letI denominatorr : ℝ := sqrtRate * Fintype.card F
  pr > ENNReal.ofReal (max (numeratorl / denominatorl) (numeratorr / denominatorr)) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := by sorry

/--
Lemma 7.5 in [BCIKS20].

This is the “list agreement on a curve implies correlated agreement” lemma.

We are given two lists of functions `u, v : Fin (l + 2) → ι → F`, where each `v i` is a
Reed–Solomon codeword of degree `deg` over the evaluation domain `domain`.  From these
lists we form the bivariate “curves”

* `w   x z = ∑ i, z^(i.1) * u i x`,
* `wtilde x z = ∑ i, z^(i.1) * v i x`.

Fix a finite set `S' ⊆ F` with `S'.card > l + 1`, and a (product) measure `μ` on the
evaluation domain `ι`.  Assume that for every `z ∈ S'` the one-dimensional functions
`w · z` and `wtilde · z` have agreement at least `α` with respect to `μ`.  Then the set
of points `x` on which *all* coordinates agree, i.e. `u i x = v i x` for every `i`,
has μ-measure strictly larger than

`α - (l + 1) / (S'.card - (l + 1))`.
-/
lemma list_agreement_on_curve_implies_correlated_agreement_bound
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {v : Fin (l + 2) → ι → F}
  (hv : ∀ i, v i ∈ (ReedSolomon.code domain deg))
  {S' : Finset F}
  (hS'_card : S'.card > l + 1) :
  letI w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  letI wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  (hS'_agree : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α) →
  mu_set μ {x : ι | ∀ i, u i x = v i x} >
  α - ((l + 1) : ℝ) / (S'.card - (l + 1)) := by sorry

/--
Lemma 7.6 in [BCIKS20].

This is the “integral-weight” strengthening of the list-agreement-on-a-curve ⇒
correlated-agreement bound.

We have two lists of functions `u, v : Fin (l + 2) → ι → F`, where each `v i` is a
Reed–Solomon codeword of degree `deg` over the evaluation domain `domain`.  From
these lists we form the bivariate “curves”
* `w x z     = ∑ i, z^(i.1) * u i x`,
* `wtilde x z = ∑ i, z^(i.1) * v i x`.

The domain `ι` is finite and is equipped with a weighted measure `μ`, where each
weight `μ i` is a rational with common denominator `M`.  Let `S' ⊆ F` be a set of
field points with
* `S'.card > l + 1`, and
* `S'.card ≥ (M * Fintype.card ι + 1) * (l + 1)`.

Assume that for every `z ∈ S'` the µ-weighted agreement between `w · z` and
`wtilde · z` is at least `α`.  Then the µ-measure of the set of points where *all*
coordinates agree, i.e. where `u i x = v i x` for every `i`, is at least `α`:

`mu_set μ {x | ∀ i, u i x = v i x} ≥ α`.
-/
lemma sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M : ℕ}
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  {v : Fin (l + 2) → ι → F}
  (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
  {S' : Finset F}
  (hS'_card : S'.card > l + 1)
  (hS'_card₁ : S'.card ≥ (M * Fintype.card ι + 1) * (l + 1)) :
  letI w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  letI wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  (hS'_agree : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α) →
  mu_set μ {x : ι | ∀ i, u i x = v i x} ≥ α := by sorry
end

end WeightedAgreement

end BCIKS20ProximityGapSection7

end ProximityGap
