/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

import Mathlib.Data.Fintype.Card
import ArkLib.Data.CodingTheory.PolishchukSpielman
import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import ArkLib.Data.Probability.Instances
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


/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].

Let `C` be a collection of affine spaces. Then `C` displays a `(δ, ε)`-proximity gap with respect to
a Reed-Solomon code, where `(δ,ε)` are the proximity and error parameters defined up to the
Johnson bound. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  δ_ε_proximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanFinsetCollection C)
    δ
    (errorBound δ deg domain) := by sorry

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


theorem RS_rate_mul_card_le_deg {ι : Type} [Fintype ι] [Nonempty ι]
  {F : Type} [Field F]
  (deg : ℕ) (domain : ι ↪ F) :
  ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) * (Fintype.card ι : ℝ≥0)
    ≤ (deg : ℝ≥0)) := by
  classical
  -- unfold the definition of rate and reduce the statement to a finrank bound
  simp [LinearCode.rate, LinearCode.length, LinearCode.dim]
  -- `ReedSolomon.code` is the image of `Polynomial.degreeLT F deg` under evaluation,
  -- so its finrank is bounded by the finrank of `Polynomial.degreeLT F deg`.
  simpa [ReedSolomon.code, Polynomial.finrank_degreeLT_n] using
    (Submodule.finrank_map_le (R := F)
      (f := ReedSolomon.evalOnPoints (F := F) domain)
      (p := Polynomial.degreeLT F deg))


theorem ca_Pr_uniform_mono {α : Type} [Fintype α] [Nonempty α]
  (p q : α → Prop) (hpq : ∀ a, p a → q a) :
  Pr_{let a ←$ᵖ α}[p a] ≤ Pr_{let a ←$ᵖ α}[q a] := by
  classical
  -- unfold `Pr_{...}[...]`
  simp [ProbabilityTheory.prStx]
  -- goal: (p <$> $ᵖ α) True ≤ (q <$> $ᵖ α) True
  -- rewrite as outer measures over preimages of `{True}`
  have hp' : (p <$> ($ᵖ α)) True = ($ᵖ α).toOuterMeasure (p ⁻¹' ({True} : Set Prop)) := by
    -- `PMF.toOuterMeasure_apply_singleton` rewrites evaluation at `True`
    -- and `PMF.toOuterMeasure_map_apply` rewrites outer measure of a mapped PMF
    calc
      (p <$> ($ᵖ α)) True = (p <$> ($ᵖ α)).toOuterMeasure ({True} : Set Prop) := by
        symm
        simpa using (PMF.toOuterMeasure_apply_singleton (p := (p <$> ($ᵖ α))) True)
      _ = ($ᵖ α).toOuterMeasure (p ⁻¹' ({True} : Set Prop)) := by
        simpa [PMF.monad_map_eq_map] using
          (PMF.toOuterMeasure_map_apply (p := ($ᵖ α)) (f := p) (s := ({True} : Set Prop)))
  have hq' : (q <$> ($ᵖ α)) True = ($ᵖ α).toOuterMeasure (q ⁻¹' ({True} : Set Prop)) := by
    calc
      (q <$> ($ᵖ α)) True = (q <$> ($ᵖ α)).toOuterMeasure ({True} : Set Prop) := by
        symm
        simpa using (PMF.toOuterMeasure_apply_singleton (p := (q <$> ($ᵖ α))) True)
      _ = ($ᵖ α).toOuterMeasure (q ⁻¹' ({True} : Set Prop)) := by
        simpa [PMF.monad_map_eq_map] using
          (PMF.toOuterMeasure_map_apply (p := ($ᵖ α)) (f := q) (s := ({True} : Set Prop)))
  -- reduce to a monotonicity statement on outer measures
  rw [hp', hq']
  refine PMF.toOuterMeasure_mono (p := ($ᵖ α)) ?_
  intro a ha
  -- `ha : a ∈ p ⁻¹' {True} ∩ ($ᵖ α).support`
  have hpa_eq : p a = True := by
    -- unpack `a ∈ p ⁻¹' {True}`
    simpa [Set.preimage, Set.mem_singleton_iff] using ha.1
  have hpa : p a := by
    simpa [hpa_eq] using (trivial : True)
  have hqa : q a := hpq a hpa
  have hqa_eq : q a = True := by
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      exact hqa
  -- show `a ∈ q ⁻¹' {True}`
  have : q a ∈ ({True} : Set Prop) := by
    simpa [Set.mem_singleton_iff, hqa_eq]
  exact this

theorem ca_RS_rate_mul_card_sq_le_deg_sq {ι : Type} [Fintype ι] [Nonempty ι]
  {F : Type} [Field F]
  (deg : ℕ) (domain : ι ↪ F) :
  (((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) ^ 2)
    * ((Fintype.card ι : ℝ) ^ 2)
    ≤ (deg : ℝ) ^ 2 := by
  classical
  have hNN :
      (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) * (Fintype.card ι : ℝ≥0)
        ≤ (deg : ℝ≥0) :=
    RS_rate_mul_card_le_deg (ι := ι) (F := F) deg domain
  have hR :
      ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)
        ≤ (deg : ℝ) := by
    exact_mod_cast hNN

  have ha :
      0 ≤ ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
    positivity
  have hb : 0 ≤ (deg : ℝ) := by
    positivity

  have hsq_mul :
      (((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ))
          * (((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ))
        ≤ (deg : ℝ) * (deg : ℝ) := by
    exact mul_le_mul hR hR ha hb

  -- Convert back to squares and rewrite (a*b)^2
  have hsq :
      (((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ^ 2
        ≤ (deg : ℝ) ^ 2 := by
    simpa [pow_two] using hsq_mul

  simpa [mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

theorem ca_card_add_one_div_two_le_card_sq {ι : Type} [Fintype ι] [Nonempty ι] :
  (((Fintype.card ι : ℝ) + 1) / 2) ≤ (Fintype.card ι : ℝ) ^ 2 := by
  classical
  have hn_nat : (1 : ℕ) ≤ Fintype.card ι := by
    -- `Fintype.card_pos` gives `0 < card`
    simpa using (Nat.succ_le_iff.2 (Fintype.card_pos (α := ι)))
  have hn : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hn_nat
  nlinarith

theorem ca_const_128_23_div_20_pow7_le_half: ((128 * 23 : ℝ) / (20 ^ 7 : ℝ)) ≤ (1 / 2 : ℝ) := by
  norm_num

theorem ca_inv_add_three_le_const_inv (s m : ℝ≥0)
  (hs : s ≠ 0) (hm : m ≠ 0) (hmle : m ≤ s / 20) :
  ((m : ℝ)⁻¹ + 3 / (s : ℝ)) ≤ (23 / 20 : ℝ) * (m : ℝ)⁻¹ := by
  have hs0 : (s : ℝ) ≠ 0 := by
    exact_mod_cast hs
  have hmleR : (m : ℝ) ≤ (s : ℝ) / 20 := by
    exact_mod_cast hmle

  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have hmpos' : (0 : ℝ≥0) < m := lt_of_le_of_ne (zero_le _) (Ne.symm hm)
    exact_mod_cast hmpos'

  have h20 : (20 : ℝ) / (s : ℝ) ≤ (m : ℝ)⁻¹ := by
    -- invert the inequality m ≤ s/20
    have h1 : (1 : ℝ) / ((s : ℝ) / 20) ≤ (1 : ℝ) / (m : ℝ) :=
      one_div_le_one_div_of_le hmpos hmleR
    -- rewrite reciprocals
    simpa [one_div, one_div_div] using h1

  have h3 : (3 : ℝ) / (s : ℝ) ≤ (3 / 20 : ℝ) * (m : ℝ)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left h20 (by nlinarith : (0 : ℝ) ≤ (3 / 20 : ℝ))
    -- simplify the left-hand side
    have : (3 / 20 : ℝ) * ((20 : ℝ) / (s : ℝ)) = (3 : ℝ) / (s : ℝ) := by
      field_simp [hs0]
    simpa [this, mul_assoc, mul_left_comm, mul_comm] using hmul

  calc
    (m : ℝ)⁻¹ + 3 / (s : ℝ)
        ≤ (m : ℝ)⁻¹ + (3 / 20 : ℝ) * (m : ℝ)⁻¹ := by
          -- add (m⁻¹) to the left of both sides
          simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right h3 ((m : ℝ)⁻¹))
    _ = (23 / 20 : ℝ) * (m : ℝ)⁻¹ := by
          ring

theorem ca_one_sub_tsub_comm (a b : ℝ≥0) : (1 - a - b) = (1 - b - a) := by
  simp [tsub_tsub, add_comm, add_left_comm, add_assoc]

theorem ca_prob_pos_singleton_iff {α : Type} [DecidableEq α]
  (a : α) (P : α → Prop) :
  (0 : ENNReal) < Pr_{let x ←$ᵖ (↥({a} : Finset α))}[P x.1] ↔ P a := by
  classical
  change (0 : ENNReal) < (PMF.map (fun x : (↥({a} : Finset α)) => P x.1) ($ᵖ (↥({a} : Finset α)))) True ↔ P a
  by_cases hPa : P a
  · -- identify the (unique) default element of the singleton subtype
    have hdef : (default : (↥({a} : Finset α))) = ⟨a, by simp⟩ := by
      ext x
      simp
    have hPa' : P ((default : (↥({a} : Finset α))).1) := by
      have : (default : (↥({a} : Finset α))).1 = a := by
        simpa using congrArg Subtype.val hdef
      simpa [this] using hPa
    have hnonempty : ({x ∈ ({default} : Finset (↥({a} : Finset α))) | P x.1}).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      refine ⟨default, ?_, hPa'⟩
      simp
    simpa [hPa] using hnonempty
  · simp [hPa]

def ca_uniformMu {ι : Type} : ι → Set.Icc (0 : ℚ) 1 := fun _ => ⟨(1 : ℚ), by simp⟩

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

theorem ca_agree_uniform_eq_card_div {ι : Type} [Fintype ι] [DecidableEq ι]
  {F : Type} [Field F] [DecidableEq F]
  (w v : ι → F) :
  WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w v
    = ((#{i : ι | w i = v i} : ℝ) / (Fintype.card ι : ℝ)) := by
  classical
  -- unfold the definition of agreement and the uniform weight function
  simp [WeightedAgreement.agree, ca_uniformMu, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]


theorem ca_agree_set_ge_of_relDistFromCode_le {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} {w : ι → F} :
  (δᵣ(w, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (δ : ENNReal)) →
    WeightedAgreement.agree_set (μ := ca_uniformMu (ι := ι)) w (ReedSolomonCode.finCarrier domain deg) ≥ (1 - δ : ℝ≥0) := by
  intro hδw
  classical
  rcases (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (u := w)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1 hδw with ⟨v, hvC, hvδ⟩

  have hvFin : v ∈ ReedSolomonCode.finCarrier domain deg := by
    simp [ReedSolomonCode.finCarrier, hvC]

  have hmax :
      WeightedAgreement.agree_set (μ := ca_uniformMu (ι := ι)) w (ReedSolomonCode.finCarrier domain deg)
        ≥ WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w v := by
    unfold WeightedAgreement.agree_set
    set s : Finset ℝ :=
      Finset.image (WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w)
        (ReedSolomonCode.finCarrier domain deg)
    have hs_mem :
        WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w v ∈ s := by
      dsimp [s]
      refine Finset.mem_image.2 ?_
      exact ⟨v, hvFin, rfl⟩
    have hs_nonempty : s.Nonempty := ⟨_, hs_mem⟩

    have hgreat : IsGreatest (↑s : Set ℝ) (s.max' hs_nonempty) :=
      Finset.isGreatest_max' (s := s) (H := hs_nonempty)

    have hle : WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w v ≤ s.max' hs_nonempty := by
      exact hgreat.2 hs_mem

    dsimp [s] at hle ⊢
    simpa [ge_iff_le] using hle

  -- Now lower bound the agreement of `w` with this particular `v`.
  have hagree :
      WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w v ≥ (1 - δ : ℝ≥0) := by
    rcases (Code.relCloseToWord_iff_exists_agreementCols (u := w) (v := v) (δ := δ)).1 hvδ with
      ⟨S, hS_card, hS⟩

    have hS_subset : S ⊆ ({ i : ι | w i = v i } : Finset ι) := by
      intro i hi
      have hi' : w i = v i := (hS i).1 hi
      simpa using hi'

    have hcard_le : (S.card : ℝ≥0) ≤ (({ i : ι | w i = v i } : Finset ι).card : ℝ≥0) := by
      exact_mod_cast Finset.card_le_card hS_subset

    have hS_card_nnreal :
        (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      exact (Code.relDist_floor_bound_iff_complement_bound (n := Fintype.card ι)
        (upperBound := S.card) (δ := δ)).1 hS_card

    -- Work in NNReal first, then cast to ℝ.
    have hn_pos : 0 < (Fintype.card ι : ℝ≥0) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)

    -- From the cardinality bound, obtain a bound on normalized size.
    have hnorm : (1 - δ : ℝ≥0) ≤ (S.card : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
      -- `a ≤ b / n` ↔ `a*n ≤ b`
      exact (le_div_iff₀ hn_pos).2 hS_card_nnreal

    -- compare with the full agreement set
    have hnorm_le :
        (S.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)
          ≤ (({ i : ι | w i = v i } : Finset ι).card : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
      -- divide the card inequality by n
      exact div_le_div_of_nonneg_right hcard_le (by exact le_of_lt hn_pos)

    have hnorm' :
        (1 - δ : ℝ≥0)
          ≤ (({ i : ι | w i = v i } : Finset ι).card : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
      exact le_trans hnorm hnorm_le

    -- rewrite agree via cardinalities
    have hagree_eq :
        WeightedAgreement.agree (μ := ca_uniformMu (ι := ι)) w v
          = ((#{i : ι | w i = v i} : ℝ) / (Fintype.card ι : ℝ)) := by
      simpa using (ca_agree_uniform_eq_card_div (ι := ι) (F := F) w v)

    -- cast the NNReal inequality to ℝ and finish
    -- TODO: relate finset card to `#{i | ...}`
    -- fallback: try `exact_mod_cast` and simp
    
    -- We'll try to close using `nlinarith` after rewriting.
    
    -- convert hnorm' to ℝ
    have hnormR : ((1 - δ : ℝ≥0) : ℝ) ≤
        ((({ i : ι | w i = v i } : Finset ι).card : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ) := by
      exact_mod_cast hnorm'

    -- now rewrite the RHS to match hagree_eq and conclude
    --
    -- try simp to identify the finset card with the fintype card of the subtype
    --
    have hcard_ident :
        ((({ i : ι | w i = v i } : Finset ι).card : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ)
          = ((#{i : ι | w i = v i} : ℝ) / (Fintype.card ι : ℝ)) := by
      -- hope simp knows this
      simp

    -- put together
    have hfinal : ((1 - δ : ℝ≥0) : ℝ) ≤ ((#{i : ι | w i = v i} : ℝ) / (Fintype.card ι : ℝ)) := by
      simpa [hcard_ident] using hnormR

    -- conclude with rewritten agree
    --
    -- goal is ≥, so rewrite and use hfinal
    --
    simpa [hagree_eq, ge_iff_le] using hfinal

  -- Combine.
  exact le_trans hagree hmax

theorem ca_mu_set_uniform {ι : Type} [Fintype ι] (S : Finset ι) :
    WeightedAgreement.mu_set (μ := (ca_uniformMu (ι := ι))) S = (S.card : ℝ) / (Fintype.card ι : ℝ) := by
  classical
  unfold WeightedAgreement.mu_set ca_uniformMu
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem ca_weighted_additional_bound_endgame {ι : Type} [Fintype ι] [Nonempty ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0)
  (hδJ : δ ∈ Set.Ioo
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
    (1 - ReedSolomonCode.sqrtRate deg domain)) :
  let ρ : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
  let m : ℝ≥0 := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
  let n : ℝ := (Fintype.card ι : ℝ)
  (n + 1) * 23 * (m : ℝ) ^ 6 * 128 ≤ 20 * (deg : ℝ) ^ 2 := by
  classical
  dsimp
  set ρ : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) with hρ
  set s : ℝ≥0 := ρ.sqrt with hs
  set m : ℝ≥0 := min (1 - s - δ) (s / 20) with hm
  set n : ℝ := (Fintype.card ι : ℝ) with hn

  -- Step 1: m ≤ s/20
  have hmle : m ≤ s / 20 := by
    simpa [hm] using (min_le_right (1 - s - δ) (s / 20))

  -- Step 2: m^6 ≤ (s/20)^6 (in ℝ)
  have hm_pow : (m : ℝ) ^ 6 ≤ ((s / 20 : ℝ≥0) : ℝ) ^ 6 := by
    have hm_pow_nn : m ^ 6 ≤ (s / 20) ^ 6 := by
      exact pow_le_pow_left' hmle 6
    exact_mod_cast hm_pow_nn

  have hmul : (n + 1) * 23 * (m : ℝ) ^ 6 * 128 ≤ (n + 1) * 23 * (((s / 20 : ℝ≥0) : ℝ) ^ 6) * 128 := by
    have hn23 : 0 ≤ (n + 1) * 23 := by positivity
    have h1 : (n + 1) * 23 * (m : ℝ) ^ 6 ≤ (n + 1) * 23 * (((s / 20 : ℝ≥0) : ℝ) ^ 6) := by
      have := mul_le_mul_of_nonneg_left hm_pow hn23
      simpa [mul_assoc] using this
    have h128 : 0 ≤ (128 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_right h1 h128
    simpa [mul_assoc] using this

  refine le_trans hmul ?_

  -- Work with A/20
  have h20pos : (0 : ℝ) < 20 := by norm_num
  have hAdiv : ((n + 1) * 23 * (((s / 20 : ℝ≥0) : ℝ) ^ 6) * 128) / 20 ≤ (deg : ℝ) ^ 2 := by
    -- rewrite A/20 into the nice form
    have hrewrite : ((n + 1) * 23 * (((s / 20 : ℝ≥0) : ℝ) ^ 6) * 128) / 20
        = (n + 1) * ((128 * 23 : ℝ) / (20 ^ 7 : ℝ)) * (s : ℝ) ^ 6 := by
      simp [NNReal.coe_div, div_pow]
      ring
    -- switch to this form
    rw [hrewrite]
    -- now use the constant inequality
    have hconst : ((128 * 23 : ℝ) / (20 ^ 7 : ℝ)) ≤ (1 / 2 : ℝ) :=
      ca_const_128_23_div_20_pow7_le_half
    have hstep1 : (n + 1) * ((128 * 23 : ℝ) / (20 ^ 7 : ℝ)) * (s : ℝ) ^ 6
        ≤ (n + 1) * (1 / 2 : ℝ) * (s : ℝ) ^ 6 := by
      have hn1 : 0 ≤ (n + 1 : ℝ) := by positivity
      have hs6 : 0 ≤ (s : ℝ) ^ 6 := by positivity
      have : (n + 1) * ((128 * 23 : ℝ) / (20 ^ 7 : ℝ)) ≤ (n + 1) * (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hconst hn1
      have := mul_le_mul_of_nonneg_right this hs6
      simpa [mul_assoc] using this

    -- card inequality
    have hcard : ((n + 1) / 2) ≤ n ^ 2 := by
      simpa [hn] using (ca_card_add_one_div_two_le_card_sq (ι := ι))

    -- deduce s < 1
    have hδ_lt : δ < 1 - s := by
      simpa [ReedSolomonCode.sqrtRate, hρ.symm, hs.symm] using hδJ.2
    have hs_lt_one_nnr : s < 1 := by
      have hpos : (0 : ℝ≥0) < 1 - s :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ δ from by simp) hδ_lt
      simpa using (tsub_pos_iff_lt).1 hpos
    have hs_le_one : (s : ℝ) ≤ 1 := by
      exact le_of_lt (by exact_mod_cast hs_lt_one_nnr)
    have hs6_le_hs4 : (s : ℝ) ^ 6 ≤ (s : ℝ) ^ 4 := by
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
      exact pow_le_pow_of_le_one hs0 hs_le_one (by decide : (4 : ℕ) ≤ 6)

    -- rewrite s^4 = ρ^2
    have hs4_eq : (s : ℝ) ^ 4 = (ρ : ℝ) ^ 2 := by
      have hs2 : (s : ℝ) ^ 2 = (ρ : ℝ) := by
        have : s ^ 2 = ρ := by
          simpa [hs] using (NNReal.sq_sqrt ρ)
        exact_mod_cast this
      calc
        (s : ℝ) ^ 4 = ((s : ℝ) ^ 2) ^ 2 := by
          ring
        _ = (ρ : ℝ) ^ 2 := by
          simp [hs2]

    -- rate*card^2 ≤ deg^2
    have hrate : ((ρ : ℝ) ^ 2) * (n ^ 2) ≤ (deg : ℝ) ^ 2 := by
      have := ca_RS_rate_mul_card_sq_le_deg_sq (ι := ι) (F := F) deg domain
      simpa [hρ, hn, pow_two] using this

    -- final chaining
    calc
      (n + 1) * ((128 * 23 : ℝ) / (20 ^ 7 : ℝ)) * (s : ℝ) ^ 6
          ≤ (n + 1) * (1 / 2 : ℝ) * (s : ℝ) ^ 6 := hstep1
      _ = ((n + 1) / 2) * (s : ℝ) ^ 6 := by
            ring
      _ ≤ (n ^ 2) * (s : ℝ) ^ 6 := by
            have hs6' : 0 ≤ (s : ℝ) ^ 6 := by positivity
            have := mul_le_mul_of_nonneg_right hcard hs6'
            simpa [mul_assoc] using this
      _ ≤ (n ^ 2) * (s : ℝ) ^ 4 := by
            have hn2 : 0 ≤ (n ^ 2 : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left hs6_le_hs4 hn2
            simpa [mul_assoc] using this
      _ = (n ^ 2) * (ρ : ℝ) ^ 2 := by
            simp [hs4_eq, mul_assoc]
      _ = ((ρ : ℝ) ^ 2) * (n ^ 2) := by
            ring
      _ ≤ (deg : ℝ) ^ 2 := hrate

  -- convert back from /20
  have hA : (n + 1) * 23 * (((s / 20 : ℝ≥0) : ℝ) ^ 6) * 128 ≤ (deg : ℝ) ^ 2 * 20 :=
    (div_le_iff₀ h20pos).1 hAdiv
  simpa [mul_assoc, mul_comm, mul_left_comm] using hA

theorem ca_weighted_additional_bound_le_k_mul_errorBound {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (k deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0)
  (hδJ : δ ∈ Set.Ioo
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
    (1 - ReedSolomonCode.sqrtRate deg domain)) :
  ENNReal.ofReal (
      ((k) * ((Fintype.card ι) + 1) : ℝ) / (Fintype.card F : ℝ)
      *
      (1 / min ((1 - δ) - ReedSolomonCode.sqrtRate deg domain) ((ReedSolomonCode.sqrtRate deg domain) / 20) +
        3 / (ReedSolomonCode.sqrtRate deg domain))
    )
    ≤ (k : ENNReal) * (errorBound δ deg domain : ENNReal) := by
  classical
  by_cases hk0 : k = 0
  · subst hk0
    simp

  set ρ : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
  have hδJρ : δ ∈ Set.Ioo (((1 : ℝ≥0) - ρ) / 2) (1 - ρ.sqrt) := by
    simpa [ρ, ReedSolomonCode.sqrtRate] using hδJ

  by_cases hs0 : ρ.sqrt = 0
  · have hs0' : ReedSolomonCode.sqrtRate deg domain = 0 := by
      simpa [ReedSolomonCode.sqrtRate, ρ] using hs0
    simp [ProximityGap.errorBound, ρ, hs0, hs0', hδJρ, hk0]

  have hs : ρ.sqrt ≠ 0 := hs0

  -- Define the min-parameter `m`
  set m : ℝ≥0 := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
  have hmle : m ≤ ρ.sqrt / 20 := by
    exact min_le_right _ _

  -- Show `m ≠ 0`
  have hpos1 : 0 < (1 - ρ.sqrt - δ) := by
    exact (tsub_pos_iff_lt.2 hδJρ.2)
  have hs_pos : 0 < ρ.sqrt := by
    exact lt_of_le_of_ne (by exact zero_le _) (Ne.symm hs)
  have hpos2 : 0 < ρ.sqrt / 20 := by
    have h20 : (0 : ℝ≥0) < (20 : ℝ≥0) := by norm_num
    exact div_pos hs_pos h20
  have hm_pos : 0 < m := by
    have : (0 : ℝ≥0) < min (1 - ρ.sqrt - δ) (ρ.sqrt / 20) := lt_min hpos1 hpos2
    simpa [m] using this
  have hm : m ≠ 0 := ne_of_gt hm_pos

  -- `δ` is not in the unique-decoding regime interval
  have h_notIcc : ¬ δ ∈ Set.Icc (0 : ℝ≥0) ((1 - ρ) / 2) := by
    intro hIcc
    exact (not_lt_of_ge hIcc.2) hδJρ.1

  -- Unfold `errorBound` in the Johnson regime
  have h_errorBound :
      errorBound δ deg domain =
        ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩ := by
    have hmin : min (1 - ρ.sqrt - δ) (ρ.sqrt / 20) = m := by
      simp [m]
    simpa [ProximityGap.errorBound, ρ, h_notIcc, hδJρ, hmin]

  -- Rewrite the LHS min to `m`
  have hmin_LHS :
      min ((1 - δ) - ReedSolomonCode.sqrtRate deg domain)
          (ReedSolomonCode.sqrtRate deg domain / 20)
        = m := by
    simp [ReedSolomonCode.sqrtRate, ρ, m, ca_one_sub_tsub_comm (a := (ρ.sqrt)) (b := δ)]

  -- Bound the inverse expression by a constant multiple
  have h_inv_bound : ((m : ℝ)⁻¹ + 3 / (ρ.sqrt : ℝ)) ≤ (23 / 20 : ℝ) * (m : ℝ)⁻¹ := by
    exact ca_inv_add_three_le_const_inv (s := ρ.sqrt) (m := m) hs hm hmle

  -- First compare with the simplified real expression using `h_inv_bound`
  have hLHS_le :
      ENNReal.ofReal (
          ((k) * ((Fintype.card ι) + 1) : ℝ) / (Fintype.card F : ℝ)
          *
            (1 /
                  min ((1 - δ) - ReedSolomonCode.sqrtRate deg domain)
                    (ReedSolomonCode.sqrtRate deg domain / 20) +
                3 / (ReedSolomonCode.sqrtRate deg domain))
        )
        ≤
        ENNReal.ofReal (
          ((k) * ((Fintype.card ι) + 1) : ℝ) / (Fintype.card F : ℝ)
          * ((23 / 20 : ℝ) * (m : ℝ)⁻¹)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hfactor_nonneg :
        0 ≤ ((k) * ((Fintype.card ι) + 1) : ℝ) / (Fintype.card F : ℝ) := by
      positivity
    have hinner :
        (1 /
              min ((1 - δ) - ReedSolomonCode.sqrtRate deg domain)
                (ReedSolomonCode.sqrtRate deg domain / 20) +
            3 / (ReedSolomonCode.sqrtRate deg domain))
          ≤
          (23 / 20 : ℝ) * (m : ℝ)⁻¹ := by
      have : (1 / (m : ℝ) + 3 / (ρ.sqrt : ℝ)) ≤ (23 / 20 : ℝ) * (m : ℝ)⁻¹ := by
        simpa [one_div] using h_inv_bound
      simpa [hmin_LHS, ReedSolomonCode.sqrtRate, ρ, one_div] using this
    have := mul_le_mul_of_nonneg_left hinner hfactor_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc] using this

  -- reduce to proving the bound with the simplified LHS
  refine le_trans hLHS_le ?_

  -- compare via `toReal` on the RHS
  refine ENNReal.ofReal_le_of_le_toReal ?_

  have hRHS_toReal :
      ENNReal.toReal ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) =
        (k : ℝ) * ((deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)) : ℝ) := by
    simp [h_errorBound, ENNReal.toReal_mul, mul_assoc, mul_left_comm, mul_comm]

  -- rewrite RHS, then work purely in `ℝ`
  simp [hRHS_toReal]

  set n : ℝ := (Fintype.card ι : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)

  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hk0)
  have hqpos : (0 : ℝ) < q := by
    subst q
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hmposR : (0 : ℝ) < (m : ℝ) := by
    simpa [NNReal.coe_pos] using hm_pos

  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmposR

  -- clear denominators and simplify to a polynomial inequality
  field_simp [hkne, hqne, hmne]

  have hpow2 : (2 : ℝ) ^ 7 = (128 : ℝ) := by norm_num

  -- finish via the endgame lemma
  have hend :=
    ca_weighted_additional_bound_endgame (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ) hδJ
  simpa [ρ, m, n, hpow2] using hend

theorem correlatedAgreement_affine_curves_listDecodingRegime_k0 [DecidableEq ι]
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  : δ_ε_correlatedAgreementCurves (k := 0) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  simp [δ_ε_correlatedAgreementCurves]
  intro u hprob

  have hcurve : Curve.polynomialCurveFinite (F := F) (A := F) u = {u 0} := by
    ext v
    simp [Curve.polynomialCurveFinite, Fin.sum_univ_one]

  have hu0_close : δᵣ(u 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
    let T := (↥(Curve.polynomialCurveFinite (F := F) (A := F) u))
    let p : PMF T := $ᵖ T
    let f : T → Prop := fun a =>
      δᵣ((a : ι → F), (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ

    have hprob' : (0 : ENNReal) < (f <$> p) True := by
      dsimp [p, f, T]
      simpa using hprob

    have hTrue_support : True ∈ (PMF.map f p).support := by
      refine (PMF.mem_support_iff (PMF.map f p) True).2 ?_
      have hprob'' : (0 : ENNReal) < (PMF.map f p) True := by
        -- avoid unfolding `PMF.map`; just change to the `<$>` form.
        change (0 : ENNReal) < (f <$> p) True
        exact hprob'
      exact ne_of_gt hprob''

    rcases (PMF.mem_support_map_iff (p := p) (f := f) (b := True)).1 hTrue_support with
      ⟨a, -, ha_eq⟩

    have ha : f a := by
      simpa [ha_eq] using (show True from trivial)

    have ha_mem' : (a : ι → F) ∈ ({u 0} : Finset (ι → F)) := by
      simpa [T, hcurve] using a.property
    have ha_eq_u0 : (a : ι → F) = u 0 := by
      simpa using ha_mem'

    simpa [f, ha_eq_u0] using ha

  have hAgree :
      jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (W := u) := by
    rcases
        (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist
            (u := u 0) (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1
          hu0_close with
      ⟨v0, hv0_mem, hv0_close⟩

    rcases
        (Code.relCloseToWord_iff_exists_agreementCols
            (u := u 0) (v := v0) (δ := δ)).1
          hv0_close with
      ⟨S, hS_card, hS_agree⟩

    refine ⟨S, ?_, ?_⟩
    · have hS_card' : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) :=
        (Code.relDist_floor_bound_iff_complement_bound
            (n := Fintype.card ι) (upperBound := S.card) (δ := δ)).1
          hS_card
      simpa [ge_iff_le] using hS_card'
    · refine ⟨fun _ : Fin 1 => v0, ?_⟩
      intro i
      fin_cases i
      constructor
      · exact hv0_mem
      · intro j hj
        refine Finset.mem_filter.2 ?_
        refine ⟨Finset.mem_univ j, ?_⟩
        exact ((hS_agree j).1 hj).symm

  exact
    (Code.jointAgreement_iff_jointProximity
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (u := u) (δ := δ)).1
      hAgree


theorem correlatedAgreement_affine_curves_listDecodingRegime_succ [DecidableEq ι] {k : ℕ}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδJ : δ ∈ Set.Ioo
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
    (1 - ReedSolomonCode.sqrtRate deg domain))
  : δ_ε_correlatedAgreementCurves (k := Nat.succ k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementCurves
  intro U hPrClose

  -- Uniform weights, agreement threshold α = 1 - δ
  let μ : ι → Set.Icc (0 : ℚ) 1 := ca_uniformMu (ι := ι)
  let α : ℝ≥0 := 1 - δ
  let M : ℕ := 1

  have hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ) := by
    intro i
    refine ⟨1, ?_⟩
    simp [μ, M, ca_uniformMu]

  -- Probabilities over the finite polynomial curve
  let curve : Finset (ι → F) := Curve.polynomialCurveFinite (F := F) (A := F) U
  let prClose : ENNReal :=
    Pr_{let y ←$ᵖ ↥curve}[δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (δ : ENNReal)]
  let prAgree : ENNReal :=
    Pr_{let y ←$ᵖ ↥curve}[
      WeightedAgreement.agree_set (μ := μ) y.1 (ReedSolomonCode.finCarrier domain deg) ≥ α]

  have hprClose : prClose > (Nat.succ k : ℝ≥0) * (errorBound δ deg domain) := by
    simpa [prClose, curve] using hPrClose

  have hprClose_le_prAgree : prClose ≤ prAgree := by
    have hpq :
        ∀ y : ↥curve,
          (δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (δ : ENNReal)) →
            WeightedAgreement.agree_set (μ := μ) y.1 (ReedSolomonCode.finCarrier domain deg) ≥ α := by
      intro y hy
      have h :=
        ca_agree_set_ge_of_relDistFromCode_le (ι := ι) (F := F)
          (deg := deg) (domain := domain) (δ := δ) (w := y.1) hy
      simpa [μ, α] using h

    simpa [prClose, prAgree] using
      (ca_Pr_uniform_mono (α := ↥curve)
        (p := fun y : ↥curve =>
          δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (δ : ENNReal))
        (q := fun y : ↥curve =>
          WeightedAgreement.agree_set (μ := μ) y.1 (ReedSolomonCode.finCarrier domain deg) ≥ α)
        hpq)

  have hproximity : prAgree > (Nat.succ k : ℝ≥0) * (errorBound δ deg domain) :=
    lt_of_lt_of_le hprClose hprClose_le_prAgree

  -- Rewrite `hproximity` into the exact shape used by the weighted theorem.
  have hproximity' :
      (let curve := Curve.polynomialCurveFinite (F := F) (A := F) U;
        Pr_{let y ←$ᵖ ↥curve}[
          WeightedAgreement.agree_set (μ := μ) y.1 (ReedSolomonCode.finCarrier domain deg) ≥ α])
        > (k + 1 : ℝ≥0) * (errorBound δ deg domain) := by
    simpa [prAgree, curve, Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using hproximity

  -- Additional bound needed by the weighted theorem.
  have h_additionally' :
      (let curve := Curve.polynomialCurveFinite (F := F) (A := F) U;
        Pr_{let y ←$ᵖ ↥curve}[
          WeightedAgreement.agree_set (μ := μ) y.1 (ReedSolomonCode.finCarrier domain deg) ≥ α])
      ≥
        ENNReal.ofReal (
          ((k + 1) * (M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
          *
          (1 / min (α - ReedSolomonCode.sqrtRate deg domain)
                ((ReedSolomonCode.sqrtRate deg domain) / 20) +
            3 / (ReedSolomonCode.sqrtRate deg domain))
        ) := by
    have h_bound :
        ENNReal.ofReal (
            ((Nat.succ k) * ((Fintype.card ι) + 1) : ℝ) / (Fintype.card F : ℝ)
            *
            (1 /
                min ((1 - δ) - ReedSolomonCode.sqrtRate deg domain)
                    ((ReedSolomonCode.sqrtRate deg domain) / 20) +
              3 / (ReedSolomonCode.sqrtRate deg domain))
          )
          ≤ (Nat.succ k : ENNReal) * (errorBound δ deg domain : ENNReal) :=
      ca_weighted_additional_bound_le_k_mul_errorBound (ι := ι) (F := F)
        (k := Nat.succ k) (deg := deg) (domain := domain) (δ := δ) hδJ

    have h_bound' :
        ENNReal.ofReal (
            ((k + 1) * (M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
            *
            (1 / min (α - ReedSolomonCode.sqrtRate deg domain)
                  ((ReedSolomonCode.sqrtRate deg domain) / 20) +
              3 / (ReedSolomonCode.sqrtRate deg domain))
          )
          ≤ (Nat.succ k : ENNReal) * (errorBound δ deg domain : ENNReal) := by
      simpa [α, M, Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm, mul_add] using h_bound

    have h_threshold_le :
        (Nat.succ k : ENNReal) * (errorBound δ deg domain : ENNReal)
          ≤
        (let curve := Curve.polynomialCurveFinite (F := F) (A := F) U;
          Pr_{let y ←$ᵖ ↥curve}[
            WeightedAgreement.agree_set (μ := μ) y.1 (ReedSolomonCode.finCarrier domain deg) ≥ α]) := by
      have : (Nat.succ k : ENNReal) * (errorBound δ deg domain : ENNReal) ≤ prAgree :=
        le_of_lt hproximity
      simpa [prAgree, curve] using this

    exact le_trans h_bound' h_threshold_le

  -- Rate / Johnson regime gives the gap condition sqrtRate < α and α < 1
  have hsqrt_lt : ReedSolomonCode.sqrtRate deg domain < α := by
    have hδ_lt : δ < 1 - ReedSolomonCode.sqrtRate deg domain := hδJ.2
    have hsqrt_add : ReedSolomonCode.sqrtRate deg domain + δ < (1 : ℝ≥0) :=
      (lt_tsub_iff_left).1 (by simpa using hδ_lt)
    apply (lt_tsub_iff_left).2
    simpa [α, add_comm, add_left_comm, add_assoc] using hsqrt_add

  have hα_lt_one : α < 1 := by
    have hδ_pos : 0 < δ := lt_of_le_of_lt (zero_le _) hδJ.1
    simpa [α] using
      (tsub_lt_self (a := (1 : ℝ≥0)) (b := δ)
        (by simpa using (show (0 : ℝ≥0) < (1 : ℝ≥0) from zero_lt_one)) hδ_pos)

  have h_weighted :
      ∃ ι' : Finset ι, ∃ v : Fin (k + 2) → ι → F,
        (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        WeightedAgreement.mu_set (μ := μ) ι' ≥ α ∧
        ∀ i, ∀ x ∈ ι', U i x = v i x := by
    simpa [Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using
      (WeightedAgreement.weighted_correlated_agreement_for_parameterized_curves
        (ι := ι) (F := F) (l := k) (k := k) (u := U) (deg := deg) (domain := domain) (δ := δ)
        (μ := μ) (M := M) (α := α) hμ
        hsqrt_lt hα_lt_one
        (hproximity := hproximity')
        (h_additionally := h_additionally'))

  rcases h_weighted with ⟨S, v, hvC, hμS, hEq⟩
  refine ⟨S, ?_, ?_⟩
  · have hμ_uniform :
        WeightedAgreement.mu_set (μ := μ) S = (S.card : ℝ) / (Fintype.card ι : ℝ) := by
      simpa [μ] using (ca_mu_set_uniform (ι := ι) S)

    have hα_le_div : (α : ℝ) ≤ (S.card : ℝ) / (Fintype.card ι : ℝ) := by
      have : (α : ℝ) ≤ WeightedAgreement.mu_set (μ := μ) S := by
        simpa [ge_iff_le] using hμS
      simpa [hμ_uniform] using this

    have hn_pos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos (α := ι))

    have hcard_ge : (α : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (le_div_iff₀ hn_pos).1 hα_le_div

    exact_mod_cast hcard_ge

  · refine ⟨v, ?_⟩
    intro i
    constructor
    · exact hvC i
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hEq i x hx).symm


theorem correlatedAgreement_affine_curves_listDecodingRegime [DecidableEq ι] {k : ℕ}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδJ : δ ∈ Set.Ioo
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
    (1 - ReedSolomonCode.sqrtRate deg domain))
  : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  cases k with
  | zero =>
      simpa using
        (correlatedAgreement_affine_curves_listDecodingRegime_k0 (deg := deg) (domain := domain) (δ := δ)
          (ι := ι) (F := F))
  | succ k' =>
      simpa using
        (correlatedAgreement_affine_curves_listDecodingRegime_succ (k := k') (deg := deg) (domain := domain)
          (δ := δ) (ι := ι) (F := F) hδJ)

theorem errorBound_eq_div_card_of_mem_Icc {ι : Type} [Fintype ι] [Nonempty ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0)
  (hδUD : δ ∈ Set.Icc (0 : ℝ≥0)
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)) :
  errorBound δ deg domain = (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  simp [ProximityGap.errorBound, hδUD]

theorem polynomialCurveFinite_card_le_field {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} (u : Fin k → ι → F) :
  (Curve.polynomialCurveFinite (F := F) (A := F) u).card ≤ Fintype.card F := by
  classical
  -- define the parameterization map
  let f : F → (ι → F) := fun r => ∑ i : Fin k, (r ^ (i : ℕ)) • u i
  have hs : Curve.polynomialCurveFinite (F := F) (A := F) u = Finset.univ.image f := by
    ext v
    -- unfold the definitions of membership
    -- note: `polynomialCurveFinite` is defined by set-builder on a finite type
    simp [Curve.polynomialCurveFinite, f, eq_comm]
  -- now use card_image_le
  calc
    (Curve.polynomialCurveFinite (F := F) (A := F) u).card
        = (Finset.univ.image f).card := by simpa [hs]
    _ ≤ (Finset.univ : Finset F).card := Finset.card_image_le
    _ = Fintype.card F := by simpa

noncomputable def polynomialCurveFinite_param
  {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} (u : WordStack F (Fin (k + 1)) ι) :
  {y // y ∈ Curve.polynomialCurveFinite (F := F) (A := F) u} → F :=
fun y =>
  Classical.choose (
    (show ∃ r : F, y.1 = ∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i from by
      classical
      have hy : y.1 ∈ Curve.polynomialCurveFinite (F := F) (A := F) u := y.property
      -- unfold to expose the filter form
      dsimp [Curve.polynomialCurveFinite] at hy
      -- membership in a filtered univ gives the predicate
      exact (Finset.mem_filter.mp hy).2
    )
  )

theorem polynomialCurveFinite_param_spec {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} (u : WordStack F (Fin (k + 1)) ι)
  (y : {y // y ∈ Curve.polynomialCurveFinite (F := F) (A := F) u}) :
  y.1 = ∑ i : Fin (k + 1), (polynomialCurveFinite_param (u := u) y) ^ (i : ℕ) • u i := by
  classical
  -- Unfold the definition and use `Classical.choose_spec` for the witness packed into `polynomialCurveFinite_param`.
  simpa [polynomialCurveFinite_param] using
    (Classical.choose_spec
      (show ∃ r : F, y.1 = ∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i from by
        classical
        have hy : y.1 ∈ Curve.polynomialCurveFinite (F := F) (A := F) u := y.property
        dsimp [Curve.polynomialCurveFinite] at hy
        exact (Finset.mem_filter.mp hy).2))

theorem polynomialCurveFinite_param_injective {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} (u : WordStack F (Fin (k + 1)) ι) :
  Function.Injective (polynomialCurveFinite_param (u := u)) := by
  classical
  intro y₁ y₂ h
  apply Subtype.ext
  -- show equality of the underlying points
  calc
    y₁.1
        = ∑ i : Fin (k + 1),
            (polynomialCurveFinite_param (u := u) y₁) ^ (i : ℕ) • u i := by
          simpa using (polynomialCurveFinite_param_spec (u := u) y₁)
    _ = ∑ i : Fin (k + 1),
            (polynomialCurveFinite_param (u := u) y₂) ^ (i : ℕ) • u i := by
          simpa [h]
    _ = y₂.1 := by
          simpa using (polynomialCurveFinite_param_spec (u := u) y₂).symm

theorem RS_correlatedAgreement_affineCurves_uniqueDecodingRegime_weighted {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδUD : δ ∈ Set.Icc (0 : ℝ≥0)
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2))
  (u : WordStack F (Fin (k + 1)) ι)
  (hPr :
    Pr_{let y ←$ᵖ ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)}[
      WeightedAgreement.agree_set (μ := ca_uniformMu (ι := ι)) y.1
        (ReedSolomonCode.finCarrier domain deg) ≥ (1 - δ : ℝ≥0)]
    > (k : ENNReal) * ((Fintype.card ι : ENNReal) / (Fintype.card F : ENNReal)))
  :
  ∃ S : Finset ι, ∃ v : Fin (k + 1) → ι → F,
    (∀ i, v i ∈ (ReedSolomon.code domain deg : Set (ι → F))) ∧
    (WeightedAgreement.mu_set (μ := ca_uniformMu (ι := ι)) S ≥ (1 - δ : ℝ≥0)) ∧
    (∀ i x, x ∈ S → u i x = v i x) := by
  -- Key clarification (fixing earlier doubt): the sampling model here is **uniform over the curve as a Finset of distinct points** `Curve.polynomialCurveFinite u`, which matches the statement of BCIKS20 Thm 1.5 as it is commonly presented (Pr over `curve(u)`). So we should not try to rewrite the goal into parameter-sampling `z ←$ F` nor assume `curve.card = |F|`.
  -- 
  -- Target shape:
  -- - Hypothesis: `Pr_{y←uniform curve}[agree_set y ≥ 1-δ] > k * (|ι|/|F|)`.
  -- - Conclusion: ∃ large coordinate set `S` (μ_set ≥ 1-δ) and codewords `v i ∈ RS` with `u i = v i` on `S`.
  -- 
  -- High-level proof skeleton (BCIKS20 §6.1 / Thm 6.1 style):
  -- 
  -- 0) **Case split on `k`**:
  -- - `k = 0`: curve is a singleton `{u 0}`. From `Pr > 0` get `agree_set u0 ≥ 1-δ`, pick `v0 ∈ RS.finCarrier` witnessing the max, set `S := {x | u0 x = v0 x}`; convert agreement to `S.card ≥ (1-δ)*|ι|` using `ca_agree_uniform_eq_card_div`; finish with `ca_mu_set_uniform`. For `i : Fin 1` the equality `u i = v i` is just `i=0`.
  -- - `k = succ k'`: proceed with main argument below.
  -- 
  -- 1) **Probability → many good curve points**:
  -- Let `curve := Curve.polynomialCurveFinite u` and `Good (y : ↥curve) : Prop := agree_set y.1 ≥ 1-δ`.
  -- Use the standard uniform-probability formula on finite spaces (`prob_uniform_eq_card_filter_div_card` / `ProbabilityTheory.prob_eq_count_div_card` depending on the ArkLib instance) to rewrite `hPr` into a strict lower bound on `goodPts.card` where `goodPts := Finset.univ.filter Good`.
  -- 
  -- Crucial counting step (avoids any injectivity assumption): show `goodPts.card > Fintype.card ι`.
  -- - From `hPr` you get `goodPts.card > (k * |ι| / |F|) * curve.card`.
  -- - Prove the general lower bound `|F| ≤ k * curve.card` for `k>0` (equivalently `curve.card ≥ |F|/k`).
  --   Idea: consider the map `evalCurve : F → (ι → F), z ↦ ∑ i, z^i • u i`; `curve` is its image.
  --   Show each fiber has size ≤ k (use a coordinate `x` where the coefficient of the highest nonzero `z`-power is nonzero; then the scalar polynomial equation has ≤ k solutions by `Polynomial.card_roots` / root-count lemma). Handle the degenerate “constant map” case separately (then `curve.card = 1` but the hypothesis is strong enough / or forces higher coefficients 0 when `|F|>k`).
  -- - Combining gives `goodPts.card > |ι|`.
  -- 
  -- 2) **Choose parameters for good points (optional convenience)**:
  -- Use `polynomialCurveFinite_param` and its injectivity to obtain a Finset `ZGood : Finset F` of distinct parameters corresponding to good curve points, with `ZGood.card = goodPts.card` and thus `ZGood.card > |ι|`.
  -- This gives a large set of distinct `z` values to run the polynomial-in-`Z` arguments.
  -- 
  -- 3) **Decode each good point to a unique RS codeword**:
  -- For each good curve point `y` (or `z ∈ ZGood`), unfold `WeightedAgreement.agree_set` to obtain a witness codeword `c_z ∈ ReedSolomonCode.finCarrier domain deg` such that
  -- `WeightedAgreement.agree (μ := ca_uniformMu) (curvePoint z) c_z ≥ 1-δ`.
  -- Convert to a Hamming-distance / relative-distance bound using `ca_agree_uniform_eq_card_div`:
  -- - agreement lower bound ⇒ `{x | curvePoint z x = c_z x}` has card ≥ `(1-δ)*|ι|` ⇒ mismatches ≤ `δ*|ι|` ⇒ `δᵣ(curvePoint z, RS.code) ≤ δ`.
  -- Then use `hδUD : δ ≤ (1-ρ)/2` (unique-decoding radius) to get **uniqueness** of the decoded RS codeword within that radius; this ensures the choice `c_z` is canonical.
  -- 
  -- 4) **Glue the decoded codewords into one polynomial curve of RS codewords**:
  -- This is the core §6.1 step.
  -- - Represent each decoded codeword `c_z` as evaluation of a polynomial `p_z : F[X]` with `natDegree < deg` (use `ReedSolomon.codewordToPoly` / interpolation lemmas).
  -- - Show there exists a bivariate polynomial `P : F[X][Z]` with `deg_X < deg` and `deg_Z ≤ k` such that for all `z ∈ ZGood`, the restriction `P(·,z)` equals `p_z`.
  --   Expected tools:
  --   - `BerlekampWelch.decoder_eq_some` for existence/correctness of `p_z` from distance ≤ δ.
  --   - `PolishchukSpielman.polishchuk_spielman` (or auxiliary lemmas in `ArkLib.Data.CodingTheory.PolishchukSpielman`) to conclude global divisibility / interpolation from agreement on many `z`.
  -- - Expand `P` in `Z`: `P(X,Z) = ∑_{i=0}^k V_i(X) * Z^i`.
  --   Define `v i : ι → F := fun x => (V_i.eval (domain x))`.
  --   Prove `v i ∈ ReedSolomon.code domain deg` from the `deg_X` bound.
  -- 
  -- 5) **Root counting / double counting to get a large coordinate set `S`**:
  -- For each `x : ι`, consider the univariate polynomial
  -- `Q_x(Z) := (∑ i, Z^i • u i x) - (∑ i, Z^i • v i x)` of degree ≤ k.
  -- For each good `z`, from the decoding correctness we have that the curve point at `z` agrees with `∑ i, z^i • v i` on at least `(1-δ)` fraction of coordinates. Double count pairs `(x,z)` to show there is a set `S ⊆ ι` with `S.card ≥ (1-δ)*|ι|` such that for each `x ∈ S`, the polynomial `Q_x` has more than `k` roots (coming from many `z ∈ ZGood`), hence `Q_x = 0` identically, hence `u i x = v i x` for all i.
  -- Finally translate `S.card ≥ (1-δ)*|ι|` to `mu_set S ≥ 1-δ` using `ca_mu_set_uniform`.
  -- 
  -- Proof engineering notes:
  -- - Prefer `simp only [...]` over `simp`.
  -- - Keep coercions explicit between `ℝ≥0`, `ℝ`, `ENNReal`.
  -- - Use `ca_agree_uniform_eq_card_div` and `ca_mu_set_uniform` as the main bridges between weighted objects and cardinalities.
  sorry

theorem RS_correlatedAgreement_affineCurves_uniqueDecodingRegime {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδUD : δ ∈ Set.Icc (0 : ℝ≥0)
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2))
  : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) := by
  classical
  unfold δ_ε_correlatedAgreementCurves
  intro u hPr_close
  -- Define the two predicates
  let p : (↥(Curve.polynomialCurveFinite (F := F) (A := F) u)) → Prop :=
    fun y => δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (δ : ENNReal)
  let q : (↥(Curve.polynomialCurveFinite (F := F) (A := F) u)) → Prop :=
    fun y =>
      WeightedAgreement.agree_set (μ := ca_uniformMu (ι := ι)) y.1
        (ReedSolomonCode.finCarrier domain deg) ≥ (1 - δ : ℝ≥0)
  have hpq : ∀ y, p y → q y := by
    intro y hy
    -- apply agreement lemma pointwise
    exact ca_agree_set_ge_of_relDistFromCode_le (ι := ι) (F := F) (deg := deg)
      (domain := domain) (δ := δ) (w := y.1) hy
  have hPr_mono :
      Pr_{let y ←$ᵖ ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)}[p y]
        ≤
      Pr_{let y ←$ᵖ ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)}[q y] :=
    ca_Pr_uniform_mono (α := ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)) p q hpq
  have hPr_agree :
      Pr_{let y ←$ᵖ ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)}[q y]
        > (k : ENNReal) * ((Fintype.card ι : ENNReal) / (Fintype.card F : ENNReal)) := by
    -- derive from hPr_close using monotonicity
    have hPr_close' :
        (k : ENNReal) * ((Fintype.card ι : ENNReal) / (Fintype.card F : ENNReal))
          < Pr_{let y ←$ᵖ ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)}[p y] := by
      -- hPr_close is already this statement up to rewriting
      simpa [p, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hPr_close
    -- now use lt_of_lt_of_le
    exact (lt_of_lt_of_le hPr_close' hPr_mono)
  -- Apply the weighted correlated agreement theorem
  rcases
      RS_correlatedAgreement_affineCurves_uniqueDecodingRegime_weighted (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := domain) (δ := δ) hδUD u hPr_agree
    with ⟨S, v, hv_code, hmuS, huv⟩
  -- Package the result into jointAgreement
  refine ⟨S, ?_, ?_⟩
  · -- Convert the weighted measure bound into a cardinality bound
    -- First rewrite `mu_set` using the uniform lemma
    have hmuS' :
        ((S.card : ℝ) / (Fintype.card ι : ℝ)) ≥ ((1 - δ : ℝ≥0) : ℝ) := by
      -- rewrite mu_set
      simpa [ca_mu_set_uniform (ι := ι) S] using hmuS
    -- Multiply through by card ι
    have hcardι_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos (α := ι))
    have hcard_le :
        ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      -- from hmuS'
      have := (le_div_iff₀ hcardι_pos).1 hmuS'
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    -- cast back to ℝ≥0
    have hcard_le_nnreal :
        (1 - δ : ℝ≥0) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      -- use norm_cast / exact_mod_cast
      exact_mod_cast hcard_le
    -- goal has reversed inequality
    simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using hcard_le_nnreal
  · refine ⟨v, ?_⟩
    intro i
    refine ⟨hv_code i, ?_⟩
    -- show agreement on S
    intro x hx
    -- membership in filter
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- use huv
    exact (huv i x hx).symm

theorem correlatedAgreement_affine_curves_uniqueDecodingRegime_core {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [DecidableEq ι]
  {k : ℕ} {u : WordStack F (Fin (k + 1)) ι}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδUD : δ ∈ Set.Icc (0 : ℝ≥0)
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2))
  (hPr :
    (Pr_{let y ←$ᵖ ↥(Curve.polynomialCurveFinite (F := F) (A := F) u)}[
        δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (δ : ENNReal)]
      )
      > (k : ℝ≥0) * ((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0))) :
  jointAgreement (F := F) (κ := Fin (k + 1)) (ι := ι)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) (W := u) (δ := δ) := by
  classical
  -- We proceed by applying a (missing) correlated-agreement theorem for RS over polynomial curves.
  have hCA :
      δ_ε_correlatedAgreementCurves (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (k := k)
        (δ := δ) (ε := (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) :=
    RS_correlatedAgreement_affineCurves_uniqueDecodingRegime (ι := ι) (F := F)
      (k := k) (deg := deg) (domain := domain) (δ := δ) hδUD
  -- unfold the definition and apply to the specific curve/wordstack `u`
  exact hCA u (by
    -- `hPr` already matches the required bound
    simpa [mul_assoc] using hPr)


theorem correlatedAgreement_affine_curves_uniqueDecodingRegime [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδUD : δ ∈ Set.Icc (0 : ℝ≥0)
    (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2))
  : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  -- unfold the wrapper definition
  unfold δ_ε_correlatedAgreementCurves
  intro u hPr
  -- rewrite the error bound using the unique-decoding-regime hypothesis
  have hPr' := (by
    simpa [errorBound_eq_div_card_of_mem_Icc (deg := deg) (domain := domain) (δ := δ) hδUD] using hPr
    )
  -- apply the core unique-decoding lemma
  exact
    correlatedAgreement_affine_curves_uniqueDecodingRegime_core (ι := ι) (F := F)
      (k := k) (u := u) (deg := deg) (domain := domain) (δ := δ) (hδUD := hδUD) hPr'

theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ < 1 - ReedSolomonCode.sqrtRate deg domain)
  : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  by_cases hUD :
      δ ∈
        Set.Icc (0 : ℝ≥0)
          (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
  ·
    exact
      correlatedAgreement_affine_curves_uniqueDecodingRegime (ι := ι) (F := F) (k := k) (u := u)
        (deg := deg) (domain := domain) (δ := δ) hUD
  ·
    have hnotle :
        ¬ δ ≤
            (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2) := by
      intro hle
      apply hUD
      refine ⟨zero_le δ, hle⟩
    have hlower :
        (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2) < δ := by
      exact lt_of_not_ge hnotle
    have hJ :
        δ ∈
          Set.Ioo
            (((1 : ℝ≥0) - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
            (1 - ReedSolomonCode.sqrtRate deg domain) := by
      exact ⟨hlower, hδ⟩
    exact
      correlatedAgreement_affine_curves_listDecodingRegime (ι := ι) (F := F) (k := k) (deg := deg)
        (domain := domain) (δ := δ) hJ


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

end BCIKS20ProximityGapSection6

end ProximityGap
