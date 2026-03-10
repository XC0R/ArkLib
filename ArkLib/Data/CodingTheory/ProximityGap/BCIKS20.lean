/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

import Mathlib.Algebra.Module.Submodule.Union
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
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hm : 1 ≤ m) :
  ∃ Q, Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs f Q :=
  GuruswamiSudan.proximity_gap_existence (k + 1) n ωs f hm

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
  (hk : k + 2 ≤ n) (hm : 1 ≤ m)
  (cond : Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs w Q)
  {p : ReedSolomon.code ωs (k + 1)}
  (h : (↑Δ₀(w, fun i ↦ Polynomial.eval (ωs i) (ReedSolomon.codewordToPoly p)) : ℝ) / ↑n <
       _root_.proximity_gap_johnson (k + 1) n m)
  :
  (Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q :=
  GuruswamiSudan.proximity_gap_divisibility hk hm p cond h


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

theorem Pr_uniform_bind_comm {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
  (P : α → β → Prop) :
  Pr_{let a ←$ᵖ α; let b ←$ᵖ β}[P a b] = Pr_{let b ←$ᵖ β; let a ←$ᵖ α}[P a b] := by
  classical
  -- Expand the `Pr_{...}[...]` notation and use commutativity of `PMF.bind`.
  simpa [Bind.bind, Pure.pure] using
    congrArg (fun r : PMF Prop => (r True : ENNReal))
      (PMF.bind_comm ($ᵖ α) ($ᵖ β) (fun a b => PMF.pure (P a b)))


theorem Pr_uniform_congr_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
  (e : α ≃ β) (P : β → Prop) :
  Pr_{let y ←$ᵖ β}[P y] = Pr_{let x ←$ᵖ α}[P (e x)] := by
  classical
  simp [ProbabilityTheory.prStx]

  have hβ : (P <$> ($ᵖ β)) True = ($ᵖ β).toOuterMeasure ({y : β | P y} : Set β) := by
    calc
      (P <$> ($ᵖ β)) True
          = (P <$> ($ᵖ β)).toOuterMeasure ({True} : Set Prop) := by
              simpa using (PMF.toOuterMeasure_apply_singleton (p := (P <$> ($ᵖ β))) True).symm
      _   = (($ᵖ β).map P).toOuterMeasure ({True} : Set Prop) := by
              simpa [PMF.monad_map_eq_map]
      _   = ($ᵖ β).toOuterMeasure (P ⁻¹' ({True} : Set Prop)) := by
              simpa using
                (PMF.toOuterMeasure_map_apply (p := ($ᵖ β)) (f := P) (s := ({True} : Set Prop)))
      _   = ($ᵖ β).toOuterMeasure ({y : β | P y} : Set β) := by
              have hpre : (P ⁻¹' ({True} : Set Prop)) = ({y : β | P y} : Set β) := by
                ext y
                by_cases hy : P y <;>
                  simp [Set.mem_preimage, Set.mem_singleton_iff, hy]
              simpa [hpre]

  have hα : ((fun a : α => P (e a)) <$> ($ᵖ α)) True = ($ᵖ α).toOuterMeasure ({x : α | P (e x)} : Set α) := by
    calc
      ((fun a : α => P (e a)) <$> ($ᵖ α)) True
          = ((fun a : α => P (e a)) <$> ($ᵖ α)).toOuterMeasure ({True} : Set Prop) := by
              simpa using
                (PMF.toOuterMeasure_apply_singleton
                  (p := ((fun a : α => P (e a)) <$> ($ᵖ α))) True).symm
      _   = (($ᵖ α).map (fun a : α => P (e a))).toOuterMeasure ({True} : Set Prop) := by
              simpa [PMF.monad_map_eq_map]
      _   = ($ᵖ α).toOuterMeasure ((fun a : α => P (e a)) ⁻¹' ({True} : Set Prop)) := by
              simpa using
                (PMF.toOuterMeasure_map_apply (p := ($ᵖ α)) (f := (fun a : α => P (e a)))
                  (s := ({True} : Set Prop)))
      _   = ($ᵖ α).toOuterMeasure ({x : α | P (e x)} : Set α) := by
              have hpre : ((fun a : α => P (e a)) ⁻¹' ({True} : Set Prop)) = ({x : α | P (e x)} : Set α) := by
                ext x
                by_cases hx : P (e x) <;>
                  simp [Set.mem_preimage, Set.mem_singleton_iff, hx]
              simpa [hpre]

  rw [hβ, hα]

  haveI : Fintype ({y : β | P y} : Set β) := Fintype.ofFinite _
  haveI : Fintype ({x : α | P (e x)} : Set α) := Fintype.ofFinite _

  rw [PMF.toOuterMeasure_uniformOfFintype_apply (α := β) (s := ({y : β | P y} : Set β))]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply (α := α) (s := ({x : α | P (e x)} : Set α))]

  have hden : Fintype.card α = Fintype.card β := Fintype.card_congr e

  let esub : ({x : α | P (e x)} : Set α) ≃ ({y : β | P y} : Set β) :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y =>
        ⟨e.symm y.1, by
          have hy : P y.1 := y.2
          simpa using hy⟩
      left_inv := by
        intro x
        ext
        simp
      right_inv := by
        intro y
        ext
        simp }

  have hnum : Fintype.card ({x : α | P (e x)} : Set α) = Fintype.card ({y : β | P y} : Set β) :=
    Fintype.card_congr esub

  rw [hnum, hden]


theorem Pr_uniform_translate_affineSubspace {ι F : Type} [Fintype ι] [Nonempty ι]
  [Field F]
  {U : AffineSubspace F (ι → F)} [Fintype U] [Nonempty U]
  (v : ι → F) (hv : v ∈ U.direction) (P : (ι → F) → Prop) :
  Pr_{let x ←$ᵖ U}[P (v + x.1)] = Pr_{let x ←$ᵖ U}[P x.1] := by
  classical
  let Q : U → Prop := fun x => P x.1
  let τ : U ≃ U :=
    { toFun := fun x =>
        ⟨v + x.1, by
          -- show v + x.1 ∈ U
          simpa [vadd_eq_add] using (U.vadd_mem_of_mem_direction hv x.2)⟩
      invFun := fun x =>
        ⟨(-v) + x.1, by
          have hv' : (-v) ∈ U.direction := by
            simpa using (U.direction.neg_mem hv)
          simpa [vadd_eq_add] using (U.vadd_mem_of_mem_direction hv' x.2)⟩
      left_inv := by
        intro x
        ext i
        simp [add_assoc]
      right_inv := by
        intro x
        ext i
        simp [add_assoc] }
  -- apply invariance of uniform measure under equivalence
  simpa [Q, τ] using (Pr_uniform_congr_equiv τ Q).symm

theorem agree_ge_mu_set_of_eq_on [DecidableEq ι] [Fintype ι] [DecidableEq F]
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {u v : ι → F} {ι' : Finset ι} :
  (∀ x ∈ ι', u x = v x) →
    agree μ u v ≥ mu_set μ ι' := by
  intro hEq
  unfold agree mu_set
  rw [ge_iff_le]
  classical
  let s : Finset ι := Finset.univ.filter (fun i => u i = v i)
  have hs : ι' ⊆ s := by
    intro x hx
    have hx' : u x = v x := hEq x hx
    -- membership in filter
    simpa [s, hx', hx]
  have hsum : (∑ i ∈ ι', (μ i).1) ≤ ∑ i ∈ s, (μ i).1 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hs ?_
    intro i hi hi_not
    exact (μ i).2.1
  have hsum' : (↑(∑ i ∈ ι', (μ i).1) : ℝ) ≤ (↑(∑ i ∈ s, (μ i).1) : ℝ) := by
    exact_mod_cast hsum
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hfactor : 0 ≤ (1 / (Fintype.card ι : ℝ)) := by
    exact le_of_lt (one_div_pos.mpr hcardpos)
  have hmul : (1 / (Fintype.card ι : ℝ)) * (↑(∑ i ∈ ι', (μ i).1) : ℝ)
      ≤ (1 / (Fintype.card ι : ℝ)) * (↑(∑ i ∈ s, (μ i).1) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hsum' hfactor
  -- rewrite RHS sum
  have hsumR : (∑ i with u i = v i, (μ i).1) = ∑ i ∈ s, (μ i).1 := by
    simp [s]
  -- finish
  simpa [hsumR, s] using hmul

theorem exists_good_parallel_affine_line [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0}
  (w' : ι → F)
  (hw' : w' ∈ (affineSpan F (Finset.univ.image (Fin.tail u)).toSet).direction) :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
  letI ε := ProximityGap.errorBound α deg domain
  letI bound : ENNReal :=
    ENNReal.ofReal (
      ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
      * (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
    )
  letI U := (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
  letI pr := Pr_{let x ←$ᵖ U}[agree_set μ x (finCarrier domain deg) ≥ α]
  pr > ε → pr ≥ bound →
  ∃ base : ι → F,
    base ∈ U ∧
    let prLine :=
      Pr_{let z ←$ᵖ F}[agree_set μ (base + z • w') (finCarrier domain deg) ≥ α]
    prLine > ε ∧ prLine ≥ bound := by
  classical
  intro _hα _hα₁ _hμ hpr_gt hpr_ge
  let A : AffineSubspace F (ι → F) :=
    affineSpan F (Finset.univ.image (Fin.tail u)).toSet
  let U : AffineSubspace F (ι → F) := u 0 +ᵥ A
  let sqrtRate : ℝ≥0 := ReedSolomonCode.sqrtRate deg domain
  let ε : ℝ≥0 := ProximityGap.errorBound α deg domain
  let bound : ENNReal :=
    ENNReal.ofReal
      (((M * Fintype.card ι + 1 : ℕ) : ℝ) / (Fintype.card F : ℝ) *
        (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate))
  let pr : ENNReal :=
    Pr_{let x ←$ᵖ U}[agree_set μ x (finCarrier domain deg) ≥ α]

  have hpr_gt' : pr > (ε : ENNReal) := by
    simpa [pr, ε, U, A, sqrtRate] using hpr_gt
  have hpr_ge' : pr ≥ bound := by
    simpa [pr, bound, U, A, sqrtRate] using hpr_ge

  let P : (ι → F) → Prop := fun x => agree_set μ x (finCarrier domain deg) ≥ (α : ℝ)
  let f : U → ENNReal := fun b => Pr_{let z ←$ᵖ F}[P (b.1 + z • w')]

  obtain ⟨b0, hb0⟩ := Finite.exists_max f

  let J : ENNReal := Pr_{let x ←$ᵖ U; let z ←$ᵖ F}[P (x.1 + z • w')]

  have hwU : w' ∈ U.direction := by
    simpa [U, A, AffineSubspace.pointwise_vadd_direction] using hw'

  have htranslate : ∀ z : F, Pr_{let x ←$ᵖ U}[P (x.1 + z • w')] = pr := by
    intro z
    have hzU : z • w' ∈ U.direction := by
      simpa using (U.direction.smul_mem z hwU)
    have h :=
      Pr_uniform_translate_affineSubspace (U := U) (v := z • w') (hv := hzU) (P := P)
    simpa [pr, P, add_comm, add_left_comm, add_assoc] using h

  have hinner : ∀ z : F,
      (($ᵖ (↥U)).bind fun x : (↥U) => PMF.pure (P (↑x + z • w'))) True = pr := by
    intro z
    simpa [Bind.bind, Pure.pure] using htranslate z

  -- Step 1: `J = pr`
  have hJ_eq : J = pr := by
    have hcomm : J = Pr_{let z ←$ᵖ F; let x ←$ᵖ U}[P (x.1 + z • w')] := by
      dsimp [J]
      simpa using
        (Pr_uniform_bind_comm (α := U) (β := F) (P := fun x z => P (x.1 + z • w')))
    rw [hcomm]
    simp only [Bind.bind, Pure.pure]
    rw [PMF.bind_apply]
    -- rewrite inner probability
    have hrewrite :
        (∑' z : F,
            ($ᵖ F) z * (($ᵖ (↥U)).bind fun x : (↥U) => PMF.pure (P (↑x + z • w'))) True) =
          ∑' z : F, ($ᵖ F) z * pr := by
      refine tsum_congr ?_
      intro z
      simp [hinner z]
    -- use the rewrite
    -- (use `convert` to avoid binder-name issues)
    have :
        (∑' z : F,
            ($ᵖ F) z * (($ᵖ (↥U)).bind fun x : (↥U) => PMF.pure (P (↑x + z • w'))) True) =
          pr := by
      -- start from the rewritten expression
      -- and evaluate the constant average
      calc
        (∑' z : F,
              ($ᵖ F) z * (($ᵖ (↥U)).bind fun x : (↥U) => PMF.pure (P (↑x + z • w'))) True)
            = ∑' z : F, ($ᵖ F) z * pr := hrewrite
        _ = (∑' z : F, ($ᵖ F) z) * pr := by
              simpa using (ENNReal.tsum_mul_right :
                (∑' z : F, ($ᵖ F) z * pr) = (∑' z : F, ($ᵖ F) z) * pr)
        _ = 1 * pr := by
              -- `∑' z, ($ᵖ F) z = 1`
              rw [PMF.tsum_coe ($ᵖ F)]
        _ = pr := by simp
    -- finish
    exact this

  -- Step 2: `J ≤ f b0`
  have hJ_le : J ≤ f b0 := by
    dsimp [J]
    simp only [Bind.bind, Pure.pure]
    rw [PMF.bind_apply]
    have hx : ∀ x : (↥U),
        (($ᵖ F).bind fun z : F => PMF.pure (P (↑x + z • w'))) True = f x := by
      intro x
      rfl
    have hpoint : ∀ x : (↥U), ($ᵖ (↥U)) x * f x ≤ ($ᵖ (↥U)) x * f b0 := by
      intro x
      exact mul_le_mul_left' (hb0 x) _
    have htsum : (∑' x : (↥U), ($ᵖ (↥U)) x * f x) ≤ (∑' x : (↥U), ($ᵖ (↥U)) x * f b0) :=
      ENNReal.tsum_le_tsum hpoint
    have htsum' :
        (∑' x : (↥U), ($ᵖ (↥U)) x *
              (($ᵖ F).bind fun z : F => PMF.pure (P (↑x + z • w'))) True) ≤
          (∑' x : (↥U), ($ᵖ (↥U)) x * f b0) := by
      simpa [hx] using htsum
    calc
      (∑' x : (↥U), ($ᵖ (↥U)) x *
            (($ᵖ F).bind fun z : F => PMF.pure (P (↑x + z • w'))) True) ≤
          (∑' x : (↥U), ($ᵖ (↥U)) x * f b0) := htsum'
      _ = (∑' x : (↥U), ($ᵖ (↥U)) x) * f b0 :=
            (ENNReal.tsum_mul_right :
              (∑' x : (↥U), ($ᵖ (↥U)) x * f b0) = (∑' x : (↥U), ($ᵖ (↥U)) x) * f b0)
      _ = 1 * f b0 := by
            have hsum : (∑' x : (↥U), ($ᵖ (↥U)) x) = (1 : ENNReal) := PMF.tsum_coe ($ᵖ (↥U))
            -- rewrite then close
            rw [hsum]
      _ = f b0 := by simp

  have hpr_le_fb0 : pr ≤ f b0 := by
    simpa [hJ_eq] using hJ_le

  refine ⟨b0.1, b0.2, ?_⟩
  dsimp
  constructor
  · exact lt_of_lt_of_le hpr_gt' hpr_le_fb0
  ·
    have hbound_le_pr :
        ENNReal.ofReal
            ((↑M * ↑(Fintype.card ι) + 1) / ↑(Fintype.card F) *
              (1 / ↑(min (α - ReedSolomonCode.sqrtRate deg domain)
                      (ReedSolomonCode.sqrtRate deg domain / 20)) +
                3 / ↑(ReedSolomonCode.sqrtRate deg domain))) ≤
          pr := by
      simpa [pr, U, A] using hpr_ge
    exact le_trans hbound_le_pr hpr_le_fb0


theorem mem_polynomialCurveFinite_fin2_iff [DecidableEq ι] [Fintype ι] [DecidableEq F]
  {base dir : ι → F} (w : ι → F) :
  let uLine : Fin 2 → ι → F := fun i => if i = 0 then base else dir
  let curve := Curve.polynomialCurveFinite (F := F) (A := F) uLine
  w ∈ curve ↔ ∃ z : F, w = base + z • dir := by
  classical
  -- attempt to unfold and simp
  simp [Curve.polynomialCurveFinite, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc]

theorem exists_equiv_polynomialCurveFinite_fin2_of_ne_zero [DecidableEq ι] [Fintype ι] [DecidableEq F]
  {base dir : ι → F} (hdir : dir ≠ 0) :
  let uLine : Fin 2 → ι → F := fun i => if i = 0 then base else dir
  let curve := Curve.polynomialCurveFinite (F := F) (A := F) uLine
  ∃ e : F ≃ curve, ∀ z : F, ((e z : curve) : ι → F) = base + z • dir := by
  classical
  -- Unfold the `let`-bindings in the statement
  dsimp
  -- Name the curve set for readability
  let curve : Set (ι → F) :=
    Curve.polynomialCurveFinite (F := F) (A := F) (fun i : Fin 2 => if i = 0 then base else dir)

  -- Parametrization map
  let g : F → curve := fun z =>
    ⟨base + z • dir,
      by
        -- show `base + z • dir` lies on the curve
        have hz :
            base + z • dir ∈
              Curve.polynomialCurveFinite (F := F) (A := F)
                (fun i : Fin 2 => if i = 0 then base else dir) := by
          simpa using
            ((mem_polynomialCurveFinite_fin2_iff (F := F) (ι := ι) (base := base) (dir := dir)
                  (w := base + z • dir)).2
              ⟨z, rfl⟩)
        simpa [curve] using hz⟩

  have hg_inj : Function.Injective g := by
    intro z1 z2 h
    have hval : base + z1 • dir = base + z2 • dir := by
      simpa [g] using congrArg Subtype.val h
    have hsmul : z1 • dir = z2 • dir := add_left_cancel hval

    have hidx : ∃ i : ι, dir i ≠ 0 := by
      by_contra hnone
      have hzero : dir = 0 := by
        funext i
        by_contra hi
        apply hnone
        exact ⟨i, hi⟩
      exact hdir hzero

    rcases hidx with ⟨i, hi⟩
    have hmul : z1 * dir i = z2 * dir i := by
      have := congrArg (fun f : ι → F => f i) hsmul
      simpa using this

    have hmul' := congrArg (fun t : F => t * (dir i)⁻¹) hmul
    -- cancel the nonzero factor `dir i`
    simpa [mul_assoc, hi] using hmul'

  have hg_surj : Function.Surjective g := by
    intro w
    have hwmem :
        (w : ι → F) ∈
          Curve.polynomialCurveFinite (F := F) (A := F)
            (fun i : Fin 2 => if i = 0 then base else dir) := by
      simpa [curve] using w.property

    have hiff :
        (w : ι → F) ∈
            Curve.polynomialCurveFinite (F := F) (A := F)
              (fun i : Fin 2 => if i = 0 then base else dir) ↔
          ∃ z : F, (w : ι → F) = base + z • dir := by
      simpa using
        (mem_polynomialCurveFinite_fin2_iff (F := F) (ι := ι) (base := base) (dir := dir)
          (w := (w : ι → F)))

    rcases (hiff.1 hwmem) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    simpa [g] using hz.symm

  refine ⟨Equiv.ofBijective g ⟨hg_inj, hg_surj⟩, ?_⟩
  intro z
  rfl

theorem mu_set_mono [DecidableEq ι] [Fintype ι]
  {μ : ι → Set.Icc (0 : ℚ) 1} {s t : Finset ι} :
  s ⊆ t → mu_set μ s ≤ mu_set μ t := by
  intro hst
  unfold mu_set
  -- monotonicity of the sum
  have hsum : (∑ i ∈ s, ((μ i).1 : ℝ)) ≤ ∑ i ∈ t, ((μ i).1 : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hst ?_
    intro i hit hnot
    -- show nonneg
    have : (0 : ℚ) ≤ (μ i).1 := (μ i).2.1
    exact_mod_cast this
  -- multiply by nonnegative constant
  have hconst : (0 : ℝ) ≤ (1 / (Fintype.card ι : ℝ)) := by positivity
  -- use mul_le_mul_of_nonneg_left
  have := mul_le_mul_of_nonneg_left hsum hconst
  simpa [mul_assoc] using this

theorem mu_set_filter_pos_subset_of_subset_of_ge [DecidableEq ι] [Fintype ι]
  {μ : ι → Set.Icc (0 : ℚ) 1} {s t : Finset ι} :
  s ⊆ t → mu_set μ t ≤ mu_set μ s →
  t.filter (fun i => (μ i).1 > 0) ⊆ s := by
  intro hst hle
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxt, hxpos⟩
  by_contra hxs
  have hxposR : (0 : ℝ) < (μ x).1 := by
    exact_mod_cast hxpos
  have hfactorpos : (0 : ℝ) < (1 / (Fintype.card ι : ℝ)) := by
    have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Classical.choice ‹Nonempty ι›⟩)
    simpa [one_div] using (inv_pos.mpr hcardpos)
  have hlt : mu_set μ s < mu_set μ (insert x s) := by
    unfold mu_set
    -- show the casted sum increases
    have hsum_lt : ((∑ i ∈ s, (μ i).1 : ℚ) : ℝ) < ((∑ i ∈ insert x s, (μ i).1 : ℚ) : ℝ) := by
      -- work in ℚ then cast
      have hsum_lt_q : (∑ i ∈ s, (μ i).1) < (∑ i ∈ insert x s, (μ i).1) := by
        -- rewrite RHS
        have hsum : (∑ i ∈ insert x s, (μ i).1) = (μ x).1 + ∑ i ∈ s, (μ i).1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (Finset.sum_insert (s := s) (a := x) (f := fun i => (μ i).1) hxs)
        -- now strict inequality
        have : (∑ i ∈ s, (μ i).1) < (μ x).1 + ∑ i ∈ s, (μ i).1 := by
          exact lt_add_of_pos_left _ hxpos
        -- rewrite using hsum
        simpa [hsum] using this
      exact_mod_cast hsum_lt_q
    exact (mul_lt_mul_of_pos_left hsum_lt hfactorpos)
  have hsubset : insert x s ⊆ t := by
    exact Finset.insert_subset hxt hst
  have hle' : mu_set μ (insert x s) ≤ mu_set μ s := by
    have := mu_set_mono (μ := μ) (s := insert x s) (t := t) hsubset
    exact le_trans this hle
  exact (not_lt_of_ge hle' hlt)


theorem pr_polynomialCurveFinite_fin2_eq_pr_param [DecidableEq ι] [Fintype ι] [DecidableEq F]
  {base dir : ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1} {α : ℝ≥0} :
  let uLine : Fin 2 → ι → F := fun i => if i = 0 then base else dir
  let line := Curve.polynomialCurveFinite (F := F) (A := F) uLine
  Pr_{let w ←$ᵖ line}[agree_set μ w (finCarrier domain deg) ≥ α]
    = Pr_{let z ←$ᵖ F}[agree_set μ (base + z • dir) (finCarrier domain deg) ≥ α] := by
  classical
  dsimp
  by_cases hdir0 : dir = 0
  · subst hdir0
    -- Define the (degenerate) curve/line as a finset.
    let curve :=
      Curve.polynomialCurveFinite (F := F) (A := F)
        (fun i : Fin 2 => if i = 0 then base else (0 : ι → F))
    -- Every point on the degenerate curve equals `base`.
    have hcurve : ∀ w : curve, ((w : ι → F) = base) := by
      intro w
      have hw :=
        (mem_polynomialCurveFinite_fin2_iff (F := F) (ι := ι)
          (base := base) (dir := (0 : ι → F)) (w := (w : ι → F)))
      dsimp at hw
      rcases (hw.1 w.property) with ⟨z, hz⟩
      simpa [smul_zero, add_zero] using hz
    -- Constant proposition (since `w = base` on the curve, and `base + z•0 = base` on the RHS).
    let p : Prop := (↑α : ℝ) ≤ agree_set μ base (finCarrier domain deg)
    by_cases hp : p
    · -- If `p` holds, both probabilities are `1`.
      have hcard_curve_nat : (#curve) ≠ 0 := by
        simpa [curve] using (Fintype.card_ne_zero (α := curve))
      have hcard_curve : (↑(#curve) : ENNReal) ≠ 0 :=
        (Nat.cast_ne_zero (R := ENNReal)).2 hcard_curve_nat
      have htop_curve : (↑(#curve) : ENNReal) ≠ ⊤ := by simp
      have hcard_F_nat : Fintype.card F ≠ 0 :=
        (Fintype.card_ne_zero : Fintype.card F ≠ 0)
      have hcard_F : (Fintype.card F : ENNReal) ≠ 0 :=
        (Nat.cast_ne_zero (R := ENNReal)).2 hcard_F_nat
      have htop_F : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
      have hleft :
          Pr_{let w ←$ᵖ curve}[agree_set μ (w : ι → F) (finCarrier domain deg) ≥ α] =
            (1 : ENNReal) := by
        -- reduce to a constant `True` predicate and compute the probability
        simp [curve, p, hp, hcurve, PMF.monad_map_eq_map, ENNReal.mul_inv_cancel,
          hcard_curve, htop_curve]
      have hright :
          Pr_{let z ←$ᵖ F}[agree_set μ (base + z • (0 : ι → F)) (finCarrier domain deg) ≥ α] =
            (1 : ENNReal) := by
        simp [p, hp, smul_zero, add_zero, PMF.monad_map_eq_map, ENNReal.mul_inv_cancel,
          hcard_F, htop_F]
      -- Combine.
      calc
        Pr_{let w ←$ᵖ curve}[agree_set μ (w : ι → F) (finCarrier domain deg) ≥ α]
            = (1 : ENNReal) := hleft
        _ = Pr_{let z ←$ᵖ F}[agree_set μ (base + z • (0 : ι → F)) (finCarrier domain deg) ≥ α] :=
            by simpa using hright.symm
    · -- If `p` does not hold, both probabilities are `0`.
      -- `simp` can compute both sides after rewriting to a constant `False` predicate.
      simp [curve, p, hp, hcurve, smul_zero, add_zero, PMF.monad_map_eq_map]
  · -- Nondegenerate case: use the provided equivalence between parameters and curve points.
    obtain ⟨e, he⟩ :=
      (exists_equiv_polynomialCurveFinite_fin2_of_ne_zero (F := F) (ι := ι)
        (base := base) (dir := dir) hdir0)
    have h :=
      Pr_uniform_congr_equiv (α := F)
        (β :=
          (Curve.polynomialCurveFinite (F := F) (A := F)
            (fun i : Fin 2 => if i = 0 then base else dir)))
        e
        (fun w => agree_set μ (w : ι → F) (finCarrier domain deg) ≥ α)
    simpa [he] using h

theorem weighted_RS_list_size_le_bound [DecidableEq ι] [Fintype ι] [DecidableEq F]
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ} (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hsqrt : 0 < sqrtRate) →
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  ∀ w : ι → F,
    let L : Finset (ι → F) := (finCarrier domain deg).filter (fun v => agree μ w v ≥ α)
    (L.card : ℝ) ≤ (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate) := by
  -- This is the RS list-size bound (weighted analogue of the Johnson / Guruswami–Sudan list-decoding bound) in the regime `sqrtRate < α < 1`, with the usual expression `1/min(α-√ρ, √ρ/20) + 3/√ρ`.
  -- 
  -- Why `hsqrt` is needed: when `sqrtRate = 0`, Lean evaluates divisions by 0 in `ℝ` as 0, making the RHS spuriously 0 and the statement false. The hypothesis `0 < sqrtRate` eliminates this pathology.
  -- 
  -- Proof strategy options:
  -- 1. **Reuse existing ArkLib list-decoding theorem** for Reed–Solomon (preferred): search in `ArkLib.Data.CodingTheory` / `GuruswamiSudan` / `JohnsonBound` for a theorem bounding `ncard`/`card` of close codewords, then translate “agreement ≥ α” into an equivalent distance bound.
  -- 2. **Weighted → unweighted reduction using `hμ`**: expand each coordinate `i` into `n_i` copies (common denominator `M`) so that `agree μ` becomes ordinary agreement on the expanded domain; then apply an unweighted RS list-size bound.
  -- 3. If you only find a bound in `ENNReal`/`ℚ`/`ℝ≥0`, coerce to `ℝ` and use `Nat.cast_le` / `Nat.cast_lt` to finish.
  -- 
  -- Implementation note: make sure to keep the bound in `ℝ` (as in the statement) and use explicit rewrites; avoid bare `simp`.
  sorry

theorem weighted_correlated_agreement_affine_line [DecidableEq ι] [Fintype ι] [DecidableEq F] {u : Fin 2 → ι → F}
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
    let line := Curve.polynomialCurveFinite (F := F) (A := F) u
    Pr_{let w ←$ᵖ line}[agree_set μ w (finCarrier domain deg) ≥ α]
  pr > ε →
  pr ≥ ENNReal.ofReal (
         ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
         *
         (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
       ) →
  ∃ ι' : Finset ι, ∃ v : Fin 2 → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ ι' ≥ α ∧
    ∀ i, ∀ x ∈ ι', u i x = v i x := by
  classical
  intro hα hα₁ hμ
  intro hpr hpr'
  simpa using
    (weighted_correlated_agreement_for_parameterized_curves (F := F) (ι := ι)
      (l := 0) (k := 0) (u := u) (deg := deg) (domain := domain) (δ := (α : ℝ≥0))
      (μ := μ) (M := M) (α := α) hμ hα hα₁ (by simpa using hpr) (by simpa using hpr'))

theorem average_weighted_agreement_implies_agreement_of_affineSpan [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hu1 : u 1 = 0) →
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
  letI ε := ProximityGap.errorBound α deg domain
  letI pr :=
    Pr_{let w ←$ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
    }[agree_set μ w (finCarrier domain deg) ≥ α]
  pr > ε →
  pr ≥ ENNReal.ofReal (
         ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
         *
         (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
       ) →
  ∀ w' ∈ (affineSpan F (Finset.univ.image (Fin.tail u)).toSet).direction,
    agree_set μ w' (finCarrier domain deg) ≥ α := by
  classical
  intro hα hα₁ hu1 hμ
  intro hpr hbound
  intro w' hw'

  -- Step 1: find a good parallel affine line in direction `w'`.
  rcases
      (exists_good_parallel_affine_line (F := F) (ι := ι) (u := u) (deg := deg) (domain := domain)
            (μ := μ) (M := M) (α := α) w' hw' hα hα₁ hμ hpr hbound)
    with ⟨base, hbaseU, hprParam_gt, hprParam_ge⟩

  -- Step 2: convert the parametric probability on `F` to the probability on the corresponding
  -- polynomial curve.
  let uLine : Fin 2 → ι → F := fun i => if i = 0 then base else w'
  have hprCurve_eq :
      Pr_{let w ←$ᵖ (Curve.polynomialCurveFinite (F := F) (A := F) uLine)}[
          agree_set μ w (finCarrier domain deg) ≥ α]
        = Pr_{let z ←$ᵖ F}[agree_set μ (base + z • w') (finCarrier domain deg) ≥ α] := by
    simpa [uLine] using
      (pr_polynomialCurveFinite_fin2_eq_pr_param (F := F) (ι := ι) (base := base) (dir := w')
        (deg := deg) (domain := domain) (μ := μ) (α := α))

  have hprCurve_gt :
      Pr_{let w ←$ᵖ (Curve.polynomialCurveFinite (F := F) (A := F) uLine)}[
          agree_set μ w (finCarrier domain deg) ≥ α]
        > ProximityGap.errorBound α deg domain := by
    rw [hprCurve_eq]
    exact hprParam_gt

  have hprCurve_ge :
      Pr_{let w ←$ᵖ (Curve.polynomialCurveFinite (F := F) (A := F) uLine)}[
          agree_set μ w (finCarrier domain deg) ≥ α]
        ≥ ENNReal.ofReal (
            ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
            * (1 / min (α - (ReedSolomonCode.sqrtRate deg domain))
                    ((ReedSolomonCode.sqrtRate deg domain) / 20)
                + 3 / (ReedSolomonCode.sqrtRate deg domain))
          ) := by
    rw [hprCurve_eq]
    exact hprParam_ge

  -- Step 3: apply the affine-line agreement lemma.
  rcases
      (weighted_correlated_agreement_affine_line (F := F) (ι := ι) (u := uLine) (deg := deg)
            (domain := domain) (μ := μ) (M := M) (α := α) hα hα₁ hμ hprCurve_gt hprCurve_ge)
    with ⟨ι', v, hv_code, hmuι', huv⟩

  -- Step 4: use the codeword `v 1` to lower bound the agreement of `w'`.
  have hw_eq : ∀ x ∈ ι', w' x = v 1 x := by
    intro x hx
    have := huv 1 x hx
    have h1 : (1 : Fin 2) ≠ 0 := by
      decide
    simpa [uLine, h1] using this

  have hagree_ge_mu : agree μ w' (v 1) ≥ mu_set μ ι' := by
    refine agree_ge_mu_set_of_eq_on (μ := μ) (u := w') (v := v 1) (ι' := ι') ?_
    intro x hx
    exact hw_eq x hx

  have hagree_ge_alpha : agree μ w' (v 1) ≥ α := by
    exact le_trans hmuι' hagree_ge_mu

  -- `agree_set` is the maximum of `agree` over all codewords in the carrier.
  have hv1_mem : v 1 ∈ finCarrier domain deg := by
    simpa [finCarrier] using hv_code 1

  have hle_agree_set : agree μ w' (v 1) ≤ agree_set μ w' (finCarrier domain deg) := by
    unfold agree_set
    have himem : agree μ w' (v 1) ∈ (Finset.image (agree μ w') (finCarrier domain deg)) := by
      refine Finset.mem_image.2 ?_
      exact ⟨v 1, hv1_mem, rfl⟩
    exact Finset.le_max' _ _ himem

  have : agree_set μ w' (finCarrier domain deg) ≥ α := by
    exact le_trans hagree_ge_alpha hle_agree_set

  simpa using this

theorem weighted_affineSpace_min_agree_ge_alpha [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hsqrt : 0 < sqrtRate) →
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hu1 : u 1 = 0) →
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
  letI ε := ProximityGap.errorBound α deg domain
  letI U : AffineSubspace F (ι → F) := (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
  letI pr := Pr_{let w ←$ᵖ U}[agree_set μ (w : ι → F) (finCarrier domain deg) ≥ α]
  pr > ε →
  pr ≥ ENNReal.ofReal (
         ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
         *
         (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
       ) →
  ∃ wStar : U,
    (∀ w : U, agree_set μ (wStar : ι → F) (finCarrier domain deg) ≤ agree_set μ (w : ι → F) (finCarrier domain deg)) ∧
    α ≤ agree_set μ (wStar : ι → F) (finCarrier domain deg) := by
  -- Bootstrap/minimizer lemma.
  -- 
  -- Goal: For the finite affine subspace `U := u 0 +ᵥ affineSpan ...`, pick `wStar : U` minimizing `agree_set μ (w : ι → F) RS`, and prove `α ≤ agree_set μ wStar RS`.
  -- 
  -- Plan (BCIKS20 Thm 1.6 first-step analogue):
  -- 1. Use `Finset.exists_min_image` on `Finset.univ : Finset U` for the function
  --    `f w := agree_set μ (w : ι → F) (finCarrier domain deg)` to get a minimizer `wStar` and the inequality `f wStar ≤ f w` for all `w`.
  -- 2. Prove **all** points of `U` have agreement ≥ α using a linear-span argument:
  --    - Transfer the probability lower bound from `U` to the linear span `Ū` of `U` (paper’s `\bar U`), using invariance of `agree_set` under nonzero scalar multiplication and the standard decomposition of `Ū` into a disjoint union of `U.direction` and nonzero scalar multiples of `U`.
  --    - Apply `average_weighted_agreement_implies_agreement_of_affineSpan` to `Ū` (origin 0) to conclude every element of `Ū` has agreement ≥ α.
  --    - Conclude in particular that every `w : U` satisfies `α ≤ f w`.
  -- 3. Apply this to `wStar` to conclude `α ≤ f wStar`.
  -- 
  -- If needed, introduce helper lemmas:
  -- - `agree_set` invariance under `z ≠ 0` scaling;
  -- - probability comparison between uniform on `U` and uniform on `Ū`.
  -- 
  -- This lemma replaces the false `weighted_affineSpace_all_points_good` bridge and provides the needed `α ≤ α★` bootstrap.
  sorry

theorem weighted_correlated_agreement_over_affine_spaces_of_direction [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hsqrt : 0 < sqrtRate) →
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hu1 : u 1 = 0) →
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
  (hdir :
    ∀ w' ∈ (affineSpan F (Finset.univ.image (Fin.tail u)).toSet).direction,
      agree_set μ w' (finCarrier domain deg) ≥ α) →
  ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ ι' ≥ α ∧
    ∀ i, ∀ x ∈ ι', u i x = v i x := by
  -- Refactored proof removing the false lemma `weighted_affineSpace_all_points_good`.
  -- 
  -- High-level structure:
  -- - Let `S := affineSpan F (Finset.univ.image (Fin.tail u)).toSet` and `U := u 0 +ᵥ S`.
  -- - Apply `weighted_affineSpace_min_agree_ge_alpha` to obtain a minimizer `uStar : U` and let `αStar := agree_set μ (uStar : ι → F) RS`, with `α ≤ αStar`.
  -- - List-decode around `uStar` at threshold `αStar` using `weighted_RS_list_size_le_bound` to bound the list size and deduce it is `< Fintype.card F` (via `pr ≤ 1`).
  -- - Define submodules `T(v)` indexed by codewords `v` in the list, using the fixed positive-weight core set `D⁺(v)`.
  -- - Use the affine-line theorem at threshold `αStar` to show the direction space is covered by the union of these submodules.
  -- - Apply `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` to conclude one `T(v)` is `⊤`.
  -- - Extract the final agreement set and build the required `v : Fin (l+2) → ι → F`.
  -- 
  -- Key technical trick: when the line lemma gives agreement on a *w-dependent* finset `ι'`, use
  -- `mu_set_filter_pos_subset_of_subset_of_ge` together with the equality
  -- `mu_set D(v0) = αStar` (forced by maximality of `agree_set`) to deduce `D⁺(v0) ⊆ ι'` and hence membership in the fixed submodule `T(v0)`.
  sorry

theorem weighted_correlated_agreement_over_affine_spaces [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hsqrt : 0 < sqrtRate) →
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hu1 : u 1 = 0) →
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
    ∀ i, ∀ x ∈ ι', u i x = v i x := by
  classical
  intro hsqrt hα hα₁ hu1 hμ hpr_gt hpr_lb
  have hdir :
      ∀ w' ∈ (affineSpan F (Finset.univ.image (Fin.tail u)).toSet).direction,
        agree_set μ w' (finCarrier domain deg) ≥ α := by
    exact
      average_weighted_agreement_implies_agreement_of_affineSpan (F := F) (u := u)
        (deg := deg) (domain := domain) (μ := μ) (M := M) (α := α)
        hα hα₁ hu1 hμ hpr_gt hpr_lb
  exact
    weighted_correlated_agreement_over_affine_spaces_of_direction (F := F) (k := k) (l := l) (u := u)
      (deg := deg) (domain := domain) (μ := μ) (M := M) (α := α)
      hsqrt hα hα₁ hu1 hμ hpr_gt hpr_lb hdir


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
