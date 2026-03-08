/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

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

theorem card_filter_gt_of_sum_gt {n : ℕ} (f : Fin n → ℕ) (M T k : ℕ)
  (hTM : T ≤ M)
  (hf : ∀ x, f x ≤ M)
  (hsum : (Finset.univ.sum f) > k * M + (n - k) * T) :
  (Finset.univ.filter (fun x : Fin n => f x > T)).card ≥ k + 1 := by
  classical
  by_cases hkn : n ≤ k
  · -- If `n ≤ k`, then the inequality on the sum is impossible.
    exfalso
    have hsum_le_nM : (Finset.univ.sum f) ≤ n * M := by
      -- Bound each term by `M`.
      simpa [Nat.nsmul_eq_mul, Finset.card_univ] using
        (Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin n))) (f := f) (n := M)
          (by
            intro x hx
            exact hf x))
    have hnM_le_kM : n * M ≤ k * M := Nat.mul_le_mul_right M hkn
    have hle : (Finset.univ.sum f) ≤ k * M + (n - k) * T := by
      simpa [Nat.sub_eq_zero_of_le hkn, Nat.mul_zero, Nat.add_zero] using
        (le_trans hsum_le_nM hnM_le_kM)
    exact (Nat.not_lt_of_ge hle) hsum
  · have hklt : k < n := Nat.lt_of_not_ge hkn
    have hk_le_n : k ≤ n := Nat.le_of_lt hklt

    -- Good indices are those where `f x > T`.
    let Good : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => f x > T)
    let Bad : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => ¬ f x > T)

    have hGood_le_n : Good.card ≤ n := by
      simpa [Good, Finset.card_univ] using
        (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun x : Fin n => f x > T))

    have hsplit : (Finset.univ.sum f) = Good.sum f + Bad.sum f := by
      -- Split the sum over `Good` and its complement.
      simpa [Good, Bad] using
        (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n)))
          (p := fun x : Fin n => f x > T) (f := f)).symm

    have hGoodSum : Good.sum f ≤ Good.card * M := by
      -- Upper bound each term on `Good` by `M`.
      simpa [Nat.nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (s := Good) (f := f) (n := M)
          (by
            intro x hx
            exact hf x))

    have hBadSum : Bad.sum f ≤ Bad.card * T := by
      have hle : ∀ x ∈ Bad, f x ≤ T := by
        intro x hx
        have hx' : ¬ f x > T := (Finset.mem_filter.mp hx).2
        exact le_of_not_gt hx'
      simpa [Nat.nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (s := Bad) (f := f) (n := T) hle)

    have hcard_partition : Good.card + Bad.card = n := by
      -- Cardinalities of the filtered set and its complement add to `n`.
      simpa [Good, Bad, Finset.card_univ] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
          (p := fun x : Fin n => f x > T))

    have hBad_card : Bad.card = n - Good.card := Nat.eq_sub_of_add_eq' hcard_partition

    have hsum_le : (Finset.univ.sum f) ≤ Good.card * M + (n - Good.card) * T := by
      calc
        Finset.univ.sum f
            = Good.sum f + Bad.sum f := hsplit
        _ ≤ Good.card * M + Bad.card * T := Nat.add_le_add hGoodSum hBadSum
        _ = Good.card * M + (n - Good.card) * T := by simp [hBad_card]

    -- A rewriting lemma for the upper bound on the sum.
    have rewrite :
        ∀ a : ℕ, a ≤ n → a * M + (n - a) * T = a * (M - T) + n * T := by
      intro a ha
      have hMul : a * M = a * (M - T) + a * T := by
        calc
          a * M = a * ((M - T) + T) := by
            simp [Nat.sub_add_cancel hTM]
          _ = a * (M - T) + a * T := by
            simp [Nat.mul_add]
      have hT : a * T + (n - a) * T = (a + (n - a)) * T := by
        simpa using (Nat.add_mul a (n - a) T).symm
      calc
        a * M + (n - a) * T
            = (a * (M - T) + a * T) + (n - a) * T := by
                simpa [hMul, Nat.add_assoc]
        _ = a * (M - T) + (a * T + (n - a) * T) := by
                simp [Nat.add_assoc]
        _ = a * (M - T) + (a + (n - a)) * T := by
                simp [hT]
        _ = a * (M - T) + n * T := by
                simp [Nat.add_sub_of_le ha]

    have hGood_ge : Good.card ≥ k + 1 := by
      by_contra hge
      have hGood_le_k : Good.card ≤ k := by
        have : Good.card < k + 1 := Nat.lt_of_not_ge hge
        exact Nat.le_of_lt_succ this

      have hGood_rw : Good.card * M + (n - Good.card) * T = Good.card * (M - T) + n * T :=
        rewrite Good.card hGood_le_n

      have hk_rw : k * M + (n - k) * T = k * (M - T) + n * T :=
        rewrite k hk_le_n

      have hcompare : Good.card * M + (n - Good.card) * T ≤ k * M + (n - k) * T := by
        -- Rewrite both sides as `(_)*(M-T) + n*T`.
        rw [hGood_rw, hk_rw]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right (M - T) hGood_le_k) (n * T)

      have hle_final : (Finset.univ.sum f) ≤ k * M + (n - k) * T := le_trans hsum_le hcompare
      exact (Nat.not_lt_of_ge hle_final) hsum

    simpa [Good] using hGood_ge

theorem hammingDist_le_floor_of_relHammingDist_le {n : ℕ} {F : Type} [Field F] [DecidableEq F] (u v : Fin n → F) (δ : ℚ)
  (hn : n ≠ 0) (h : (δᵣ(u, v) : ℚ) ≤ δ) :
  Δ₀(u, v) ≤ Nat.floor (δ * n) := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have hdiv : (Δ₀(u, v) : ℚ) / n ≤ δ := by
    simpa [Code.relHammingDist] using h
  have hnposQ : (0 : ℚ) < n := by
    exact_mod_cast hnpos
  have hmul : (Δ₀(u, v) : ℚ) ≤ δ * n := (div_le_iff₀ hnposQ).1 hdiv
  have hδnonneg : (0 : ℚ) ≤ δ := by
    exact le_trans (NNRat.cast_nonneg (δᵣ(u, v))) h
  have ha : (0 : ℚ) ≤ δ * n := by
    have hnnonneg : (0 : ℚ) ≤ n := by
      exact_mod_cast (Nat.zero_le n)
    exact mul_nonneg hδnonneg hnnonneg
  exact (Nat.le_floor_iff (α := ℚ) (n := Δ₀(u, v)) (a := δ * n) ha).2 hmul

theorem hammingDist_Pz_le_floor {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (z : F) (hz : z ∈ matching_set k ωs δ u₀ u₁ h_gs) :
  Δ₀(u₀ + z • u₁,
    (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity (F := F) k h_gs hz)).eval ∘ ωs)
    ≤ Nat.floor (δ * n) := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp
    ext i
    cases i with
    | mk val isLt =>
      cases isLt
  ·
    let hzS : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ :=
      (matching_set_is_a_sub_of_coeffs_of_close_proximity (F := F) k h_gs) hz
    have hδr :
        (δᵣ(u₀ + z • u₁,
            (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hzS).eval ∘ ωs) : ℚ) ≤
          δ := by
      simpa [Pz, hzS] using
        (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) (ωs := ωs) (δ := δ)
              (u₀ := u₀) (u₁ := u₁) hzS).choose_spec.2
    have hΔ :=
      hammingDist_le_floor_of_relHammingDist_le (n := n) (F := F) (u := u₀ + z • u₁)
        (v :=
          (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hzS).eval ∘
            ωs)
        δ hn hδr
    simpa [hzS] using hΔ

noncomputable def matching_set_at_x_fixed (k : ℕ) (δ : ℚ)
  {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n) : Finset F :=
  (matching_set k ωs δ u₀ u₁ h_gs).filter (fun z =>
    if hz : z ∈ matching_set k ωs δ u₀ u₁ h_gs then
      u₀ x + z * u₁ x =
        (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity (F := F) k h_gs hz)).eval (ωs x)
    else False
  )

theorem matching_set_at_x_fixed_subset_matching_set {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n) :
  matching_set_at_x_fixed k δ h_gs x ⊆ matching_set k ωs δ u₀ u₁ h_gs := by
  intro z hz
  dsimp [matching_set_at_x_fixed] at hz ⊢
  exact (Finset.mem_filter.mp hz).1

theorem matching_set_at_x_fixed_card_le_matching_set_card {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n) :
  (matching_set_at_x_fixed k δ h_gs x).card ≤ (matching_set k ωs δ u₀ u₁ h_gs).card := by
  -- Immediate from subset lemma and `Finset.card_le_card`
  exact Finset.card_le_card (matching_set_at_x_fixed_subset_matching_set (k := k) (δ := δ) h_gs x)


theorem mem_matching_set_at_x_fixed_iff {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (x : Fin n) (z : F) (hz : z ∈ matching_set k ωs δ u₀ u₁ h_gs) :
  z ∈ matching_set_at_x_fixed k δ h_gs x ↔
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity (F := F) k h_gs hz)).eval (ωs x) := by
  classical
  simp [matching_set_at_x_fixed, hz]

theorem matching_set_at_x_fixed_count_ge {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (z : F) (hz : z ∈ matching_set k ωs δ u₀ u₁ h_gs) :
  (Finset.univ.filter (fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x)).card
    ≥ n - Nat.floor (δ * n) := by
  classical
  -- Abbreviate the comparison function and the agreement predicate
  let Pfun : Fin n → F :=
    (Pz
        (matching_set_is_a_sub_of_coeffs_of_close_proximity (F := F) k h_gs hz)).eval ∘
      ωs
  let agree : Fin n → Prop := fun x : Fin n => (u₀ + z • u₁) x = Pfun x

  -- Bad positions: where the two functions disagree
  let Bad : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => ¬ agree x)

  have hBad_card : Bad.card = Δ₀(u₀ + z • u₁, Pfun) := by
    -- `Δ₀` is `hammingDist`, which is the card of the set of indices where the functions differ
    simp [Bad, agree, Pfun, hammingDist]

  have hBad_le : Bad.card ≤ Nat.floor (δ * n) := by
    have hdist : Δ₀(u₀ + z • u₁, Pfun) ≤ Nat.floor (δ * n) := by
      simpa [Pfun] using (hammingDist_Pz_le_floor (F := F) (k := k) (δ := δ) h_gs z hz)
    simpa [hBad_card] using hdist

  have hgood_eq : (Finset.univ.filter agree).card = n - Bad.card := by
    have hsum :
        (Finset.univ.filter agree).card +
            (Finset.univ.filter (fun x : Fin n => ¬ agree x)).card =
          (Finset.univ : Finset (Fin n)).card := by
      simpa using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := agree))
    have hsum' : (Finset.univ.filter agree).card + Bad.card = (Finset.univ : Finset (Fin n)).card := by
      simpa [Bad] using hsum
    have := congrArg (fun t => t - Bad.card) hsum'
    -- `(a + b) - b = a` and `#(Finset.univ : Finset (Fin n)) = n`
    simpa [Finset.card_univ] using this

  have hgood_ge : (Finset.univ.filter agree).card ≥ n - Nat.floor (δ * n) := by
    have hsub : n - Nat.floor (δ * n) ≤ n - Bad.card :=
      Nat.sub_le_sub_left hBad_le n
    -- rewrite `n - Bad.card` using `hgood_eq`
    simpa [← hgood_eq] using hsub

  -- Rewrite the filter predicate using `mem_matching_set_at_x_fixed_iff`
  have hfilter :
      Finset.univ.filter (fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x) =
        Finset.univ.filter agree := by
    ext x
    simp [agree, Pfun,
      mem_matching_set_at_x_fixed_iff (F := F) (k := k) (δ := δ) (h_gs := h_gs) (x := x)
        (z := z) (hz := hz)]

  simpa [hfilter] using hgood_ge

theorem sum_matching_set_at_x_fixed_card_eq_sum_count {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card))
    =
  (matching_set k ωs δ u₀ u₁ h_gs).sum
    (fun z : F => (Finset.univ.filter (fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x)).card) := by
  classical
  let S : Finset F := matching_set k ωs δ u₀ u₁ h_gs
  have hfilter_eq :
      ∀ x : Fin n,
        S.filter (fun z : F => z ∈ matching_set_at_x_fixed k δ h_gs x) =
          matching_set_at_x_fixed k δ h_gs x := by
    intro x
    ext z
    constructor
    · intro hz
      exact (Finset.mem_filter.mp hz).2
    · intro hz
      have hzS : z ∈ S := by
        have hsub :=
          matching_set_at_x_fixed_subset_matching_set
            (k := k) (δ := δ) (h_gs := h_gs) (x := x)
        have : z ∈ matching_set k ωs δ u₀ u₁ h_gs := hsub hz
        simpa [S] using this
      exact Finset.mem_filter.mpr ⟨hzS, hz⟩
  have hcard_eq :
      ∀ x : Fin n,
        (matching_set_at_x_fixed k δ h_gs x).card =
          S.sum (fun z : F =>
            if z ∈ matching_set_at_x_fixed k δ h_gs x then (1 : ℕ) else 0) := by
    intro x
    have hx :
        (matching_set_at_x_fixed k δ h_gs x).card =
          (S.filter (fun z : F => z ∈ matching_set_at_x_fixed k δ h_gs x)).card := by
      have := congrArg Finset.card (hfilter_eq x)
      exact this.symm
    have hfilter :
        (S.filter (fun z : F => z ∈ matching_set_at_x_fixed k δ h_gs x)).card =
          S.sum (fun z : F =>
            if z ∈ matching_set_at_x_fixed k δ h_gs x then (1 : ℕ) else 0) := by
      simpa using
        (Finset.card_filter (s := S)
          (p := fun z : F => z ∈ matching_set_at_x_fixed k δ h_gs x))
    exact hx.trans hfilter
  calc
    (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card)) =
        Finset.univ.sum
          (fun x : Fin n =>
            S.sum (fun z : F =>
              if z ∈ matching_set_at_x_fixed k δ h_gs x then (1 : ℕ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simpa using hcard_eq x
    _ =
        S.sum (fun z : F =>
          Finset.univ.sum (fun x : Fin n =>
            if z ∈ matching_set_at_x_fixed k δ h_gs x then (1 : ℕ) else 0)) := by
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := S)
              (f := fun (x : Fin n) (z : F) =>
                if z ∈ matching_set_at_x_fixed k δ h_gs x then (1 : ℕ) else 0))
    _ =
        S.sum (fun z : F =>
          (Finset.univ.filter (fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x)).card) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simpa using
            (Finset.card_filter (s := (Finset.univ : Finset (Fin n)))
              (p := fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x)).symm
    _ =
        (matching_set k ωs δ u₀ u₁ h_gs).sum
          (fun z : F =>
            (Finset.univ.filter (fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x)).card) := by
          simpa [S]

theorem sum_matching_set_at_x_fixed_card_ge {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card))
    ≥ (matching_set k ωs δ u₀ u₁ h_gs).card * (n - Nat.floor (δ * n)) := by
  classical
  -- rewrite the LHS using the provided double-counting identity
  have hrewrite :=
    (sum_matching_set_at_x_fixed_card_eq_sum_count (k := k) (δ := δ) (h_gs := h_gs) (ωs := ωs))
  -- set S for readability
  set S : Finset F := matching_set k ωs δ u₀ u₁ h_gs with hS
  -- use the rewrite, then bound each term in the sum
  calc
    (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card))
        = ∑ z ∈ S,
            (Finset.univ.filter (fun x : Fin n => z ∈ matching_set_at_x_fixed k δ h_gs x)).card := by
          simpa [S] using hrewrite
    _ ≥ ∑ z ∈ S, (n - Nat.floor (δ * n)) := by
          -- pointwise lower bound on each term
          refine Finset.sum_le_sum ?_  -- produces ≤, then we flip via rewriting
          intro z hz
          -- goal is: (n - floor ...) ≤ count
          -- provided by matching_set_at_x_fixed_count_ge
          simpa [S] using (matching_set_at_x_fixed_count_ge (k := k) (δ := δ) (h_gs := h_gs) (ωs := ωs) z hz)
    _ = S.card * (n - Nat.floor (δ * n)) := by
          -- sum of a constant over a finset
          simp
    _ = (matching_set k ωs δ u₀ u₁ h_gs).card * (n - Nat.floor (δ * n)) := by
          simpa [S]

theorem sum_matching_set_at_x_fixed_card_gt {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (hk : k + 2 ≤ n)
  (hfloor : Nat.floor (δ * n) ≤ n - (k + 1)) {D : ℕ}
  (hD : D = Bivariate.totalDegree (H k δ x₀ h_gs))
  (hM : (n - k) * ((2 * k + 1)
        * (Bivariate.natDegreeY (H k δ x₀ h_gs))
        * (Bivariate.natDegreeY (R k δ x₀ h_gs))
        * D)
      < (matching_set k ωs δ u₀ u₁ h_gs).card) :
  (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card))
    > k * (matching_set k ωs δ u₀ u₁ h_gs).card
      + (n - k) * ((2 * k + 1)
        * (Bivariate.natDegreeY (H k δ x₀ h_gs))
        * (Bivariate.natDegreeY (R k δ x₀ h_gs))
        * D) := by
  classical
  -- Abbreviate the main natural-number quantities
  set M : ℕ := (matching_set k ωs δ u₀ u₁ h_gs).card with hMdef
  set e : ℕ := Nat.floor (δ * n) with hedef
  set T : ℕ :=
      (2 * k + 1) * (Bivariate.natDegreeY (H k δ x₀ h_gs))
        * (Bivariate.natDegreeY (R k δ x₀ h_gs)) * D with hTdef

  have hge : M * (n - e)
      ≤ (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card)) := by
    simpa [M, e] using
      (sum_matching_set_at_x_fixed_card_ge (k := k) (δ := δ) (ωs := ωs) h_gs)

  have hfloor' : e ≤ n - (k + 1) := by
    simpa [e] using hfloor

  have hM' : (n - k) * T < M := by
    simpa [M, T] using hM

  have hk1 : k + 1 ≤ n - e := by
    omega

  have hkm : k * M + M ≤ M * (n - e) := by
    have hmul : (k + 1) * M ≤ (n - e) * M := Nat.mul_le_mul_right M hk1
    calc
      k * M + M = (k + 1) * M := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_mul k M).symm
      _ ≤ (n - e) * M := hmul
      _ = M * (n - e) := by
        simpa [Nat.mul_comm]

  have harith : k * M + (n - k) * T < M * (n - e) := by
    have h1 : k * M + (n - k) * T < k * M + M :=
      Nat.add_lt_add_left hM' (k * M)
    exact lt_of_lt_of_le h1 hkm

  have hlt : k * M + (n - k) * T
        < (Finset.univ.sum (fun x : Fin n => (matching_set_at_x_fixed k δ h_gs x).card)) :=
    lt_of_lt_of_le harith hge

  -- Rewrite back in terms of the original expressions
  simpa [gt_iff_lt, M, T] using hlt

theorem exists_points_with_large_matching_subset {ωs : Fin n ↪ F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (hk : k + 2 ≤ n)
  (hfloor : Nat.floor (δ * n) ≤ n - (k + 1)) {D : ℕ}
  (hD : D = Bivariate.totalDegree (H k δ x₀ h_gs))
  (hM : (n - k) * ((2 * k + 1)
        * (Bivariate.natDegreeY (H k δ x₀ h_gs))
        * (Bivariate.natDegreeY (R k δ x₀ h_gs))
        * D)
      < (matching_set k ωs δ u₀ u₁ h_gs).card) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x_fixed k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  classical
  -- Basic notation
  let S : Finset F := matching_set k ωs δ u₀ u₁ h_gs
  let M : ℕ := S.card
  let f : Fin n → ℕ := fun x : Fin n =>
    (matching_set_at_x_fixed (F := F) (n := n) (m := m) (k := k) (δ := δ)
        (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs x).card
  let T : ℕ :=
    (2 * k + 1)
      * (Bivariate.natDegreeY (H k δ x₀ h_gs))
      * (Bivariate.natDegreeY (R k δ x₀ h_gs))
      * D

  have hf : ∀ x, f x ≤ M := by
    intro x
    simpa [f, M, S] using
      (matching_set_at_x_fixed_card_le_matching_set_card (F := F) (n := n) (m := m)
        (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs x)

  have hsum : (Finset.univ.sum f) > k * M + (n - k) * T := by
    -- obtain the strict inequality from the provided lemma
    simpa [f, M, S, T] using
      (sum_matching_set_at_x_fixed_card_gt (F := F) (n := n) (m := m) (k := k)
        (δ := δ) (x₀ := x₀) (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs)
        h_gs hk hfloor (D := D) hD hM)

  have hTM : T ≤ M := by
    -- use the hypothesis `hM` (and `hk`) to see `T ≤ M`
    have hklt : k < k + 2 := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.lt_add_of_pos_right (n := k) (m := 2) (by decide : 0 < (2 : ℕ)))
    have hkn : k < n := lt_of_lt_of_le hklt hk
    have hpos : 0 < n - k := Nat.sub_pos_of_lt hkn
    have hone : (1 : ℕ) ≤ n - k := Nat.succ_le_of_lt hpos
    have hT_le_mul : T ≤ (n - k) * T := by
      -- 1*T ≤ (n-k)*T
      have : (1 : ℕ) * T ≤ (n - k) * T := Nat.mul_le_mul_right T hone
      simpa [Nat.one_mul] using this
    have hmul_lt : (n - k) * T < M := by
      -- unfold `M`, `T`, `S` in the provided hypothesis
      simpa [M, S, T, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hM
    exact le_of_lt (lt_of_le_of_lt hT_le_mul hmul_lt)

  have hgood : (Finset.univ.filter (fun x : Fin n => f x > T)).card ≥ k + 1 := by
    simpa [f, M, T] using (card_filter_gt_of_sum_gt (n := n) f M T k hTM hf hsum)

  rcases Finset.exists_subset_card_eq
      (s := (Finset.univ.filter fun x : Fin n => f x > T)) (n := k + 1) hgood with
    ⟨Dtop, hDtop_sub, hDtop_card⟩

  refine ⟨Dtop, hDtop_card, ?_⟩
  intro x hx
  have hxmem : x ∈ Finset.univ.filter (fun x : Fin n => f x > T) := hDtop_sub hx
  have hxgood' : f x > T := (Finset.mem_filter.mp hxmem).2
  simpa [f, T] using hxgood'


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
