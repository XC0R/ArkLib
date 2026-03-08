/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

import Mathlib.Data.Nat.Cast.Order.Ring
import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import ArkLib.Data.CodingTheory.PolishchukSpielman.PolishchukSpielman
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

noncomputable def RSCodeFinset (ωs : Fin n ↪ F) (deg : ℕ) : Finset (Fin n → F) :=
  ReedSolomonCode.finCarrier ωs deg

theorem RSCodeFinset_nonempty {ωs : Fin n ↪ F} {deg : ℕ} : (RSCodeFinset (n := n) (F := F) ωs deg).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  unfold RSCodeFinset ReedSolomonCode.finCarrier
  simp

noncomputable def bwError (δ : ℚ≥0) (n : ℕ) : ℕ := Nat.floor ((δ : ℝ≥0) * n)

theorem bwError_unique_decoding_ineq {deg : ℕ} {δ : ℚ≥0}
  (hδ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2) :
  2 * bwError δ n < n - deg + 1 := by
  classical
  set e : ℕ := bwError δ n

  have he_le : (e : ℝ≥0) ≤ (δ : ℝ≥0) * n := by
    subst e
    dsimp [bwError]
    simpa using (Nat.floor_le (a := (δ : ℝ≥0) * n) (by exact zero_le _))

  have hn0 : (n : ℚ≥0) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)

  have h2 : (2 : ℚ≥0) * δ ≤ (1 - (deg : ℚ≥0) / n) := by
    -- multiply `hδ` by 2
    have h :=
      mul_le_mul_of_nonneg_left hδ (show (0 : ℚ≥0) ≤ (2 : ℚ≥0) by exact zero_le _)
    -- simplify
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h

  have hδn : (2 : ℚ≥0) * (δ * n) ≤ (n : ℚ≥0) - deg := by
    -- multiply by n and rewrite
    have h :=
      mul_le_mul_of_nonneg_right h2 (show (0 : ℚ≥0) ≤ (n : ℚ≥0) by exact zero_le _)
    -- rewrite (1 - deg/n) * n
    have hmul_deg : ((deg : ℚ≥0) / n) * (n : ℚ≥0) = deg := by
      -- `a / b * b = a` for `b ≠ 0`
      simpa [div_eq_mul_inv, mul_assoc] using
        (mul_inv_cancel_right₀ (a := (deg : ℚ≥0)) hn0)
    have hmul_sub : (1 - (deg : ℚ≥0) / n) * (n : ℚ≥0) = (n : ℚ≥0) - deg := by
      calc
        (1 - (deg : ℚ≥0) / n) * (n : ℚ≥0)
            = (1 : ℚ≥0) * (n : ℚ≥0) - ((deg : ℚ≥0) / n) * (n : ℚ≥0) := by
                simpa using (tsub_mul (1 : ℚ≥0) ((deg : ℚ≥0) / n) (n : ℚ≥0))
        _ = (n : ℚ≥0) - deg := by
              simp [hmul_deg]
    -- now finish
    simpa [mul_assoc, hmul_sub] using h

  -- convert `hδn` to `ℝ≥0`
  have hδnR : (2 : ℝ≥0) * ((δ : ℝ≥0) * n) ≤ (n : ℝ≥0) - deg := by
    -- cast inequality from ℚ≥0 to ℝ≥0
    exact_mod_cast hδn

  have hmainR : (2 : ℝ≥0) * (e : ℝ≥0) ≤ (n : ℝ≥0) - deg := by
    have h :=
      mul_le_mul_of_nonneg_left he_le (show (0 : ℝ≥0) ≤ (2 : ℝ≥0) by exact zero_le _)
    exact le_trans h hδnR

  have hmain_nat : 2 * e ≤ n - deg := by
    -- go back to Nat
    exact_mod_cast hmainR

  have : 2 * e < n - deg + 1 := Nat.lt_succ_of_le hmain_nat
  simpa [e] using this


noncomputable def curveMismatchSet {l : ℕ} (u v : Fin l → Fin n → F) : Finset (Fin n) :=
  {x : Fin n | (fun i => u i x) ≠ fun i => v i x}

theorem curve_relDist_le_of_curveMismatchSet_card_le {l : ℕ} {δ : ℚ≥0} {u v : Fin l → Fin n → F}
  (hm : (curveMismatchSet (n := n) (F := F) u v).card ≤ δ * n) :
  ∀ z : F, δᵣ(curve u z, curve v z) ≤ δ := by
  intro z
  classical
  -- Define the coordinatewise evaluation functional used in the curve definition
  let g : (Fin l → F) → F := fun w => ∑ i, z ^ i.1 • w i

  -- Applying a function coordinatewise cannot increase Hamming distance
  have hcomp' :
      Δ₀((fun x : Fin n => g (fun i : Fin l => u i x)),
        (fun x : Fin n => g (fun i : Fin l => v i x)))
        ≤
      Δ₀((fun x : Fin n => fun i : Fin l => u i x),
        (fun x : Fin n => fun i : Fin l => v i x)) := by
    -- `hammingDist_comp_le_hammingDist` is stated in terms of `hammingDist`; our `Δ₀` is notation.
    simpa [g] using
      (hammingDist_comp_le_hammingDist (ι := Fin n)
        (β := fun _ : Fin n => F)
        (γ := fun _ : Fin n => (Fin l → F))
        (f := fun _ => g)
        (x := fun x : Fin n => fun i : Fin l => u i x)
        (y := fun x : Fin n => fun i : Fin l => v i x))

  -- Rewrite the LHS as the distance between the curve points
  have hcurve_u : (fun x : Fin n => g (fun i : Fin l => u i x)) = curve u z := by
    ext x
    simp [g, curve, Finset.sum_apply]
  have hcurve_v : (fun x : Fin n => g (fun i : Fin l => v i x)) = curve v z := by
    ext x
    simp [g, curve, Finset.sum_apply]

  have hcomp : Δ₀(curve u z, curve v z)
        ≤
      Δ₀((fun x : Fin n => fun i : Fin l => u i x),
        (fun x : Fin n => fun i : Fin l => v i x)) := by
    simpa [hcurve_u, hcurve_v] using hcomp'

  -- The RHS distance is exactly the size of `curveMismatchSet u v`
  have hRHS :
      Δ₀((fun x : Fin n => fun i : Fin l => u i x),
        (fun x : Fin n => fun i : Fin l => v i x))
        = (curveMismatchSet (n := n) (F := F) u v).card := by
    rfl

  have hΔ : (Δ₀(curve u z, curve v z) : ℚ≥0) ≤ (curveMismatchSet (n := n) (F := F) u v).card := by
    have : (Δ₀(curve u z, curve v z) : ℚ≥0) ≤
        (Δ₀((fun x : Fin n => fun i : Fin l => u i x),
          (fun x : Fin n => fun i : Fin l => v i x)) : ℚ≥0) := by
      exact_mod_cast hcomp
    simpa [hRHS] using this

  have hnpos : (0 : ℚ≥0) < (n : ℚ≥0) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))

  -- Unfold relative Hamming distance and clear the denominator using `div_le_iff₀`.
  unfold Code.relHammingDist
  have hmain : (Δ₀(curve u z, curve v z) : ℚ≥0) ≤ δ * n := le_trans hΔ hm
  -- `Fintype.card (Fin n) = n`
  simpa [Fintype.card_fin] using ( (div_le_iff₀ hnpos).2 hmain )


theorem exists_close_RSCodeword_of_mem_coeffs_of_close_proximity_curve {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0} {u : Fin l → Fin n → F} {z : F}
  (hz : z ∈ coeffs_of_close_proximity_curve δ u (RSCodeFinset (n := n) (F := F) ωs deg)) :
  ∃ w ∈ RSCodeFinset (n := n) (F := F) ωs deg, δᵣ(curve u z, w) ≤ δ := by
  classical
  -- Unfold membership in `coeffs_of_close_proximity_curve`
  unfold coeffs_of_close_proximity_curve at hz
  -- `hz` is membership in a `Set.toFinset`, so simplify
  simp at hz
  -- Now `hz : δᵣ(curve u z, RSCodeFinset ωs deg) ≤ δ`
  -- Convert δ to NNReal to use `Code.relCloseToCode_iff_relCloseToCodeword_of_minDist`
  set δR : ℝ≥0 := (δ : ℝ≥0)
  have hz' : δᵣ(curve u z, (RSCodeFinset (n := n) (F := F) ωs deg : Set (Fin n → F))) ≤ δR := by
    -- coe-coe and rewrite
    simpa [δR] using hz
  -- Apply the closeness-to-code lemma
  have hw : ∃ w ∈ (RSCodeFinset (n := n) (F := F) ωs deg : Set (Fin n → F)), δᵣ(curve u z, w) ≤ δR :=
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (u := curve u z)
      (C := (RSCodeFinset (n := n) (F := F) ωs deg : Set (Fin n → F))) (δ := δR)).1 hz'
  rcases hw with ⟨w, hwmem, hwdist⟩
  refine ⟨w, ?_, ?_⟩
  · -- membership back in the finset
    simpa using hwmem
  · -- convert distance bound back to ℚ≥0
    -- `hwdist : (δᵣ(curve u z, w) : ℝ≥0) ≤ δR`
    -- so cast back
    simpa [δR] using hwdist

theorem mem_RSCodeFinset_iff_mem_RSCode {ωs : Fin n ↪ F} {deg : ℕ} {w : Fin n → F} : w ∈ RSCodeFinset (n := n) (F := F) ωs deg ↔ w ∈ ReedSolomon.code ωs deg := by
  unfold RSCodeFinset
  simp [ReedSolomonCode.finCarrier]

theorem curve_mem_RSCodeFinset {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {v : Fin l → Fin n → F} (hv : ∀ i, v i ∈ RSCodeFinset (n := n) (F := F) ωs deg) (z : F) : curve v z ∈ RSCodeFinset (n := n) (F := F) ωs deg := by
  classical
  -- Convert the goal to a submodule membership goal
  rw [mem_RSCodeFinset_iff_mem_RSCode]
  -- Convert the hypotheses similarly
  have hv' : ∀ i, v i ∈ ReedSolomon.code ωs deg := by
    intro i
    exact (mem_RSCodeFinset_iff_mem_RSCode (n := n) (F := F) (ωs := ωs) (deg := deg) (w := v i)).1 (hv i)
  -- Now use closure of the Reed–Solomon code under linear combinations
  simpa [curve] using
    (ReedSolomon.code ωs deg).sum_mem (t := (Finset.univ : Finset (Fin l)))
      (fun i _ => (ReedSolomon.code ωs deg).smul_mem (z ^ i.1) (hv' i))

theorem coeffs_of_close_proximity_curve_eq_univ_of_exists_v {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0} {u v : Fin l → Fin n → F}
  (hv : ∀ i, v i ∈ RSCodeFinset (n := n) (F := F) ωs deg)
  (hclose : ∀ z, δᵣ(curve u z, curve v z) ≤ δ)
  : coeffs_of_close_proximity_curve δ u (RSCodeFinset (n := n) (F := F) ωs deg) = (Finset.univ : Finset F) := by
  classical
  ext z
  simp [coeffs_of_close_proximity_curve]
  have hzmem : curve v z ∈ RSCodeFinset (n := n) (F := F) ωs deg :=
    curve_mem_RSCodeFinset (n := n) (F := F) (l := l) (ωs := ωs) (deg := deg) hv z
  have hle :
      δᵣ(curve u z, (↑(RSCodeFinset (n := n) (F := F) ωs deg) : Set (Fin n → F))) ≤
        (δᵣ(curve u z, curve v z) : ENNReal) := by
    simpa using
      (Code.relDistFromCode_le_relDist_to_mem (ι := Fin n) (F := F)
        (u := curve u z)
        (C := (↑(RSCodeFinset (n := n) (F := F) ωs deg) : Set (Fin n → F)))
        (v := curve v z)
        (by simpa using hzmem))
  have hclose' : (δᵣ(curve u z, curve v z) : ENNReal) ≤ (δ : ENNReal) := by
    -- first cast the inequality to `ℝ≥0`, then to `ℝ≥0∞`
    have hclose_nnreal : (δᵣ(curve u z, curve v z) : NNReal) ≤ (δ : NNReal) := by
      exact_mod_cast (hclose z)
    -- now coe to `ENNReal`
    have hclose_ennreal :
        ((δᵣ(curve u z, curve v z) : NNReal) : ENNReal) ≤ ((δ : NNReal) : ENNReal) :=
      (ENNReal.coe_le_coe).2 hclose_nnreal
    -- rewrite casts from `ℚ≥0` to `ENNReal` via `NNReal`
    simpa [ENNReal.coe_nnratCast] using hclose_ennreal
  exact le_trans hle hclose'

theorem exists_poly_of_mem_coeffs_of_close_proximity_curve {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0} {u : Fin l → Fin n → F} {z : F}
  (hz : z ∈ coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)) :
  ∃ p : Polynomial F,
    p ∈ Polynomial.degreeLT F deg ∧
    Δ₀(curve u z, p.eval ∘ ωs) ≤ bwError δ n := by
  classical
  rcases
      exists_close_RSCodeword_of_mem_coeffs_of_close_proximity_curve
        (n := n) (F := F) (ωs := ωs) (deg := deg) (δ := δ) (u := u) (z := z) hz with
    ⟨w, hwRS, hrel⟩

  have hwRS' : w ∈ ReedSolomon.code ωs deg :=
    (mem_RSCodeFinset_iff_mem_RSCode (n := n) (F := F) (ωs := ωs) (deg := deg) (w := w)).1 hwRS

  -- unpack membership in the RS code as an evaluation of a low-degree polynomial
  rcases (by simpa [ReedSolomon.code] using hwRS') with ⟨p, hpLT, hpw⟩

  refine ⟨p, hpLT, ?_⟩

  -- turn the relative distance bound into a bound on the Hamming distance
  have hrel' : (δᵣ(curve u z, w) : ℝ≥0) ≤ (δ : ℝ≥0) := by
    exact_mod_cast hrel

  have hdist' : Δ₀(curve u z, w) ≤ Nat.floor ((δ : ℝ≥0) * (Fintype.card (Fin n))) := by
    have :=
      (Code.pairRelDist_le_iff_pairDist_le
            (ι := Fin n) (F := F) (u := curve u z) (v := w) (δ := (δ : ℝ≥0))).1 hrel'
    simpa using this

  have hdist : Δ₀(curve u z, w) ≤ bwError δ n := by
    simpa [bwError, Fintype.card_fin] using hdist'

  have hw_eq : w = p.eval ∘ ωs := by
    ext i
    -- `hpw : (ReedSolomon.evalOnPoints ωs) p = w`
    simpa [ReedSolomon.evalOnPoints] using congrArg (fun f => f i) hpw.symm

  simpa [hw_eq] using hdist

theorem bw_decoder_eq_some_of_mem_coeffs {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0}
  (hn : deg ≤ n)
  (hδ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2)
  {u : Fin l → Fin n → F} {z : F}
  (hz : z ∈ coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)) :
  ∃ p : Polynomial F,
    p ∈ Polynomial.degreeLT F deg ∧
    BerlekampWelch.decoder (bwError δ n) deg (fun i => ωs i) (curve u z) = some p := by
  classical
  obtain ⟨p, hpLT, hdist⟩ :=
    exists_poly_of_mem_coeffs_of_close_proximity_curve (ωs := ωs) (deg := deg) (δ := δ)
      (u := u) (z := z) hz
  by_cases hdeg : deg = 0
  · subst hdeg
    have hp0 : p = 0 := by
      have hpdeg : p.degree < (0 : ℕ) := (Polynomial.mem_degreeLT).1 hpLT
      by_contra hp0
      have : p.natDegree < (0 : ℕ) :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdeg
      exact Nat.not_lt_zero _ this
    subst hp0
    refine ⟨0, hpLT, ?_⟩
    have hzero : (0 : Polynomial F).eval ∘ (fun i : Fin n => ωs i) = (0 : Fin n → F) := by
      funext i
      simp
    have hdist0 : Δ₀(curve u z, (0 : Fin n → F)) ≤ bwError δ n := by
      simpa [hzero] using hdist
    have hnorm : ‖curve u z‖₀ ≤ bwError δ n := by
      simpa [hammingDist_zero_right] using hdist0
    simp [BerlekampWelch.decoder, hnorm]
  ·
    have hdeg_pos : 0 < deg := Nat.pos_of_ne_zero hdeg
    have hpdeg : p.degree < (deg : ℕ) := (Polynomial.mem_degreeLT).1 hpLT
    have hp_natDegree : p.natDegree < deg := by
      by_cases hp0 : p = 0
      · subst hp0
        simpa using hdeg_pos
      · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdeg
    have he : 2 * bwError δ n < n - deg + 1 :=
      bwError_unique_decoding_ineq (deg := deg) (δ := δ) hδ
    have h_inj : Function.Injective (fun i : Fin n => ωs i) := by
      simpa using ωs.injective
    have hdec :
        BerlekampWelch.decoder (bwError δ n) deg (fun i : Fin n => ωs i) (curve u z) = some p :=
      BerlekampWelch.decoder_eq_some (e := bwError δ n) (k := deg)
        (ωs := fun i : Fin n => ωs i) (f := curve u z) (p := p)
        he hn h_inj hp_natDegree hdist
    exact ⟨p, hpLT, hdec⟩

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

open scoped BigOperators in
theorem exists_v_RS_mismatch_of_large_agreement_set_of_deg_le_n {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0}
  (hn : deg ≤ n)
  (hδ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2)
  {u : Fin l → Fin n → F}
  (hS : n * l < (coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)).card) :
  ∃ v : Fin l → Fin n → F,
    (∀ i, v i ∈ RSCodeFinset ωs deg) ∧
    (curveMismatchSet u v).card ≤ δ * n := by
  classical
  by_cases hl : l = 0
  · subst hl
    refine ⟨u, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · simp [curveMismatchSet]
  ·
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl
    have hnpos : 0 < n := Nat.pos_of_neZero n
    haveI : Finite F := by infer_instance

    -- show δ ≤ 1 in ℚ≥0
    have hδ_le_one : (δ : ℚ≥0) ≤ 1 := by
      have h₁ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2 := hδ
      have h₂ : (1 - (deg : ℚ≥0) / n) / 2 ≤ (1 - (deg : ℚ≥0) / n) := by
        simpa using
          (div_le_self (a := (1 - (deg : ℚ≥0) / n)) (b := (2 : ℚ≥0)) (by simp) (by norm_num))
      have h₃ : (1 - (deg : ℚ≥0) / n) ≤ (1 : ℚ≥0) := by
        simpa using
          (sub_le_self (a := (1 : ℚ≥0)) (b := (deg : ℚ≥0) / n) (by simp))
      exact le_trans h₁ (le_trans h₂ h₃)

    -- δ ≤ δ₀ 0 3 (as real)
    have hδ' : (δ : ℝ) ≤ ProximityGap.δ₀ (rho := (0 : ℚ≥0)) (m := 3) := by
      simp [ProximityGap.δ₀]
      exact_mod_cast hδ_le_one

    -- build hS' for the big lemma: with rho=0, LHS collapses to 0, so it suffices that card S > 0
    have hSposNat : 0 < (coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)).card := by
      exact lt_trans (Nat.mul_pos hnpos hlpos) hS
    have hSposReal : (0 : ℝ) < (coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)).card := by
      exact_mod_cast hSposNat
    have hExp : ((3 / 2 : ℚ) : ℝ) ≠ 0 := by
      norm_num
    have hLHS0 : (((1 + 1 / (2 * (3 : ℕ))) ^ 7 * (3 : ℕ) ^ 7) /
        (3 * (Real.rpow (0 : ℚ≥0) (3 / 2 : ℚ))) * (n : ℕ) ^ 2 * l : ℝ) = 0 := by
      simp [Real.zero_rpow hExp]
    have hS' : (((1 + 1 / (2 * (3 : ℕ))) ^ 7 * (3 : ℕ) ^ 7) /
        (3 * (Real.rpow (0 : ℚ≥0) (3 / 2 : ℚ))) * (n : ℕ) ^ 2 * l : ℝ)
        < (coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)).card := by
      simpa [hLHS0] using hSposReal

    -- apply the (imported) correlated agreement lemma
    rcases (large_agreement_set_on_curve_implies_correlated_agreement' (F := F) (n := n)
      (l := l) (m := 3) (rho := (0 : ℚ≥0)) (δ := δ)
      (hm := by decide) (V := RSCodeFinset ωs deg) (hδ := hδ') (u := u) hS') with ⟨v, hv⟩

    refine ⟨v, ?_, ?_⟩
    · intro i
      exact (hv i).1
    ·
      -- Let A be the agreement set
      let A : Finset (Fin n) := {x : Fin n | ∀ i : Fin l, u i x = v i x}

      -- Extract a lower bound on |A|
      let i0 : Fin l := ⟨0, hlpos⟩
      have hagree : (1 - δ) * (n : ℚ≥0) ≤ (A.card : ℚ≥0) := by
        simpa [A] using (hv i0).2

      -- Relate |A| and the mismatch set by partitioning univ
      have hcard_partition_nat : A.card + (curveMismatchSet u v).card = n := by
        have h :=
          (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
            (p := fun x : Fin n => ∀ i : Fin l, u i x = v i x))
        -- simplify filters to A and curveMismatchSet
        simpa [A, curveMismatchSet, funext_iff] using h

      have hcard_partition : (A.card : ℚ≥0) + (curveMismatchSet u v).card = n := by
        exact_mod_cast hcard_partition_nat

      -- Compute n = (1-δ)*n + δ*n
      have hsum : (1 - δ) * (n : ℚ≥0) + δ * (n : ℚ≥0) = n := by
        have h1 : (1 - δ) + δ = (1 : ℚ≥0) := by
          -- (1-δ)+δ = 1 since δ ≤ 1
          simpa [add_comm, add_left_comm, add_assoc] using (tsub_add_cancel_of_le hδ_le_one)
        calc
          (1 - δ) * (n : ℚ≥0) + δ * (n : ℚ≥0)
              = ((1 - δ) + δ) * (n : ℚ≥0) := by
                  ring
          _ = (1 : ℚ≥0) * (n : ℚ≥0) := by
                  simp [h1]
          _ = n := by
                  simp

      -- Add δ*n to hagree and rewrite using hsum
      have hn_le : (n : ℚ≥0) ≤ (A.card : ℚ≥0) + δ * (n : ℚ≥0) := by
        have h' : (1 - δ) * (n : ℚ≥0) + δ * (n : ℚ≥0) ≤ (A.card : ℚ≥0) + δ * (n : ℚ≥0) := by
          exact add_le_add hagree le_rfl
        simpa [hsum] using h'

      -- Replace n by A.card + mismatch.card and cancel A.card
      have hmis : (curveMismatchSet u v).card ≤ δ * (n : ℚ≥0) := by
        have hn_le' : (A.card : ℚ≥0) + (curveMismatchSet u v).card ≤ (A.card : ℚ≥0) + δ * (n : ℚ≥0) := by
          simpa [hcard_partition] using hn_le
        exact (add_le_add_iff_left (A.card : ℚ≥0)).1 hn_le'

      simpa using hmis


theorem mem_RSCodeFinset_of_n_le_deg {ωs : Fin n ↪ F} {deg : ℕ} (hdeg : n ≤ deg) (w : Fin n → F) : w ∈ RSCodeFinset (n := n) (F := F) ωs deg := by
  classical
  refine (mem_RSCodeFinset_iff_mem_RSCode (n := n) (F := F) (ωs := ωs) (deg := deg) (w := w)).2 ?_
  -- Interpolating polynomial
  let p : Polynomial F := Lagrange.interpolate (s := (Finset.univ : Finset (Fin n)))
      (v := fun i : Fin n => ωs i) w
  have hinj : Set.InjOn (fun i : Fin n => ωs i) (Finset.univ : Finset (Fin n)) := by
    intro x hx y hy hxy
    exact ωs.injective hxy
  have hp_eval : ∀ i : Fin n, p.eval (ωs i) = w i := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin n)))
      (v := fun i : Fin n => ωs i) (r := w) (i := i) hinj (by simp)
    simpa [p] using this
  have hp_deg_lt_n : p.degree < (n : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin n)))
      (v := fun i : Fin n => ωs i) (r := w) hinj
    simpa [p] using this
  have hn_le_deg : (n : WithBot ℕ) ≤ deg := by
    exact_mod_cast hdeg
  have hp_deg_lt_deg : p.degree < (deg : WithBot ℕ) := lt_of_lt_of_le hp_deg_lt_n hn_le_deg
  have hp_mem_degLT : p ∈ Polynomial.degreeLT F deg := (Polynomial.mem_degreeLT).2 hp_deg_lt_deg
  refine ⟨p, hp_mem_degLT, ?_⟩
  ext i
  simpa [ReedSolomon.evalOnPoints, hp_eval i]

theorem exists_v_RS_mismatch_of_large_agreement_set {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0}
  (hδ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2)
  {u : Fin l → Fin n → F}
  (hS : n * l < (coeffs_of_close_proximity_curve δ u (RSCodeFinset ωs deg)).card) :
  ∃ v : Fin l → Fin n → F,
    (∀ i, v i ∈ RSCodeFinset ωs deg) ∧
    (curveMismatchSet u v).card ≤ δ * n := by
  classical
  by_cases hn : deg ≤ n
  ·
    exact
      exists_v_RS_mismatch_of_large_agreement_set_of_deg_le_n (ωs := ωs) (deg := deg) (δ := δ)
        hn hδ hS
  ·
    have hdeg : n ≤ deg := le_of_not_ge hn
    refine ⟨u, ?_, ?_⟩
    · intro i
      exact mem_RSCodeFinset_of_n_le_deg (ωs := ωs) (deg := deg) hdeg (u i)
    ·
      have hEmpty : curveMismatchSet u u = (∅ : Finset (Fin n)) := by
        ext x
        simp [curveMismatchSet]
      simpa [hEmpty] using (zero_le (δ * n))

theorem exists_correlated_curve_of_large_agreement_set {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0}
  (hδ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2)
  {u : Fin l → Fin n → F}
  (hS : n * l < (coeffs_of_close_proximity_curve δ u (RSCodeFinset (n := n) (F := F) ωs deg)).card)
  :
  ∃ v : Fin l → Fin n → F,
    (∀ i, v i ∈ RSCodeFinset (n := n) (F := F) ωs deg) ∧
    (∀ z, δᵣ(curve u z, curve v z) ≤ δ) ∧
    (curveMismatchSet u v).card ≤ δ * n := by
  classical
  rcases
      exists_v_RS_mismatch_of_large_agreement_set (n := n) (F := F) (l := l) (ωs := ωs)
        (deg := deg) (δ := δ) hδ hS with
    ⟨v, hvRS, hm⟩
  have hclose : ∀ z : F, δᵣ(curve u z, curve v z) ≤ δ :=
    curve_relDist_le_of_curveMismatchSet_card_le (n := n) (F := F) (l := l) (δ := δ)
      (u := u) (v := v) hm
  exact ⟨v, hvRS, hclose, hm⟩

theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ} {ωs : Fin n ↪ F} {deg : ℕ} {δ : ℚ≥0}
  (hδ : δ ≤ (1 - (deg : ℚ≥0) / n) / 2)
  {u : Fin l → Fin n → F}
  (hS : n * l < (coeffs_of_close_proximity_curve δ u (RSCodeFinset (n := n) (F := F) ωs deg)).card)
  :
  coeffs_of_close_proximity_curve δ u (RSCodeFinset (n := n) (F := F) ωs deg) = (Finset.univ : Finset F)
  ∧
  ∃ (v : Fin l → Fin n → F),
    (∀ i, v i ∈ RSCodeFinset (n := n) (F := F) ωs deg) ∧
    (∀ z, δᵣ(curve u z, curve v z) ≤ δ) ∧
    (curveMismatchSet u v).card ≤ δ * n := by
  classical
  rcases
      exists_correlated_curve_of_large_agreement_set (n := n) (F := F) (l := l) (ωs := ωs)
        (deg := deg) (δ := δ) (hδ := hδ) (u := u) (hS := hS) with
    ⟨v, hv, hclose, hmismatch⟩
  constructor
  ·
    exact
      coeffs_of_close_proximity_curve_eq_univ_of_exists_v (n := n) (F := F) (l := l) (ωs := ωs)
        (deg := deg) (δ := δ) (u := u) (v := v) hv hclose
  ·
    refine ⟨v, ?_⟩
    exact ⟨hv, hclose, hmismatch⟩


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
