/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
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

theorem agree_le_card_div [DecidableEq ι] [Fintype ι] [DecidableEq F]
  (μ : ι → Set.Icc (0 : ℚ) 1) (w v : ι → F) :
  agree μ w v ≤ (Finset.card ({i : ι | w i = v i} : Finset ι) : ℝ) / (Fintype.card ι) := by
  classical
  simp [ProximityGap.WeightedAgreement.agree, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- bound the sum of weights by the sum of `1`
  calc
    (∑ i with w i = v i, (↑↑(μ i) : ℝ))
        ≤ ∑ i with w i = v i, (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact_mod_cast (μ i).2.2
    _ = (#{i | w i = v i} : ℝ) := by
          -- sum of ones equals the cardinality of the filtered finset
          simp

theorem agree_set_ge_exists [Fintype ι] [DecidableEq F]
  (μ : ι → Set.Icc (0 : ℚ) 1)
  {w : ι → F} {V : Finset (ι → F)} [Nonempty V] {α : ℝ≥0} :
  agree_set μ w V ≥ α → ∃ v ∈ V, agree μ w v ≥ α := by
  intro hα
  classical
  -- Unfold `agree_set` as a `Finset.max'` over the image.
  dsimp [agree_set] at hα
  set S : Finset ℝ := Finset.image (agree μ w) V
  have hS : S.Nonempty := by
    -- `V` is nonempty by typeclass, hence so is its image.
    rcases (inferInstance : Nonempty V) with ⟨v⟩
    refine ⟨agree μ w v.1, ?_⟩
    exact Finset.mem_image.2 ⟨v.1, v.2, rfl⟩
  have hmem : S.max' hS ∈ S := Finset.max'_mem S hS
  rcases (Finset.mem_image.1 hmem) with ⟨v, hvV, hvEq⟩
  refine ⟨v, hvV, ?_⟩
  -- Rewrite the lower bound using the fact that the max is achieved at `v`.
  have : (S.max' hS) ≥ (α : ℝ) := hα
  -- `hvEq` is `agree μ w v = S.max' hS`.
  -- Rewrite `this` to get the desired inequality.
  simpa [hvEq] using this

noncomputable def bivarCoeffPoly {F : Type} [Semiring F] {l : ℕ}
    (P : Polynomial (Polynomial F)) (j : Fin (l + 2)) : Polynomial F :=
  ∑ t ∈ P.support, Polynomial.monomial t ((P.coeff t).coeff j.1)

theorem bivarCoeffPoly_coeff {F : Type} [Semiring F] {l : ℕ} (P : Polynomial (Polynomial F)) (j : Fin (l + 2)) (t : ℕ) :
  (bivarCoeffPoly (l := l) P j).coeff t = (P.coeff t).coeff j.1 := by
  classical
  -- Expand the definition and compute coefficients termwise.
  -- `Finset.sum_ite_eq` picks out the unique monomial contributing to `coeff t`.
  simp [bivarCoeffPoly, Polynomial.coeff_sum, Polynomial.coeff_monomial, Finset.sum_ite_eq]
  intro ht
  simp [ht]

theorem bivarCoeffPoly_degree_le {F : Type} [Semiring F] {l : ℕ} (P : Polynomial (Polynomial F)) (j : Fin (l + 2)) :
  (bivarCoeffPoly (l := l) P j).degree ≤ P.degree := by
  classical
  have hsupp : (bivarCoeffPoly (l := l) P j).support ⊆ P.support := by
    intro t ht
    have hcoeff : (bivarCoeffPoly (l := l) P j).coeff t ≠ 0 :=
      (Polynomial.mem_support_iff).1 ht
    have hinner : (P.coeff t).coeff j.1 ≠ 0 := by
      simpa [bivarCoeffPoly_coeff (l := l) P j t] using hcoeff
    have hPt : P.coeff t ≠ 0 := by
      intro hzero
      apply hinner
      simpa [hzero]
    exact (Polynomial.mem_support_iff).2 hPt
  exact Polynomial.degree_mono hsupp

noncomputable def bivariatePolyOfD
    {F : Type} [Field F] [DecidableEq F]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {l : ℕ} (u : Fin (l + 2) → ι → F) (domain : ι ↪ F) (D : Finset ι) : F[Z][X] :=
  ∑ j : Fin (l + 2),
    Polynomial.C ((Polynomial.X : Polynomial F) ^ j.1) *
      (Lagrange.interpolate D domain (u j)).map Polynomial.C

theorem bivariatePolyOfD_coeff {F : Type} [Field F] [DecidableEq F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {l : ℕ} (u : Fin (l + 2) → ι → F) (domain : ι ↪ F) (D : Finset ι) (t : ℕ) :
  (bivariatePolyOfD (u := u) domain D).coeff t =
    ∑ j : Fin (l + 2),
      ((Polynomial.X : Polynomial F) ^ j.1) *
        Polynomial.C ((Lagrange.interpolate D domain (u j)).coeff t) := by
  classical
  unfold bivariatePolyOfD
  -- push `coeff` through the finite sum and simplify each summand
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map]

theorem bivariatePolyOfD_degreeX_le {F : Type} [Field F] [DecidableEq F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {l : ℕ} (u : Fin (l + 2) → ι → F) (domain : ι ↪ F) (D : Finset ι) :
  Polynomial.Bivariate.degreeX (bivariatePolyOfD (u := u) domain D) ≤ l + 1 := by
  classical
  unfold Polynomial.Bivariate.degreeX
  refine Finset.sup_le ?_
  intro t ht
  -- expand the coefficient of `X^t` using the provided lemma
  rw [bivariatePolyOfD_coeff (u := u) (domain := domain) (D := D) (t := t)]
  -- bound natDegree of the finite sum by bounding each summand
  refine
    (Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin (l + 2))))
      (f := fun j : Fin (l + 2) =>
        ((Polynomial.X : Polynomial F) ^ j.1) *
          Polynomial.C ((Lagrange.interpolate D domain (u j)).coeff t))
      (n := l + 1) ?_)
  intro j hj
  have hj' : (j : ℕ) ≤ l + 1 := by
    apply Nat.le_of_lt_succ
    -- `j.is_lt : (j:ℕ) < l+2`
    simpa [Nat.add_assoc] using (show (j : ℕ) < l + 2 from j.2)
  -- bound natDegree of the product
  calc
    Polynomial.natDegree
        (((Polynomial.X : Polynomial F) ^ j.1) *
          Polynomial.C ((Lagrange.interpolate D domain (u j)).coeff t))
        ≤
        Polynomial.natDegree ((Polynomial.X : Polynomial F) ^ j.1) +
          Polynomial.natDegree (Polynomial.C ((Lagrange.interpolate D domain (u j)).coeff t)) :=
      Polynomial.natDegree_mul_le
    _ = j.1 + 0 := by
      -- avoid simp expanding the `Lagrange.interpolate` coefficient
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
    _ = j.1 := by simp
    _ ≤ l + 1 := hj'

theorem bivariatePolyOfD_degree_lt_card {F : Type} [Field F] [DecidableEq F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {l : ℕ} (u : Fin (l + 2) → ι → F) (domain : ι ↪ F) (D : Finset ι) :
  (bivariatePolyOfD (u := u) domain D).degree < (D.card : WithBot ℕ) := by
  classical
  unfold bivariatePolyOfD
  refine lt_of_le_of_lt (by
    -- bound the degree of a finite sum by the supremum of the degrees
    simpa using
      (Polynomial.degree_sum_le (s := (Finset.univ : Finset (Fin (l + 2))))
        (f := fun j : Fin (l + 2) =>
          Polynomial.C ((Polynomial.X : Polynomial F) ^ j.1) *
            (Lagrange.interpolate D domain (u j)).map Polynomial.C))) ?_
  -- show each summand has degree `< D.card`
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe (D.card))).2 ?_
  intro j hj
  -- `simp` has reduced the goal to the degree bound for the Lagrange interpolant
  simpa using
    (Lagrange.degree_interpolate_lt (s := D) (v := (domain : ι → F)) (r := u j)
      (domain.injective.injOn))

noncomputable def curveEval {F : Type} [Semiring F] {ι : Type} [Fintype ι]
    {l : ℕ} (u : Fin (l + 2) → ι → F) (z : F) : ι → F :=
  fun i => ∑ j : Fin (l + 2), z ^ j.1 * u j i

theorem curve_codeword_extraction_common_agree_points [DecidableEq ι] [Fintype ι] [Nonempty ι] [DecidableEq F] [Field F] [Fintype F]
  {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1} {M m : ℕ} (hm : 3 ≤ m) {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  (p : F → Polynomial F) →
  (hpdeg : ∀ z ∈ S, (p z).degree < deg) →
  (hpagree_card : ∀ z ∈ S,
    (α : ℝ) ≤ (Finset.card ({i : ι | curveEval u z i = (p z).eval (domain i)} : Finset ι) : ℝ)
      / (Fintype.card ι)
    ) →
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS : S.card >
    max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
        ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)) →
  ∃ (S' : Finset F) (D : Finset ι),
    S' ⊆ S ∧
    S'.card > l + 1 ∧
    S'.card ≥ (M * Fintype.card ι + 1) * (l + 1) ∧
    D.card = deg ∧
    (∀ z ∈ S', ∀ i ∈ D, curveEval u z i = (p z).eval (domain i)) := by
  -- Deep extraction/combinatorial-geometry lemma.
  -- 
  -- **Goal (conceptual):** From a large set of parameters `S` and for each `z ∈ S` a low-degree polynomial `p z` that agrees with the curve word `curveEval u z` on an `α` fraction of coordinates, extract:
  -- - a large subset `S' ⊆ S`, and
  -- - a fixed set of coordinates `D : Finset ι` of size `deg`,
  -- so that **every** `p z` (for `z ∈ S'`) matches the curve on **all** coordinates in `D`.
  -- 
  -- This is the curve analogue of the “find many x-points with large matching subsets” stage in BCIKS20 Section 5 (Claims 5.10–5.11), but tailored to degree-`(l+1)` curves.
  -- 
  -- **Why this is useful:** Once we have such a common `D` of size `deg`, each polynomial `p z` is uniquely determined by its evaluations on `domain '' D` (since `p z` has `degree < deg`). This lets us reconstruct a bivariate `P : F[Z][X]` of `Z`-degree ≤ `l+1` by Lagrange interpolation on the `u j` restricted to `D`, and then conclude `P(z, X) = p z` for all `z ∈ S'`.
  -- 
  -- **Key proof ingredients (expected):**
  -- - Use `hpagree_card` to interpret agreement as distance within Johnson radius (`hα` ensures we are in the GS / Johnson regime).
  -- - Invoke the Guruswami–Sudan / proximity-gap machinery from `ArkLib.Data.CodingTheory.ProximityGap.BCIKS20` to show that many `p z` must coincide on a large common set of evaluation points.
  -- - Use the `hS` bound: the left term (∝ `m^7 * |ι|^2 * (l+1) / sqrtRate^3`) supports the GS counting/list-size arguments; the right term supports the `(M*|ι|+1)*(l+1)` lower bound needed later.
  -- 
  -- **Disproof check:** Without the RS/list-decoding structure, such a common `D` would require exponentially large `S` (dependent random choice). The point here is that the RS/list-decoding constraints + GS machinery give this with only polynomial-sized `S`.
  sorry

theorem exists_poly_of_mem_RS_code [Fintype ι] [Field F]
  {domain : ι ↪ F} {deg : ℕ} {v : ι → F} :
  v ∈ ReedSolomon.code domain deg →
    ∃ p : Polynomial F, p.degree < deg ∧ (fun i => p.eval (domain i)) = v := by
  intro hv
  classical
  unfold ReedSolomon.code at hv
  rcases (Submodule.mem_map.mp hv) with ⟨p, hp, hpv⟩
  refine ⟨p, ?_, ?_⟩
  · -- degree bound
    -- hp : p ∈ Polynomial.degreeLT F deg
    simpa [Polynomial.mem_degreeLT] using hp
  · -- evaluation equality
    -- hpv : ReedSolomon.evalOnPoints domain p = v
    -- simplify evalOnPoints
    simpa [ReedSolomon.evalOnPoints] using hpv

theorem mem_S_iff_agree_set_ge [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0} :
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  ∀ {z : F}, z ∈ S ↔ agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α := by
  classical
  intro z
  simp

theorem mem_finCarrier_iff_mem_RS_code [Fintype ι] [Field F] [Fintype F]
  {domain : ι ↪ F} {deg : ℕ} {v : ι → F} :
  (v ∈ finCarrier domain deg) ↔ (v ∈ ReedSolomon.code domain deg) := by
  classical
  simp [finCarrier]

theorem exists_codeword_of_mem_S [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0} :
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  ∀ {z : F}, z ∈ S → ∃ c : ι → F,
    c ∈ ReedSolomon.code domain deg ∧ agree μ (curveEval u z) c ≥ α := by
  classical
  intro z hz
  -- turn membership in S into the defining predicate
  have hz' : agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α := by
    simpa using hz
  have h := agree_set_ge_exists (μ := μ) (w := curveEval u z) (V := finCarrier domain deg) (α := α) hz'
  rcases h with ⟨c, hcV, hagree⟩
  refine ⟨c, ?_, hagree⟩
  exact (mem_finCarrier_iff_mem_RS_code (domain := domain) (deg := deg) (v := c)).1 hcV

theorem natDegree_coeff_le_degreeX {F : Type} [Semiring F] (P : Polynomial (Polynomial F)) (t : ℕ) :
  (P.coeff t).natDegree ≤ Polynomial.Bivariate.degreeX P := by
  classical
  by_cases ht : t ∈ P.support
  ·
    -- t in support
    have hle : (fun n => (P.coeff n).natDegree) t ≤ P.support.sup (fun n => (P.coeff n).natDegree) :=
      Finset.le_sup (f := fun n => (P.coeff n).natDegree) ht
    simpa [Polynomial.Bivariate.degreeX] using hle
  ·
    have ht0 : P.coeff t = 0 := by
      simpa [Polynomial.notMem_support_iff] using ht
    simp [Polynomial.Bivariate.degreeX, ht0]


theorem bivarCoeffPoly_map_evalRingHom_eval {F : Type} [Field F] {l : ℕ} (P : Polynomial (Polynomial F))
  (hdegZ : Polynomial.Bivariate.degreeX P ≤ l + 1) (z : F) :
  P.map (Polynomial.evalRingHom z) =
    ∑ j : Fin (l + 2), (z ^ j.1) • (bivarCoeffPoly (l := l) P j) := by
  classical
  ext t
  -- reduce to coefficient equality
  simp [Polynomial.coeff_map, bivarCoeffPoly_coeff]
  -- bound the degree of (P.coeff t)
  have hdeg : (P.coeff t).natDegree < l + 2 := by
    have ht : (P.coeff t).natDegree ≤ Polynomial.Bivariate.degreeX P :=
      natDegree_coeff_le_degreeX (P := P) t
    have ht' : (P.coeff t).natDegree ≤ l + 1 := le_trans ht hdegZ
    -- convert ≤ l+1 to < l+2
    exact lt_of_le_of_lt ht' (Nat.lt_succ_self (l + 1))
  -- expand evaluation as a finite sum
  rw [Polynomial.eval_eq_sum_range' (p := P.coeff t) (n := l + 2) hdeg z]
  -- rewrite the `Fin`-sum as a `range` sum
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => z ^ i * (P.coeff t).coeff i) (n := l + 2)]
  -- finish by commutativity
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem bivarCoeffPoly_map_evalRingHom_eval_apply {F : Type} [Field F] {l : ℕ} (P : Polynomial (Polynomial F))
  (hdegZ : Polynomial.Bivariate.degreeX P ≤ l + 1) (z x : F) :
  (P.map (Polynomial.evalRingHom z)).eval x =
    ∑ j : Fin (l + 2), z ^ j.1 * (bivarCoeffPoly (l := l) P j).eval x := by
  classical
  have hpoly := bivarCoeffPoly_map_evalRingHom_eval (P := P) (l := l) hdegZ z
  have h := congrArg (fun p : Polynomial F => p.eval x) hpoly
  -- simplify the RHS using linearity of `Polynomial.eval`
  simpa [Polynomial.eval_finset_sum] using h


theorem bivariatePoly_to_curveCodewords [DecidableEq ι] [Fintype ι] [Nonempty ι] [DecidableEq F] [Field F] [Fintype F]
  {l deg : ℕ} {domain : ι ↪ F} (P : F[Z][X])
  (hdegZ : Polynomial.Bivariate.degreeX P ≤ l + 1)
  (hdegX : P.degree < deg) :
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    (∀ z : F,
      curveEval v z = fun i => (P.map (Polynomial.evalRingHom z)).eval (domain i)) := by
  classical
  let Q : Fin (l + 2) → Polynomial F := fun j => bivarCoeffPoly (l := l) P j
  refine ⟨fun j i => (Q j).eval (domain i), ?_, ?_⟩
  · intro j
    refine ⟨Q j, ?_⟩
    constructor
    ·
      have hdegQ : (Q j).degree < (deg : WithBot ℕ) :=
        lt_of_le_of_lt (bivarCoeffPoly_degree_le (P := P) (j := j)) hdegX
      exact (Polynomial.mem_degreeLT (R := F) (n := deg) (f := Q j)).2 hdegQ
    ·
      rfl
  · intro z
    ext i
    have h :=
      bivarCoeffPoly_map_evalRingHom_eval_apply (P := P) (l := l) (hdegZ := hdegZ) (z := z)
        (x := domain i)
    -- h : (P.map (Polynomial.evalRingHom z)).eval (domain i) = ...
    -- We want curveEval ... = ...
    -- So rewrite using h.symm
    simpa [curveEval, Q] using h.symm


theorem poly_map_C_map_evalRingHom {F : Type} [CommSemiring F]
  (p : Polynomial F) (z : F) :
  ((p.map (Polynomial.C : F →+* Polynomial F)).map (Polynomial.evalRingHom z)) = p := by
  classical
  rw [Polynomial.map_map]
  have hcomp : (Polynomial.evalRingHom z).comp (Polynomial.C : F →+* Polynomial F) = RingHom.id F := by
    ext a
    simp
  simpa [hcomp]


theorem bivariatePolyOfD_map_evalRingHom {F : Type} [Field F] [DecidableEq F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {l : ℕ} (u : Fin (l + 2) → ι → F) (domain : ι ↪ F) (D : Finset ι) (z : F) :
  (bivariatePolyOfD (u := u) domain D).map (Polynomial.evalRingHom z) =
    ∑ j : Fin (l + 2), Polynomial.C (z ^ j.1) * (Lagrange.interpolate D domain (u j)) := by
  classical
  have hcomp : (Polynomial.evalRingHom z).comp Polynomial.C = (RingHom.id F) := by
    ext a
    simp
  -- unfold the definition and simplify
  simp [bivariatePolyOfD, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_map, hcomp]

theorem bivariatePolyOfD_eval {F : Type} [Field F] [DecidableEq F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {l : ℕ} (u : Fin (l + 2) → ι → F) (domain : ι ↪ F) (D : Finset ι) :
  ∀ i ∈ D, ∀ z : F,
    ((bivariatePolyOfD (u := u) domain D).map (Polynomial.evalRingHom z)).eval (domain i)
      = curveEval u z i := by
  classical
  intro i hi z
  -- Rewrite the mapped bivariate polynomial using the provided lemma.
  rw [bivariatePolyOfD_map_evalRingHom (u := u) (domain := domain) (D := D) (z := z)]
  -- Expand the RHS definition *only*.
  simp only [curveEval]
  -- Push `eval` through the finite sum.
  have hsum :
      Polynomial.eval (domain i)
          (∑ j : Fin (l + 2),
            Polynomial.C (z ^ j.1) * Lagrange.interpolate D domain (u j)) =
        ∑ j : Fin (l + 2),
          Polynomial.eval (domain i)
            (Polynomial.C (z ^ j.1) * Lagrange.interpolate D domain (u j)) := by
    simpa using
      (Polynomial.eval_finset_sum (s := (Finset.univ : Finset (Fin (l + 2))))
        (g := fun j : Fin (l + 2) =>
          Polynomial.C (z ^ j.1) * Lagrange.interpolate D domain (u j))
        (x := domain i))
  rw [hsum]
  -- Prove equality term-by-term.
  apply Fintype.sum_congr
  intro j
  have hnode : (Lagrange.interpolate D domain (u j)).eval (domain i) = u j i := by
    simpa using
      (Lagrange.eval_interpolate_at_node (r := u j) (s := D) (v := (domain : ι → F))
        (i := i) (hvs := domain.injective.injOn) (hi := hi))
  calc
    Polynomial.eval (domain i) (Polynomial.C (z ^ j.1) * Lagrange.interpolate D domain (u j))
        = (Polynomial.C (z ^ j.1)).eval (domain i) *
            (Lagrange.interpolate D domain (u j)).eval (domain i) := by
          simp [Polynomial.eval_mul, -Lagrange.interpolate_apply]
    _ = z ^ j.1 * u j i := by
          simp [hnode, -Lagrange.interpolate_apply]

theorem exists_bivariatePoly_of_D [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]
  {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} {domain : ι ↪ F}
  (D : Finset ι) (hD : D.card = deg) :
  ∃ P : F[Z][X],
    Polynomial.Bivariate.degreeX P ≤ l + 1 ∧
    P.degree < deg ∧
    (∀ i ∈ D, ∀ z : F, (P.map (Polynomial.evalRingHom z)).eval (domain i) = curveEval u z i) := by
  classical
  refine ⟨bivariatePolyOfD (u := u) domain D, ?_, ?_, ?_⟩
  · exact bivariatePolyOfD_degreeX_le (u := u) domain D
  · simpa [hD] using (bivariatePolyOfD_degree_lt_card (u := u) domain D)
  · exact bivariatePolyOfD_eval (u := u) domain D


theorem curve_codeword_extraction_matching_poly_polys_unweighted_aux [DecidableEq ι] [Fintype ι] [Nonempty ι] [DecidableEq F] [Field F] [Fintype F]
  {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1} {M m : ℕ} (hm : 3 ≤ m) {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  (p : F → Polynomial F) →
  (hpdeg : ∀ z ∈ S, (p z).degree < deg) →
  (hpagree_card : ∀ z ∈ S,
    (α : ℝ) ≤ (Finset.card ({i : ι | curveEval u z i = (p z).eval (domain i)} : Finset ι) : ℝ)
      / (Fintype.card ι)
    ) →
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS : S.card >
    max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
        ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)) →
  ∃ (S' : Finset F) (P : F[Z][X]),
    S' ⊆ S ∧
    S'.card > l + 1 ∧
    S'.card ≥ (M * Fintype.card ι + 1) * (l + 1) ∧
    Polynomial.Bivariate.degreeX P ≤ l + 1 ∧
    P.degree < deg ∧
    (∀ z ∈ S', (P.map (Polynomial.evalRingHom z)) = p z) := by
  classical
  intro p hpdeg hpagree_card hα hS
  rcases curve_codeword_extraction_common_agree_points (F := F) (ι := ι) (u := u) (deg := deg)
      (domain := domain) (μ := μ) (M := M) (m := m) hm (α := α) p hpdeg hpagree_card hα hS with
    ⟨S', D, hS'sub, hS'card_gt, hS'card_ge, hDcard, hcurve⟩
  rcases exists_bivariatePoly_of_D (F := F) (ι := ι) (u := u) (deg := deg) (domain := domain) D hDcard with
    ⟨P, hdegX, hPdeg, hPeval⟩
  refine ⟨S', P, hS'sub, hS'card_gt, hS'card_ge, hdegX, hPdeg, ?_⟩
  intro z hz
  have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
  have heval : ∀ i : D, (P.map (Polynomial.evalRingHom z)).eval (domain i.1) = (p z).eval (domain i.1) := by
    intro i
    have hi : (i.1 : ι) ∈ D := i.2
    calc
      (P.map (Polynomial.evalRingHom z)).eval (domain i.1)
          = curveEval u z i.1 := hPeval i.1 hi z
      _ = (p z).eval (domain i.1) := hcurve z hz i.1 hi
  have hf : Function.Injective (fun i : D => domain i.1) := by
    intro i j hij
    apply Subtype.ext
    exact domain.injective hij
  have hpz_nat : (p z).natDegree < deg := by
    have hzS : z ∈ ({z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α} : Finset F) :=
      hS'sub hz
    have hpdegz : (p z).degree < deg := hpdeg z hzS
    by_cases hpz : p z = 0
    · simpa [hpz] using hdegpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt (p := p z) (n := deg) hpz).2 hpdegz
  have hPmap_nat : (P.map (Polynomial.evalRingHom z)).natDegree < deg := by
    have hdegmap : (P.map (Polynomial.evalRingHom z)).degree < deg :=
      lt_of_le_of_lt (Polynomial.degree_map_le (p := P) (f := Polynomial.evalRingHom z)) hPdeg
    by_cases hPz : P.map (Polynomial.evalRingHom z) = 0
    · simpa [hPz] using hdegpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt (p := P.map (Polynomial.evalRingHom z)) (n := deg) hPz).2 hdegmap
  have hcard : max (P.map (Polynomial.evalRingHom z)).natDegree (p z).natDegree < Fintype.card D := by
    have hmax : max (P.map (Polynomial.evalRingHom z)).natDegree (p z).natDegree < deg :=
      (max_lt_iff).2 ⟨hPmap_nat, hpz_nat⟩
    have hcard' : max (P.map (Polynomial.evalRingHom z)).natDegree (p z).natDegree < D.card := by
      simpa [hDcard] using hmax
    simpa [Fintype.card_coe] using hcard'
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (p := P.map (Polynomial.evalRingHom z)) (q := p z)
      (f := fun i : D => domain i.1) hf
  · intro i
    simpa using heval i
  · exact hcard

theorem curve_codeword_extraction_matching_poly_polys [DecidableEq ι] [Fintype ι] [Nonempty ι] [DecidableEq F] [Field F] [Fintype F]
  {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1} {M m : ℕ} (hm : 3 ≤ m) {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  (p : F → Polynomial F) →
  (hpdeg : ∀ z ∈ S, (p z).degree < deg) →
  (hpagree : ∀ z ∈ S, agree μ (curveEval u z) (fun i => (p z).eval (domain i)) ≥ α) →
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS : S.card >
    max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
        ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)) →
  ∃ (S' : Finset F) (P : F[Z][X]),
    S' ⊆ S ∧
    S'.card > l + 1 ∧
    S'.card ≥ (M * Fintype.card ι + 1) * (l + 1) ∧
    Polynomial.Bivariate.degreeX P ≤ l + 1 ∧
    P.degree < deg ∧
    (∀ z ∈ S', (P.map (Polynomial.evalRingHom z)) = p z) := by
  classical
  intro p hpdeg hpagree hα hS
  have hpagree_card :
      ∀ z ∈ ({z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α} : Finset F),
        (α : ℝ) ≤
          (Finset.card ({i : ι | curveEval u z i = (p z).eval (domain i)} : Finset ι) : ℝ) /
            (Fintype.card ι) := by
    intro z hz
    have hα_le_agree : (α : ℝ) ≤ agree μ (curveEval u z) (fun i => (p z).eval (domain i)) := by
      simpa using (hpagree z hz)
    have hagree_le_card :
        agree μ (curveEval u z) (fun i => (p z).eval (domain i)) ≤
          (Finset.card ({i : ι | curveEval u z i = (p z).eval (domain i)} : Finset ι) : ℝ) /
            (Fintype.card ι) := by
      simpa using
        (agree_le_card_div μ (curveEval u z) (fun i => (p z).eval (domain i)))
    exact le_trans hα_le_agree hagree_le_card
  simpa using
    (curve_codeword_extraction_matching_poly_polys_unweighted_aux (hm := hm) (u := u) (deg := deg)
      (domain := domain) (μ := μ) (M := M) (m := m) (α := α) p hpdeg hpagree_card hα hS)

theorem curve_codeword_extraction_matching_poly [DecidableEq ι] [Fintype ι] [Nonempty ι] [DecidableEq F] [Field F] [Fintype F]
  {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1} {M m : ℕ} (hm : 3 ≤ m) {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  (c : F → ι → F) →
  (hc : ∀ z, z ∈ S → c z ∈ ReedSolomon.code domain deg ∧ agree μ (curveEval u z) (c z) ≥ α) →
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS :
    S.card >
      max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)
    ) →
  ∃ (S' : Finset F) (P : F[Z][X]),
    S' ⊆ S ∧
    S'.card > l + 1 ∧
    S'.card ≥ (M * Fintype.card ι + 1) * (l + 1) ∧
    Polynomial.Bivariate.degreeX P ≤ l + 1 ∧
    P.degree < deg ∧
    (∀ z ∈ S', (fun i => (P.map (Polynomial.evalRingHom z)).eval (domain i)) = c z) := by
  classical
  intro c hc hα hS

  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}

  have hcS :
      ∀ z, z ∈ S → c z ∈ ReedSolomon.code domain deg ∧ agree μ (curveEval u z) (c z) ≥ α := by
    simpa [S] using hc

  have hS_card :
      S.card >
        max ((1 + 1 / (2 * m : ℝ)) ^ 7 * m ^ 7 * (Fintype.card ι) ^ 2 * (l + 1) /
            (3 * (ReedSolomonCode.sqrtRate deg domain) ^ 3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) /
            (ReedSolomonCode.sqrtRate deg domain).toReal) := by
    simpa [S] using hS

  -- choose representing polynomials for each decoded codeword
  have hexists : ∀ z, z ∈ S →
      ∃ p : Polynomial F, p.degree < deg ∧ (fun i => p.eval (domain i)) = c z := by
    intro z hz
    have hz' : c z ∈ ReedSolomon.code domain deg := (hcS z hz).1
    exact exists_poly_of_mem_RS_code (v := c z) hz'

  -- define a global function picking these polynomials on S
  let pfun : F → Polynomial F := fun z => if hz : z ∈ S then (hexists z hz).choose else 0

  have hpdeg : ∀ z ∈ S, (pfun z).degree < deg := by
    intro z hz
    simpa [pfun, hz] using (hexists z hz).choose_spec.1

  have hpeval : ∀ z ∈ S, (fun i => (pfun z).eval (domain i)) = c z := by
    intro z hz
    simpa [pfun, hz] using (hexists z hz).choose_spec.2

  have hpagree :
      ∀ z ∈ S, agree μ (curveEval u z) (fun i => (pfun z).eval (domain i)) ≥ α := by
    intro z hz
    have hcz : agree μ (curveEval u z) (c z) ≥ α := (hcS z hz).2
    simpa [hpeval z hz] using hcz

  rcases
      curve_codeword_extraction_matching_poly_polys (μ := μ) (domain := domain) (deg := deg)
        (u := u) (l := l) (M := M) (m := m) hm (α := α)
        pfun hpdeg hpagree hα hS_card with
    ⟨S', P, hS'sub, hS'card, hS'card₁, hdegX, hdeg, hmatch⟩

  refine ⟨S', P, ?_, ?_, ?_, hdegX, hdeg, ?_⟩
  · -- subset
    simpa [S] using hS'sub
  · simpa using hS'card
  · simpa using hS'card₁
  · -- matching evaluation
    intro z hzS'
    have hzS : z ∈ S := hS'sub hzS'
    have hPz : (P.map (Polynomial.evalRingHom z)) = pfun z := hmatch z hzS'
    -- rewrite by the polynomial equality and then use the evaluation equality
    calc
      (fun i => (P.map (Polynomial.evalRingHom z)).eval (domain i))
          = (fun i => (pfun z).eval (domain i)) := by
              funext i
              simpa [hPz]
      _ = c z := hpeval z hzS


theorem curve_codeword_extraction [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M m : ℕ} (hm : 3 ≤ m)
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}
  (c : F → ι → F) →
  (hc : ∀ z, z ∈ S → c z ∈ ReedSolomon.code domain deg ∧ agree μ (curveEval u z) (c z) ≥ α) →
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS :
    S.card >
      max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)
    ) →
  ∃ (S' : Finset F) (v : Fin (l + 2) → ι → F),
    S' ⊆ S ∧
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    S'.card > l + 1 ∧
    S'.card ≥ (M * Fintype.card ι + 1) * (l + 1) ∧
    (∀ z ∈ S', curveEval v z = c z) := by
  classical
  intro c hc hα hS
  obtain ⟨S', P, hS'sub, hS'card_gt, hS'card_ge, hdegZ, hdegX, hmatch⟩ :=
    curve_codeword_extraction_matching_poly (u := u) (deg := deg) (domain := domain)
      (μ := μ) (M := M) (m := m) hm (α := α) c hc hα hS
  obtain ⟨v, hv_mem, hv_curve⟩ :=
    bivariatePoly_to_curveCodewords (domain := domain) (deg := deg) (l := l) P hdegZ hdegX
  refine ⟨S', v, hS'sub, hv_mem, hS'card_gt, hS'card_ge, ?_⟩
  intro z hz
  exact (hv_curve z).trans (hmatch z hz)


theorem extract_subset_curve_codewords [DecidableEq ι] [Fintype ι] [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M m : ℕ}
  (hm : 3 ≤ m)
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
  ∃ (S' : Finset F) (v : Fin (l + 2) → ι → F),
    S' ⊆ S ∧
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    S'.card > l + 1 ∧
    S'.card ≥ (M * Fintype.card ι + 1) * (l + 1) ∧
    (∀ z ∈ S',
      agree μ (fun i ↦ ∑ j, z ^ j.1 * u j i)
               (fun i ↦ ∑ j, z ^ j.1 * v j i) ≥ α) := by
  classical
  intro hα hS
  -- re-introduce the abbreviations as local instances/constants
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {z : F | agree_set μ (curveEval u z) (finCarrier domain deg) ≥ α}

  have hα' : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α := by
    simpa [sqrtRate] using hα
  have hS' : S.card >
      max ((1 + 1 / (2 * m : ℝ)) ^ 7 * m ^ 7 * (Fintype.card ι) ^ 2 * (l + 1) /
            (3 * sqrtRate ^ 3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal) := by
    -- `S` is definitional equal to the set used in the statement
    simpa [S, sqrtRate, curveEval] using hS

  -- choose a codeword for each `z ∈ S`
  let c : F → ι → F := fun z =>
    if hz : z ∈ S then
      Classical.choose (exists_codeword_of_mem_S (u := u) (deg := deg) (domain := domain)
        (μ := μ) (α := α) (z := z) hz)
    else 0
  have hc : ∀ z, z ∈ S → c z ∈ ReedSolomon.code domain deg ∧
      agree μ (curveEval u z) (c z) ≥ α := by
    intro z hz
    have hspec := Classical.choose_spec
      (exists_codeword_of_mem_S (u := u) (deg := deg) (domain := domain)
        (μ := μ) (α := α) (z := z) hz)
    simpa [c, hz] using hspec

  rcases curve_codeword_extraction (u := u) (deg := deg) (domain := domain)
      (μ := μ) (M := M) (m := m) hm (α := α) c hc hα' hS' with
    ⟨S', v, hS'sub, hv, hcard, hcard' , hcv⟩

  refine ⟨S', v, ?_, hv, hcard, hcard', ?_⟩
  · -- `S' ⊆ S`
    simpa [S, curveEval] using hS'sub
  · intro z hz
    have hzS : z ∈ S := hS'sub hz
    have hagree : agree μ (curveEval u z) (c z) ≥ α := (hc z hzS).2
    have hcz : c z = curveEval v z := (hcv z hz).symm
    simpa [curveEval, hcz] using hagree


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

theorem weighted_correlated_agreement_for_parameterized_curves' [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
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
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := by
  classical
  intro hα hS
  obtain ⟨S', v, hS'sub, hv, hS'card_gt, hS'card_ge, hS'agree⟩ :=
    extract_subset_curve_codewords (F := F) (ι := ι) (l := l) (u := u)
      (deg := deg) (domain := domain) (μ := μ) (M := M) (m := m) hm (α := α) hα hS
  refine ⟨v, hv, ?_⟩
  -- use correlated agreement lemma
  have hcorr :=
    sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
      (k := k) (l := l) (u := u) (deg := deg) (domain := domain)
      (μ := μ) (α := α) (M := M) hμ hv (S' := S') hS'card_gt hS'card_ge
  exact hcorr (by
    intro z hz
    simpa using hS'agree z hz)


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
end

end WeightedAgreement

end BCIKS20ProximityGapSection7

end ProximityGap
