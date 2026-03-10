/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Card
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

def WCA_affineSpace {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]
    {l : ℕ} (u : Fin (l + 2) → ι → F) : AffineSubspace F (ι → F) :=
  Affine.affineSubspaceAtOrigin (F := F) (A := F) (origin := u 0) (directions := Fin.tail u)

noncomputable abbrev WCA_bound (ι F : Type) [Fintype ι] [Fintype F]
    (sr : ℝ≥0) (M m : ℕ) : ℝ :=
  max
    (((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2) / ((3 * sr^3) * Fintype.card F))
    (((max (2 * m + 3) 23) * (M * Fintype.card ι + 1)) / (sr * Fintype.card F))

def WCA_good {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]
    (μ : ι → Set.Icc (0 : ℚ) 1) (domain : ι ↪ F) (deg : ℕ) (α : ℝ≥0) : (ι → F) → Prop :=
  fun x => agree_set μ x (finCarrier domain deg) ≥ α

theorem agree_le_one {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [DecidableEq F]
  (μ : ι → Set.Icc (0 : ℚ) 1) (u v : ι → F) :
  agree μ u v ≤ (1 : ℝ) := by
  classical
  unfold agree
  let s : Finset ι := { i : ι | u i = v i }
  have hμle : ∀ i : ι, (μ i).1 ≤ (1 : ℚ) := by
    intro i
    exact (μ i).2.2
  have hsumQ : (∑ i ∈ s, (μ i).1) ≤ (Fintype.card ι : ℚ) := by
    have h1 : (∑ i ∈ s, (μ i).1) ≤ (∑ i ∈ s, (1 : ℚ)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hμle i
    have hcard : s.card ≤ Fintype.card ι := by
      simpa using (Finset.card_le_univ s)
    calc
      (∑ i ∈ s, (μ i).1) ≤ (∑ i ∈ s, (1 : ℚ)) := h1
      _ = (s.card : ℚ) := by
        simp
      _ ≤ (Fintype.card ι : ℚ) := by
        exact_mod_cast hcard
  have hsumR : (↑(∑ i ∈ s, (μ i).1) : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hsumQ
  have hpos : 0 ≤ (1 / (Fintype.card ι : ℝ)) := by
    positivity
  have hmul : (1 / (Fintype.card ι : ℝ)) * (↑(∑ i ∈ s, (μ i).1) : ℝ)
      ≤ (1 / (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ) :=
    mul_le_mul_of_nonneg_left hsumR hpos
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  calc
    1 / (Fintype.card ι : ℝ) * (↑(∑ i with u i = v i, (μ i).1) : ℝ)
        = 1 / (Fintype.card ι : ℝ) * (↑(∑ i ∈ s, (μ i).1) : ℝ) := by
            simp [s]
    _ ≤ 1 / (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) := hmul
    _ = (1 : ℝ) := by
        simpa using (one_div_mul_cancel hcard_ne)


theorem agree_set_le_one {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [DecidableEq F]
  (μ : ι → Set.Icc (0 : ℚ) 1) (u : ι → F)
  (V : Finset (ι → F)) [Nonempty V] :
  agree_set μ u V ≤ (1 : ℝ) := by
  classical
  unfold agree_set
  let S : Finset ℝ := Finset.image (agree μ u) V
  have hS : S.Nonempty := by
    rcases (show Nonempty V from inferInstance) with ⟨w⟩
    refine ⟨agree μ u w.1, ?_⟩
    exact Finset.mem_image.2 ⟨w.1, w.2, rfl⟩
  have hgoal : S.max' hS ≤ (1 : ℝ) := by
    refine (Finset.max'_le_iff (s := S) (H := hS) (x := (1 : ℝ))).2 ?_
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨w, hwV, rfl⟩
    simpa using (agree_le_one μ u w)
  simpa [S] using hgoal


instance instNonempty_WCA_affineSpace {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]
    {l : ℕ} (u : Fin (l + 2) → ι → F) : Nonempty (WCA_affineSpace u) := by
  classical
  -- `WCA_affineSpace u` is defined via `AffineSubspace.mk'`, hence nonempty.
  simpa [WCA_affineSpace, Affine.affineSubspaceAtOrigin] using
    (Affine.instNonemptyAffineSubspace_mk' (F := F) (V := (ι → F)) (p := u 0)
      (direction := Submodule.span F (Finset.univ.image (Fin.tail u))))

theorem mu_set_mono [Fintype ι] [DecidableEq ι]
  (μ : ι → Set.Icc (0 : ℚ) 1) {s t : Finset ι} :
  s ⊆ t → mu_set μ s ≤ mu_set μ t := by
  intro hst
  classical
  unfold mu_set
  -- compare the sums
  have hsum : (∑ i ∈ s, (μ i).1) ≤ (∑ i ∈ t, (μ i).1) := by
    -- use monotonicity of sum over subsets, weights are nonnegative
    refine Finset.sum_le_sum_of_subset_of_nonneg hst ?_
    intro i hi ht
    -- show 0 ≤ (μ i).1
    exact (μ i).2.1
  have hscalar : 0 ≤ (1 / (Fintype.card ι : ℝ)) := by
    positivity
  -- multiply inequality by nonnegative scalar
  -- note: `hsum` is in ℚ, coerces to ℝ
  have := (mul_le_mul_of_nonneg_left (show (↑(∑ i ∈ s, (μ i).1) : ℝ) ≤ (↑(∑ i ∈ t, (μ i).1) : ℝ) from by
      exact_mod_cast hsum) hscalar)
  -- simplify
  simpa [mul_assoc] using this

theorem sum_ite_const_eq_card_subtype_mul {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (c : ENNReal) :
  (∑ a, (if P a then c else 0)) = (Fintype.card {a : α // P a} : ENNReal) * c := by
  classical
  calc
    (∑ a : α, (if P a then c else 0))
        = (Finset.univ.sum fun a : α => if P a then c else 0) := by
            simp
    _ = (Finset.univ.filter P).sum (fun _ : α => c) := by
            simpa using
              (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := P) (f := fun _ : α => c)).symm
    _ = ((Finset.univ.filter P).card : ENNReal) * c := by
            simpa [Nat.nsmul_eq_mul] using (Finset.sum_const (s := Finset.univ.filter P) c)
    _ = (Fintype.card {a : α // P a} : ENNReal) * c := by
            simpa [Fintype.card_subtype]

theorem pr_uniformOfFintype_eq_card {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) [DecidablePred P] :
  Pr_{let x ←$ᵖ α}[P x] = ((Fintype.card {x : α // P x} : ENNReal) / (Fintype.card α)) := by
  classical
  change (P <$> ($ᵖ α)) True =
      ((Fintype.card { x : α // P x } : ENNReal) / (Fintype.card α))
  -- Expand the probability computation for the uniform distribution.
  simp [PMF.monad_map_eq_map, PMF.map_apply, div_eq_mul_inv]
  -- Count the number of satisfying elements.
  simpa using
    (sum_ite_const_eq_card_subtype_mul (α := α) (P := P)
      (c := (↑(Fintype.card α) : ENNReal)⁻¹))

theorem wca_exists_base_with_many_good_on_line {F V : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype V] [DecidableEq V]
  (U : AffineSubspace F V) [Nonempty U]
  (Good : V → Prop) [DecidablePred Good]
  (d : U.direction) (hd : (d : V) ≠ 0)
  [Fintype (U.direction ⧸ Submodule.span F ({d} : Set U.direction))]
  {T : ℕ}
  (hGood : Fintype.card {x : U // Good x.1} > T * Fintype.card (U.direction ⧸ Submodule.span F ({d} : Set U.direction))) :
  ∃ b : U, Fintype.card {z : F // Good ((z • (d : V)) +ᵥ (b : V))} > T := by
  classical
  -- Choose an arbitrary reference point in `U`.
  let p : U := Classical.choice (inferInstance : Nonempty U)

  -- Good points in `U`.
  let α : Type := {x : U // Good x.1}

  -- Quotient of the direction by the line spanned by `d`.
  let P : Submodule F U.direction := Submodule.span F ({d} : Set U.direction)
  let β : Type := (U.direction ⧸ P)

  -- Displacement of a point from the reference point, viewed in `U.direction`.
  let disp : α → U.direction := fun x =>
    (⟨(x.1 : V) -ᵥ (p : V), U.vsub_mem_direction x.1.property p.property⟩ : U.direction)

  -- Map to the quotient; fibers correspond to affine lines parallel to `d`.
  let f : α → β := fun x => Submodule.Quotient.mk (p := P) (disp x)

  -- Convert the hypothesis to the form needed for pigeonhole.
  have hmul : Fintype.card β * T < Fintype.card α := by
    have h' : T * Fintype.card β < Fintype.card α := by
      simpa [α, β, P] using hGood
    simpa [Nat.mul_comm] using h'

  -- Get a large fiber of `f`.
  rcases (Fintype.exists_lt_card_fiber_of_mul_lt_card (f := f) (n := T) hmul) with ⟨q, hq⟩

  -- The fiber over `q`.
  let fiber : Type := {x : α // f x = q}
  have hfiber : T < Fintype.card fiber := by
    -- `hq` is stated using `#{x | f x = q}`, i.e. the filtered-universe finset cardinality.
    have hcard : Fintype.card fiber = #{x : α | f x = q} := by
      simpa [fiber] using (Fintype.card_subtype (α := α) (p := fun x : α => f x = q))
    simpa [hcard] using hq

  -- Pick a base point `b` in this fiber.
  have hfiber_pos : 0 < Fintype.card fiber :=
    lt_of_le_of_lt (Nat.zero_le T) hfiber
  have hfiber_nonempty : Nonempty fiber := (Fintype.card_pos_iff.1 hfiber_pos)
  let bα : fiber := Classical.choice hfiber_nonempty
  let b : U := bα.1.1

  -- Any point in the fiber lies on the affine line through `b` in direction `d`.
  have hx_on_line :
      ∀ x : fiber, ∃ z : F, (x.1.1 : V) = (z • (d : V)) +ᵥ (b : V) := by
    intro x

    -- Points in the same fiber have equal image under `f`.
    have hquot : f x.1 = f bα.1 := by
      simpa [x.2, bα.2]

    have hmemP : disp x.1 - disp bα.1 ∈ P := by
      have : (Submodule.Quotient.mk (p := P) (disp x.1) : β) =
            Submodule.Quotient.mk (p := P) (disp bα.1) := by
        simpa [f] using hquot
      exact (Submodule.Quotient.eq (p := P) (x := disp x.1) (y := disp bα.1)).1 this

    -- Rewrite the difference of displacements as the displacement from `b`.
    have hdir :
        disp x.1 - disp bα.1 =
          (⟨(x.1.1 : V) -ᵥ (b : V),
            U.vsub_mem_direction x.1.1.property bα.1.1.property⟩ : U.direction) := by
      ext
      simp [disp, b, vsub_sub_vsub_cancel_right]

    have hmem :
        (⟨(x.1.1 : V) -ᵥ (b : V),
          U.vsub_mem_direction x.1.1.property bα.1.1.property⟩ : U.direction) ∈ P := by
      simpa [hdir] using hmemP

    -- Membership in `span {d}` gives a scalar.
    rcases
        (Submodule.mem_span_singleton).1 (by simpa [P] using hmem) with ⟨z, hz⟩
    refine ⟨z, ?_⟩

    have hzV : (x.1.1 : V) -ᵥ (b : V) = z • (d : V) := by
      have hz' := congrArg (fun (w : U.direction) => (w : V)) hz
      simpa [b] using hz'.symm

    -- Turn a `vsub` equation into the desired `vadd` equation.
    exact (eq_vadd_iff_vsub_eq (p₁ := (x.1.1 : V)) (g := z • (d : V)) (p₂ := (b : V))).2 hzV

  -- Define a map from the fiber to scalars witnessing goodness on this line.
  let zOf : fiber → F := fun x => Classical.choose (hx_on_line x)
  have hzOf_spec :
      ∀ x : fiber, (x.1.1 : V) = (zOf x • (d : V)) +ᵥ (b : V) := by
    intro x
    simpa [zOf] using (Classical.choose_spec (hx_on_line x))

  let γ : Type := {z : F // Good ((z • (d : V)) +ᵥ (b : V))}

  let g : fiber → γ := fun x =>
    ⟨zOf x, by
      simpa [hzOf_spec x] using (x.1.2 : Good (x.1.1 : V))⟩

  have hg_inj : Function.Injective g := by
    intro x₁ x₂ h
    have hz : zOf x₁ = zOf x₂ := congrArg Subtype.val h

    have hxV : (x₁.1.1 : V) = (x₂.1.1 : V) := by
      calc
        (x₁.1.1 : V) = (zOf x₁ • (d : V)) +ᵥ (b : V) := hzOf_spec x₁
        _ = (zOf x₂ • (d : V)) +ᵥ (b : V) := by simpa [hz]
        _ = (x₂.1.1 : V) := (hzOf_spec x₂).symm

    have hxU : (x₁.1.1 : U) = (x₂.1.1 : U) := by
      ext
      exact hxV

    have hxα : (x₁.1 : α) = (x₂.1 : α) := by
      apply Subtype.ext
      exact hxU

    apply Subtype.ext
    exact hxα

  have hcard : Fintype.card fiber ≤ Fintype.card γ :=
    Fintype.card_le_of_injective g hg_inj

  refine ⟨b, ?_⟩
  exact lt_of_lt_of_le hfiber hcard


theorem wca_exists_eq_of_cover_lt_fieldCard {F V : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype V] [DecidableEq V]
  (U : AffineSubspace F V) [Nonempty U]
  (L : Finset (AffineSubspace F V))
  (hL : L.card < Fintype.card F)
  (hsub : ∀ A ∈ L, A ≤ U)
  (hnonempty : ∀ A ∈ L, Nonempty A)
  (hcover : (U : Set V) ⊆ ⋃ A ∈ L, (A : Set V)) :
  ∃ A ∈ L, A = U := by
  classical
  let q : ℕ := Fintype.card F
  have hqpos : 0 < q := Fintype.card_pos

  -- Split on `finrank` of the direction of `U`.
  cases hdim : Module.finrank F U.direction with
  | zero =>
      -- If `U.direction` has finrank 0, then `U.direction = ⊥` and any nonempty `A ≤ U` must equal `U`.
      let u0 : U := Classical.choice (inferInstance : Nonempty U)
      have hu : (u0.1 : V) ∈ ⋃ A ∈ L, (A : Set V) := hcover u0.2
      rcases Set.mem_iUnion.1 hu with ⟨A, huA⟩
      rcases Set.mem_iUnion.1 huA with ⟨hAL, huA'⟩
      refine ⟨A, hAL, ?_⟩
      have hAle : A ≤ U := hsub A hAL
      have hAne : (A : Set V).Nonempty := by
        rcases hnonempty A hAL with ⟨a⟩
        exact ⟨a.1, a.2⟩
      have hUdir : U.direction = ⊥ :=
        (Submodule.finrank_eq_zero (R := F) (S := U.direction)).1 hdim
      have hAdir_le : A.direction ≤ U.direction := AffineSubspace.direction_le hAle
      have hAdir : A.direction = ⊥ := by
        have : A.direction ≤ (⊥ : Submodule F V) := by
          simpa [hUdir] using hAdir_le
        exact le_antisymm this bot_le
      have hdirEq : A.direction = U.direction := by
        simpa [hAdir, hUdir]
      exact
        AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirEq hAne hAle

  | succ d' =>
      -- Main counting argument in positive dimension.
      by_contra hex
      have hne : ∀ A ∈ L, A ≠ U := by
        intro A hA hEq
        exact hex ⟨A, hA, hEq⟩

      -- Cardinality of `U`.
      let u0 : U := Classical.choice (inferInstance : Nonempty U)
      have cardU : Fintype.card U = q ^ Nat.succ d' := by
        have h1 : Fintype.card U = Fintype.card U.direction :=
          Fintype.card_congr (Equiv.vaddConst u0).symm
        have h2 : Fintype.card U.direction = q ^ Nat.succ d' := by
          simpa [q, hdim] using (Module.card_eq_pow_finrank (K := F) (V := U.direction))
        exact h1.trans h2

      -- Surjection from the disjoint union of all `A ∈ L` onto `U`.
      let g : (Σ A : L, A.1) → U := fun x =>
        ⟨x.2.1, (hsub x.1.1 x.1.2) x.2.2⟩

      have hg : Function.Surjective g := by
        intro u
        have hu : (u.1 : V) ∈ ⋃ A ∈ L, (A : Set V) := hcover u.2
        rcases Set.mem_iUnion.1 hu with ⟨A, huA⟩
        rcases Set.mem_iUnion.1 huA with ⟨hAL, huA'⟩
        refine ⟨⟨⟨A, hAL⟩, ⟨u.1, huA'⟩⟩, ?_⟩
        ext
        rfl

      have hcardU_le_sigma : Fintype.card U ≤ Fintype.card (Σ A : L, A.1) :=
        Fintype.card_le_of_surjective g hg

      have hcardSigma : Fintype.card (Σ A : L, A.1) = ∑ A : L, Fintype.card A.1 := by
        simpa using (Fintype.card_sigma (β := fun A : L => A.1))

      have hcardU_le_sum : Fintype.card U ≤ ∑ A : L, Fintype.card A.1 := by
        simpa [hcardSigma] using hcardU_le_sigma

      -- Uniform bound on the size of each `A ∈ L`.
      let bound : ℕ := q ^ d'
      have bound_pos : 0 < bound := by
        dsimp [bound]
        exact Nat.pow_pos hqpos

      have hcardA_le : ∀ A : L, Fintype.card A.1 ≤ bound := by
        intro A
        have hAle : A.1 ≤ U := hsub A.1 A.2
        have hAne : (A.1 : Set V).Nonempty := by
          rcases hnonempty A.1 A.2 with ⟨a⟩
          exact ⟨a.1, a.2⟩
        have hAlt : A.1 < U := lt_of_le_of_ne hAle (hne A.1 A.2)
        have hdirlt : A.1.direction < U.direction :=
          AffineSubspace.direction_lt_of_nonempty hAlt hAne
        have hfinrank_lt : Module.finrank F A.1.direction < Nat.succ d' := by
          have : Module.finrank F A.1.direction < Module.finrank F U.direction :=
            Submodule.finrank_lt_finrank_of_lt (K := F) (V := V) hdirlt
          simpa [hdim] using this
        have hle_exp : Module.finrank F A.1.direction ≤ d' := Nat.le_of_lt_succ hfinrank_lt

        obtain ⟨p, hp⟩ := hAne
        let pA : A.1 := ⟨p, hp⟩
        letI : Nonempty A.1 := ⟨pA⟩

        have hAcard : Fintype.card A.1 = Fintype.card A.1.direction :=
          Fintype.card_congr (Equiv.vaddConst pA).symm

        have card_dir : Fintype.card A.1.direction = q ^ Module.finrank F A.1.direction := by
          simpa [q] using (Module.card_eq_pow_finrank (K := F) (V := A.1.direction))

        have cardA_eq : Fintype.card A.1 = q ^ Module.finrank F A.1.direction :=
          hAcard.trans card_dir

        have hpow_le : q ^ Module.finrank F A.1.direction ≤ q ^ d' :=
          Nat.pow_le_pow_right hqpos hle_exp

        simpa [bound, cardA_eq] using hpow_le

      have hsum_le : (∑ A : L, Fintype.card A.1) ≤ Fintype.card L * bound := by
        classical
        simpa using
          (Finset.sum_le_card_nsmul (s := (Finset.univ : Finset L))
            (f := fun A : L => Fintype.card A.1) (n := bound) (by
              intro A _
              exact hcardA_le A))

      have hL' : Fintype.card L < q := by
        simpa [q] using hL

      have hstrict_prod : Fintype.card L * bound < q * bound :=
        Nat.mul_lt_mul_of_pos_right hL' bound_pos

      have hqmul : q * bound = q ^ Nat.succ d' := by
        dsimp [bound]
        -- `q^(d'+1) = q^d' * q`
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

      have hprod_lt_cardU : Fintype.card L * bound < Fintype.card U := by
        have : Fintype.card L * bound < q ^ Nat.succ d' :=
          lt_of_lt_of_eq hstrict_prod hqmul
        simpa [cardU] using this

      have : Fintype.card U < Fintype.card U := by
        have h1 : Fintype.card U ≤ ∑ A : L, Fintype.card A.1 := hcardU_le_sum
        have h2 : (∑ A : L, Fintype.card A.1) ≤ Fintype.card L * bound := hsum_le
        have h3 : Fintype.card L * bound < Fintype.card U := hprod_lt_cardU
        exact lt_of_le_of_lt (le_trans h1 h2) h3

      exact lt_irrefl _ this


theorem wca_ratio_bound_implies_exists_v [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M m : ℕ}
  [DecidablePred (fun x : (WCA_affineSpace u) =>
    WCA_good (F := F) (ι := ι) μ domain deg α x.1)]
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  (sr : ℝ≥0)
  (hsr : sr = ReedSolomonCode.sqrtRate deg domain) :
  (0 : ℝ≥0) < sr →
  (sr * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (α < 1) →
  ((Fintype.card {x : (WCA_affineSpace u) //
        WCA_good (F := F) (ι := ι) μ domain deg α x.1} : ENNReal) /
      (Fintype.card (WCA_affineSpace u))) >
    ENNReal.ofReal (WCA_bound ι F sr M m) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := by
  -- This lemma is the core combinatorial lift (BCIKS20 §6.3/§7.3) from a lower bound on the density of `Good` points in the affine space `U := WCA_affineSpace u` to a global correlated-agreement witness.
  -- 
  -- Recommended skeleton:
  -- - Work with `U := WCA_affineSpace u` and `Good := WCA_good μ domain deg α`.
  -- - Split on `U.direction = ⊥` vs `≠ ⊥`.
  --   * `direction = ⊥`: `U` is a singleton; use the ratio bound to show the unique point is good and pick witnesses directly.
  --   * `direction ≠ ⊥`: implement the BCIKS20 minimizer/list/cover/collapse argument.
  -- 
  -- Nontrivial case outline:
  -- 1. Choose `u* : U` minimizing `agree_set μ (↑u*) (finCarrier domain deg)` (finite min exists).
  -- 2. Let `α*` be that minimum; show `α* ≥ α`.
  -- 3. Define the candidate list `V* := {v ∈ finCarrier domain deg | agree μ (↑u*) v ≥ α*}`.
  -- 4. Use the *max-right* part of `WCA_bound` to show `V*.card < Fintype.card F`.
  -- 5. For each `v ∈ V*`, build an affine subspace `A_v ≤ U` (nonempty, contains `u*`) such that
  --    `⋃ v∈V*, A_v` covers `U`.
  --    (This uses the line theorem `weighted_correlated_agreement_for_parameterized_curves'` with `l := 0` on lines from `u*` to arbitrary points.)
  -- 6. Apply `wca_exists_eq_of_cover_lt_fieldCard` to the cover to get some `v` with `A_v = U`.
  -- 7. From `A_v = U`, extract codewords for each generator `u j` agreeing on a common domain of μ-measure ≥ α, and finish with `mu_set_mono`.
  -- 
  -- Tips:
  -- - You already have the geometric collapse lemma `wca_exists_eq_of_cover_lt_fieldCard`; focus on constructing the cover and proving the card bound.
  -- - Keep ENNReal/ℝ coercions localized; switch to Nat-card inequalities only when applying `wca_exists_base_with_many_good_on_line` or similar pigeonhole steps.
  sorry

theorem weighted_correlated_agreement_over_affine_spaces'_direct [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M m : ℕ}
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  (sr : ℝ≥0)
  (hsr : sr = ReedSolomonCode.sqrtRate deg domain)
  (pr : ENNReal)
  (hpr : pr = Pr_{let x ←$ᵖ (WCA_affineSpace u)}[WCA_good (F := F) (ι := ι) μ domain deg α x]) :
  (0 : ℝ≥0) < sr →
  (sr * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (α < 1) →
  pr > ENNReal.ofReal (WCA_bound ι F sr M m) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := by
  classical
  intro hsr_pos hα hα₁ hpr_bound

  -- Provide decidability for the "good" predicate on the affine space.
  haveI : DecidablePred (fun x : (WCA_affineSpace u) =>
      WCA_good (F := F) (ι := ι) μ domain deg α x.1) :=
    Classical.decPred _

  -- Rewrite the probability bound using `hpr`.
  have hpr_bound' :
      Pr_{let x ←$ᵖ (WCA_affineSpace u)}[WCA_good (F := F) (ι := ι) μ domain deg α x] >
        ENNReal.ofReal (WCA_bound ι F sr M m) := by
    simpa [hpr] using hpr_bound

  -- Convert probability to a counting ratio.
  have hPr :
      Pr_{let x ←$ᵖ (WCA_affineSpace u)}[WCA_good (F := F) (ι := ι) μ domain deg α x] =
        ((Fintype.card {x : (WCA_affineSpace u) //
              WCA_good (F := F) (ι := ι) μ domain deg α x.1} : ENNReal) /
          (Fintype.card (WCA_affineSpace u))) := by
    simpa using
      (pr_uniformOfFintype_eq_card (α := (WCA_affineSpace u))
        (P := fun x : (WCA_affineSpace u) =>
          WCA_good (F := F) (ι := ι) μ domain deg α x.1))

  have hratio :
      ((Fintype.card {x : (WCA_affineSpace u) //
            WCA_good (F := F) (ι := ι) μ domain deg α x.1} : ENNReal) /
          (Fintype.card (WCA_affineSpace u))) >
        ENNReal.ofReal (WCA_bound ι F sr M m) := by
    -- Rewrite only the LHS of `hpr_bound'` and avoid simplifying the `max` inside `WCA_bound`.
    have h := hpr_bound'
    rw [hPr] at h
    exact h

  -- Now apply the packaged affine-space→line reduction.
  exact
    wca_ratio_bound_implies_exists_v (F := F) (ι := ι) (k := k)
      (hm := hm) (hμ := hμ) (sr := sr) (hsr := hsr)
      hsr_pos hα hα₁ hratio

theorem weighted_correlated_agreement_over_affine_spaces' [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M m : ℕ}
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) :
  letI sr := ReedSolomonCode.sqrtRate deg domain
  (hsr_pos : (0 : ℝ≥0) < sr) →
  letI pr :=
    Pr_{let x ←$ᵖ (WCA_affineSpace u)}[agree_set μ x (finCarrier domain deg) ≥ α]
  (hα : sr * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hα₁ : α < 1) →
  letI numeratorl : ℝ := (1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2
  letI denominatorl : ℝ := (3 * sr^3) * Fintype.card F
  letI numeratorr : ℝ := (max (2 * m + 3) 23) * (M * Fintype.card ι + 1)
  letI denominatorr : ℝ := sr * Fintype.card F
  pr > ENNReal.ofReal (max (numeratorl / denominatorl) (numeratorr / denominatorr)) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := by
  classical
  simpa using
    (weighted_correlated_agreement_over_affine_spaces'_direct (F := F) (ι := ι) (k := k) (l := l) (u := u)
      (deg := deg) (domain := domain) (μ := μ) (α := α) (M := M) (m := m) hm hμ)


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
