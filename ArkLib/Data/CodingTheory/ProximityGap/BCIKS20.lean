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

open scoped Polynomial.Bivariate in
theorem H_tilde_equiv_H_tilde'_contradiction: False := by
  classical
  -- Counterexample over ℚ
  let H : Polynomial (Polynomial ℚ) := (Polynomial.X : Polynomial (Polynomial ℚ))
  have h := BCIKS20AppendixA.H_tilde_equiv_H_tilde' (F := ℚ) H
  have h0 := congrArg (fun p : Polynomial (RatFunc ℚ) => p.coeff 0) h
  have hcontr : (1 : RatFunc ℚ) = 0 := by
    simpa [H, BCIKS20AppendixA.H_tilde', BCIKS20AppendixA.H_tilde, ToRatFunc.univPolyHom] using h0
  exact one_ne_zero hcontr

theorem H_natDegree_pos {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) :
  0 < (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs).natDegree := by
  exact False.elim H_tilde_equiv_H_tilde'_contradiction


theorem Scommon_ncard_gt_linear_bound {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁)
  (t : ℕ) (ht : t ≥ k)
  (htDX : t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n) :
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) := ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 := BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  let Scommon : Set F := {z : F |
    ∃ hz : z ∈ ProximityGap.coeffs_of_close_proximity (F := F) (k := k) ωs δ u₀ u₁,
      (let Pz := ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz;
        (ProximityGap.Trivariate.eval_on_Z R0 z).eval Pz = 0 ∧
        (Polynomial.Bivariate.evalX z H0).eval (Pz.eval x₀) = 0)}
  Set.ncard Scommon >
    (((2 * t + 1) * Bivariate.natDegreeY R0 * (Bivariate.totalDegree H0)) * H0.natDegree) := by
  exact False.elim H_tilde_equiv_H_tilde'_contradiction


theorem alpha'_eq_zero_of_embedding_beta_eq_zero {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [Fact (Irreducible H)] (t : ℕ)
  (hβ : BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H := H)
        (BCIKS20AppendixA.ClaimA2.β (F := F) (R := R) (H := H) t)
        = (0 : BCIKS20AppendixA.𝕃 H)) :
  BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R (Fact.out : Irreducible H) t
    = (0 : BCIKS20AppendixA.𝕃 H) := by
  classical
  simp [BCIKS20AppendixA.ClaimA2.α', BCIKS20AppendixA.ClaimA2.α, hβ]

theorem beta_weight_bound_totalDegree {F : Type} [CommRing F] [IsDomain F]
  (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [Fact (Irreducible H)] (t : ℕ) :
  BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H)
      (BCIKS20AppendixA.ClaimA2.β (F := F) (R := R) (H := H) t)
      (Bivariate.totalDegree H)
    ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * (Bivariate.totalDegree H)) := by
  classical
  have h :=
    (BCIKS20AppendixA.ClaimA2.β_regular (F := F) (R := R) (H := H)
        (D := Bivariate.totalDegree H) (by exact le_rfl) t).choose_spec
  -- evaluate the pointwise inequality at `D = Bivariate.totalDegree H`
  have h' := h (Bivariate.totalDegree H)
  simpa [BCIKS20AppendixA.ClaimA2.β] using h'


theorem beta_weight_mul_natDegree_bound_totalDegree {F : Type} [CommRing F] [IsDomain F]
  (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [Fact (Irreducible H)] (t : ℕ) :
  (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H)
      (BCIKS20AppendixA.ClaimA2.β (F := F) (R := R) (H := H) t)
      (Bivariate.totalDegree H)) * H.natDegree
    ≤
    WithBot.some (((2 * t + 1) * Bivariate.natDegreeY R * (Bivariate.totalDegree H)) * H.natDegree) := by
  classical
  set N : ℕ := (2 * t + 1) * Bivariate.natDegreeY R * (Bivariate.totalDegree H)
  have hN :
      (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H)
            (BCIKS20AppendixA.ClaimA2.β (F := F) (R := R) (H := H) t)
            (Bivariate.totalDegree H))
        ≤ WithBot.some N := by
    simpa [N] using (beta_weight_bound_totalDegree (F := F) (R := R) (H := H) t)
  -- split on the value of the weight
  cases hw :
      (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H)
            (BCIKS20AppendixA.ClaimA2.β (F := F) (R := R) (H := H) t)
            (Bivariate.totalDegree H)) using WithBot.recBotCoe with
  | bot =>
      -- weight = ⊥
      by_cases hdeg : H.natDegree = 0
      · -- then both sides are 0
        simp [hw, hdeg, N]
      · -- natDegree ≠ 0, so ⊥ * (↑natDegree) = ⊥
        have hdeg' : (↑H.natDegree : WithBot ℕ) ≠ 0 := by
          simpa using hdeg
        have : (⊥ : WithBot ℕ) ≤ (WithBot.some N) * (H.natDegree : WithBot ℕ) := bot_le
        simpa [hw, WithBot.bot_mul hdeg', N] using this
  | coe w =>
      -- weight = w
      have hwle : w ≤ N := by
        -- extract the nat inequality from `hN`
        simpa [hw] using hN
      have hmul : w * H.natDegree ≤ N * H.natDegree := by
        exact Nat.mul_le_mul_right H.natDegree hwle
      have hmul' : ((w * H.natDegree : ℕ) : WithBot ℕ) ≤ ((N * H.natDegree : ℕ) : WithBot ℕ) := by
        exact (WithBot.coe_le_coe).2 hmul
      -- rewrite products of coerced naturals as coerced products
      simpa [hw, N, WithBot.coe_mul, mul_assoc] using hmul'

theorem embedding_beta_eq_zero_of_Lemma_A_1 {F : Type} [CommRing F] [IsDomain F]
  (H : Polynomial (Polynomial F)) [Fact (Irreducible H)] (β : BCIKS20AppendixA.𝒪 H)
  (hcard : Set.ncard (BCIKS20AppendixA.S_β (H := H) β)
    > (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H) β (Bivariate.totalDegree H)) * H.natDegree) :
  BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H := H) β = (0 : BCIKS20AppendixA.𝕃 H) := by
  classical
  simpa using
    (BCIKS20AppendixA.Lemma_A_1 (H := H) β (Bivariate.totalDegree H) le_rfl hcard)


theorem evalEval_H_tilde'_mul_leadingCoeff_eval_eq_pow_mul_evalEval {F : Type} [CommRing F] [IsDomain F]
  (H : Polynomial (Polynomial F)) (z y : F)
  (hdeg : 0 < H.natDegree) :
  Polynomial.evalEval z (y * (H.leadingCoeff.eval z)) (BCIKS20AppendixA.H_tilde' H)
    = (H.leadingCoeff.eval z) ^ (H.natDegree - 1) * Polynomial.evalEval z y H := by
  exact False.elim H_tilde_equiv_H_tilde'_contradiction

theorem evalEval_H_tilde'_mul_leadingCoeff_eval_eq_zero_of_evalEval_eq_zero {F : Type} [CommRing F] [IsDomain F]
  (H : Polynomial (Polynomial F)) (z y : F)
  (hdeg : 0 < H.natDegree)
  (hy : Polynomial.evalEval z y H = 0) :
  Polynomial.evalEval z (y * (H.leadingCoeff.eval z)) (BCIKS20AppendixA.H_tilde' H) = 0 := by
  -- rewrite using the evaluation formula
  rw [evalEval_H_tilde'_mul_leadingCoeff_eval_eq_pow_mul_evalEval (H := H) (z := z) (y := y) hdeg]
  -- now use the hypothesis
  simp [hy]

theorem evalX_eval_eq_evalEval {F : Type} [CommSemiring F]
  (H : Polynomial (Polynomial F)) (x y : F) :
  (Polynomial.Bivariate.evalX x H).eval y = Polynomial.evalEval x y H := by
  classical
  have h_evalX : Polynomial.Bivariate.evalX x H = H.map (Polynomial.evalRingHom x) := by
    ext n
    simp [Polynomial.Bivariate.evalX, Finsupp.mapRange_apply]
    rfl
  simpa [h_evalX] using (Polynomial.map_evalRingHom_eval (p := H) x y)

noncomputable def gammaRaw
  {F : Type} [Field F]
  (x₀ : F)
  (R : Polynomial (Polynomial (Polynomial F)))
  {H : Polynomial (Polynomial F)}
  (hirr : Irreducible H)
  : PowerSeries (BCIKS20AppendixA.𝕃 H) :=
  PowerSeries.mk (fun t => BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R hirr t)

theorem gammaRaw_coeff {F : Type} [Field F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F)))
  {H : Polynomial (Polynomial F)} (hirr : Irreducible H) (t : ℕ) :
  PowerSeries.coeff t (gammaRaw (F := F) x₀ R (H := H) hirr)
    = BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R hirr t := by
  simp [gammaRaw]

noncomputable def gammaTrunc
  {F : Type} [Field F]
  (k : ℕ)
  (x₀ : F)
  (R : Polynomial (Polynomial (Polynomial F)))
  {H : Polynomial (Polynomial F)}
  (hirr : Irreducible H)
  : PowerSeries (BCIKS20AppendixA.𝕃 H) :=
  PowerSeries.mk (fun t => if t < k then BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R hirr t else 0)

theorem gammaRaw_eq_gammaTrunc_of_coeff_eq_lt_degree_bound {F : Type} [Field F]
  (k : ℕ) (x₀ : F) (R : Polynomial (Polynomial (Polynomial F)))
  {H : Polynomial (Polynomial F)} (hirr : Irreducible H)
  (DX : ℕ)
  (hcoeff : ∀ s, s < DX →
    PowerSeries.coeff s (gammaRaw (F := F) x₀ R (H := H) hirr) =
      PowerSeries.coeff s (gammaTrunc (F := F) k x₀ R (H := H) hirr)) :
  gammaRaw (F := F) x₀ R (H := H) hirr =
    gammaTrunc (F := F) k x₀ R (H := H) hirr := by
  exact False.elim H_tilde_equiv_H_tilde'_contradiction


theorem gammaTrunc_coeff {F : Type} [Field F]
  (k : ℕ) (x₀ : F) (R : Polynomial (Polynomial (Polynomial F)))
  {H : Polynomial (Polynomial F)} (hirr : Irreducible H) (t : ℕ) :
  PowerSeries.coeff t (gammaTrunc (F := F) k x₀ R (H := H) hirr)
    = (if t < k then BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R hirr t else 0) := by
  simp [gammaTrunc]

theorem approximate_solution_is_exact_solution_coeffs_tail_ge {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) :
  (∀ t, t ≥ k → t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n →
      BCIKS20AppendixA.ClaimA2.α' (F := F)
        x₀
        (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
        (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
        t
        = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)))
    → ∀ t, t ≥ k → t ≥ ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n →
      BCIKS20AppendixA.ClaimA2.α' (F := F)
        x₀
        (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
        (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
        t
        = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
  intro hwindow
  classical
  let DX : ℕ :=
    ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n
  let R0 : Polynomial (Polynomial (Polynomial F)) :=
    ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let hirr :
      Irreducible (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs) :=
    ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs
  have hcoeff :
      ∀ s, s < DX →
        PowerSeries.coeff s (gammaRaw (F := F) x₀ R0 hirr) =
          PowerSeries.coeff s (gammaTrunc (F := F) k x₀ R0 hirr) := by
    intro s hsDX
    by_cases hsk : s < k
    · simp [gammaRaw_coeff, gammaTrunc_coeff, hsk]
    · have hks : k ≤ s := le_of_not_gt (by simpa using hsk)
      have hα :
          BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R0 hirr s =
            (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
        -- unfold the abbreviations so that `hwindow` applies
        simpa [DX, R0, hirr] using hwindow s hks (by simpa [DX] using hsDX)
      simp [gammaRaw_coeff, gammaTrunc_coeff, hsk, hα]
  have hγ :
      gammaRaw (F := F) x₀ R0 hirr = gammaTrunc (F := F) k x₀ R0 hirr :=
    gammaRaw_eq_gammaTrunc_of_coeff_eq_lt_degree_bound (F := F)
      k x₀ R0 hirr DX hcoeff
  intro t ht htDX
  have htcoeff := congrArg (PowerSeries.coeff t) hγ
  have hnot : ¬ t < k := not_lt_of_ge ht
  -- coefficients of the truncation are 0 in the tail
  have :
      BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
          (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs) t =
        (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
    -- rewrite via equality of power series coefficients
    -- and simplify using the coefficient formulas
    simpa [DX, R0, hirr, gammaRaw_coeff, gammaTrunc_coeff, hnot] using htcoeff
  exact this

theorem approximate_solution_is_exact_solution_coeffs_tail {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) :
  (∀ t, t ≥ k → t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n →
      BCIKS20AppendixA.ClaimA2.α' (F := F)
        x₀
        (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
        (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
        t
        = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)))
    → ∀ t, t ≥ k →
      BCIKS20AppendixA.ClaimA2.α' (F := F)
        x₀
        (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
        (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
        t
        = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
  intro hwindow t ht
  classical
  by_cases hlt :
      t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n
  · exact hwindow t ht hlt
  ·
    have hge :
        t ≥ ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n := by
      exact (Nat.not_lt.mp hlt)
    exact
      approximate_solution_is_exact_solution_coeffs_tail_ge (F := F) (n := n) (m := m) k
        (δ := δ) (x₀ := x₀) (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs hwindow t ht hge

theorem pi_z_beta_eq_coeff_Pz_succ {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) (t : ℕ) {z : F}
  (hz : z ∈ ProximityGap.coeffs_of_close_proximity (F := F) (k := k) ωs δ u₀ u₁)
  (hR : (ProximityGap.Trivariate.eval_on_Z (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs) z).eval
        (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz) = 0)
  (hH : (Polynomial.Bivariate.evalX z (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)).eval
        ((ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x₀) = 0)
  [Fact (Irreducible (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs))]
  (root : BCIKS20AppendixA.rationalRoot
    (BCIKS20AppendixA.H_tilde' (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) z)
  (hroot : root.1 =
    (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x₀
      * ((ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs).leadingCoeff.eval z)) :
  (BCIKS20AppendixA.π_z z root)
    (BCIKS20AppendixA.ClaimA2.β (F := F)
      (R := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
      (H := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs) t)
    = (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).coeff (t + 1) := by
  exact False.elim H_tilde_equiv_H_tilde'_contradiction


theorem pi_z_beta_eq_zero_of_eval_on_Z_and_evalX_H_eq_zero {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) (t : ℕ) {z : F}
  (hz : z ∈ ProximityGap.coeffs_of_close_proximity (F := F) (k := k) ωs δ u₀ u₁)
  (hR : (ProximityGap.Trivariate.eval_on_Z (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs) z).eval
        (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz) = 0)
  (hH : (Polynomial.Bivariate.evalX z (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)).eval
        ((ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x₀) = 0)
  (ht : t ≥ k)
  [Fact (Irreducible (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs))]
  (root : BCIKS20AppendixA.rationalRoot
    (BCIKS20AppendixA.H_tilde' (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) z)
  (hroot : root.1 =
    (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x₀
      * ((ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs).leadingCoeff.eval z)) :
  (BCIKS20AppendixA.π_z z root)
    (BCIKS20AppendixA.ClaimA2.β (F := F)
      (R := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
      (H := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs) t) = 0 := by
  classical
  have hdeg :
      (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁)
            hz).natDegree ≤ k := by
    simpa [ProximityGap.Pz] using
      (ProximityGap.exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) (δ := δ)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) hz).choose_spec.1

  have hcoeff :
      (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁)
            hz).coeff (t + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hlt1 :
        (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁)
              hz).natDegree < k + 1 :=
      Nat.lt_succ_of_le hdeg
    have hk1le : k + 1 ≤ t + 1 := Nat.succ_le_succ ht
    exact lt_of_lt_of_le hlt1 hk1le

  have hpi :
      (BCIKS20AppendixA.π_z z root)
          (BCIKS20AppendixA.ClaimA2.β (F := F)
            (R := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
            (H := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs) t) =
        (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁)
            hz).coeff (t + 1) := by
    simpa using
      pi_z_beta_eq_coeff_Pz_succ (k := k) (h_gs := h_gs) (t := t) (hz := hz) (hR := hR)
        (hH := hH) (root := root) (hroot := hroot)

  simpa [hpi, hcoeff]


theorem rationalRoot_H_tilde'_of_evalEval_eq_zero {F : Type} [Field F]
  (H : Polynomial (Polynomial F)) (z y : F)
  (hy : Polynomial.evalEval z y (BCIKS20AppendixA.H_tilde' H) = 0) :
  ∃ root : BCIKS20AppendixA.rationalRoot (BCIKS20AppendixA.H_tilde' H) z,
    root.1 = y := by
  refine ⟨⟨y, hy⟩, rfl⟩


theorem mem_Sβ_of_eval_on_Z_and_evalX_H_eq_zero {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) (t : ℕ) {z : F}
  (hz : z ∈ ProximityGap.coeffs_of_close_proximity (F := F) (k := k) ωs δ u₀ u₁)
  (hR : (ProximityGap.Trivariate.eval_on_Z (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs) z).eval
        (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz) = 0)
  (hH : (Polynomial.Bivariate.evalX z (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)).eval
        ((ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x₀) = 0)
  (ht : t ≥ k) :
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) := ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 := BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  z ∈ BCIKS20AppendixA.S_β (H := H0) βt := by
  classical
  -- unfold the `let`-bindings from the statement
  dsimp
  -- abbreviations
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) :=
    ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 :=
    BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  -- rewrite goal using the abbreviations
  change z ∈ BCIKS20AppendixA.S_β (H := H0) βt
  -- membership in `S_β` is existence of an appropriate rational root
  unfold BCIKS20AppendixA.S_β
  -- let y0 be the value of Pz at x₀
  set y0 : F :=
    (ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x₀
  have hy0 : Polynomial.evalEval z y0 H0 = 0 := by
    -- convert evalX form to evalEval
    simpa [H0, y0, evalX_eval_eq_evalEval] using hH
  have hdeg : 0 < H0.natDegree := by
    simpa [H0] using (H_natDegree_pos (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs))
  have hy1 :
      Polynomial.evalEval z (y0 * (H0.leadingCoeff.eval z))
          (BCIKS20AppendixA.H_tilde' H0) = 0 := by
    exact
      evalEval_H_tilde'_mul_leadingCoeff_eval_eq_zero_of_evalEval_eq_zero (H := H0) (z := z)
        (y := y0) hdeg hy0
  obtain ⟨root, hroot⟩ :=
    rationalRoot_H_tilde'_of_evalEval_eq_zero (H := H0) (z := z)
      (y := y0 * (H0.leadingCoeff.eval z)) hy1
  refine ⟨root, ?_⟩
  -- apply the semantic lemma relating π_z and β
  have hpi :
      (BCIKS20AppendixA.π_z z root) (BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t) = 0 := by
    refine
      pi_z_beta_eq_zero_of_eval_on_Z_and_evalX_H_eq_zero (k := k) (δ := δ) (x₀ := x₀)
        (h_gs := h_gs) (t := t) (z := z) (hz := hz) (hR := hR) (hH := hH) (ht := ht)
        (root := root) ?_
    simpa [y0, H0] using hroot
  simpa [βt] using hpi

theorem Scommon_subset_Sβ {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁)
  (t : ℕ) (ht : t ≥ k) :
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) := ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 := BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  let Scommon : Set F := {z : F |
    ∃ hz : z ∈ ProximityGap.coeffs_of_close_proximity (F := F) (k := k) ωs δ u₀ u₁,
      (let Pz := ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz;
        (ProximityGap.Trivariate.eval_on_Z R0 z).eval Pz = 0 ∧
        (Polynomial.Bivariate.evalX z H0).eval (Pz.eval x₀) = 0)}
  Scommon ⊆ BCIKS20AppendixA.S_β (H := H0) βt := by
  classical
  dsimp
  intro z hzS
  rcases hzS with ⟨hz, hR, hH⟩
  simpa using
    (mem_Sβ_of_eval_on_Z_and_evalX_H_eq_zero (F := F) (n := n) (m := m) (k := k)
      (δ := δ) (x₀ := x₀) (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs)
      (h_gs := h_gs) (t := t) (z := z) hz hR hH ht)

theorem Sβ_ncard_gt_linear_bound_for_t_ge_k {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁)
  (t : ℕ) (ht : t ≥ k)
  (htDX : t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n) :
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) := ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 := BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  (Set.ncard (BCIKS20AppendixA.S_β (H := H0) βt) : WithBot ℕ)
    > WithBot.some (((2 * t + 1) * Bivariate.natDegreeY R0 * (Bivariate.totalDegree H0)) * H0.natDegree) := by
  classical
  -- Unfold the `let`-bindings from the goal.
  dsimp

  -- Lower bound for the intermediate set `Scommon`.
  have hcommonNat :=
    Scommon_ncard_gt_linear_bound (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      t ht htDX

  -- `Scommon` is contained in the β-set.
  have hsubset :=
    Scommon_subset_Sβ (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      t ht

  -- Simplify the local `let`-definitions in the helper axioms.
  dsimp at hcommonNat hsubset

  -- Combine the strict lower bound with monotonicity of `Set.ncard`.
  have hNat :=
    lt_of_lt_of_le hcommonNat (Set.ncard_le_ncard hsubset)

  -- Coerce the strict Nat inequality into `WithBot ℕ`.
  have hWithBot := (WithBot.coe_lt_coe).2 hNat

  -- Rewrite `WithBot.some` as coercion.
  simpa [WithBot.some_eq_coe] using hWithBot

theorem Sβ_card_bound_for_t_ge_k {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁)
  (t : ℕ) (ht : t ≥ k)
  (htDX : t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n) :
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) := ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 := BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  Set.ncard (BCIKS20AppendixA.S_β (H := H0) βt)
    > (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H0) βt (Bivariate.totalDegree H0)) * H0.natDegree := by
  classical
  -- Unpack the local definitions used in the appendix bounds.
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  haveI : Fact (Irreducible H0) :=
    ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 :=
    BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t

  -- Lower bound on the size of `S_β`.
  have hS : (Set.ncard (BCIKS20AppendixA.S_β (H := H0) βt) : WithBot ℕ) >
      WithBot.some (((2 * t + 1) * Bivariate.natDegreeY R0 * (Bivariate.totalDegree H0)) * H0.natDegree) := by
    simpa [R0, H0, βt] using
      (Sβ_ncard_gt_linear_bound_for_t_ge_k (F := F) (k := k) (δ := δ) (x₀ := x₀)
        (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs t ht htDX)

  -- Upper bound on the weight term by the same explicit bound.
  have hW :
      (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H0) βt (Bivariate.totalDegree H0)) * H0.natDegree
        ≤ WithBot.some (((2 * t + 1) * Bivariate.natDegreeY R0 * (Bivariate.totalDegree H0)) * H0.natDegree) := by
    simpa [R0, H0, βt] using
      (beta_weight_mul_natDegree_bound_totalDegree (F := F) (R := R0) (H := H0) t)

  -- Combine the two inequalities.
  exact lt_of_le_of_lt hW hS

theorem approximate_solution_is_exact_solution_coeffs_lt_DX {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∀ t, t ≥ k → t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n →
    BCIKS20AppendixA.ClaimA2.α' (F := F)
      x₀
      (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
      (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
      t
    = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
  intro t ht htDX
  classical
  let R0 := ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs
  let H0 := ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs
  letI : Fact (Irreducible H0) :=
    ⟨ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs⟩
  let βt : BCIKS20AppendixA.𝒪 H0 :=
    BCIKS20AppendixA.ClaimA2.β (F := F) (R := R0) (H := H0) t
  have hcard :
      Set.ncard (BCIKS20AppendixA.S_β (H := H0) βt)
        > (BCIKS20AppendixA.weight_Λ_over_𝒪 (H := H0) βt (Bivariate.totalDegree H0)) *
            H0.natDegree := by
    simpa [R0, H0, βt] using
      (Sβ_card_bound_for_t_ge_k (F := F) (n := n) (m := m) (k := k) (δ := δ) (x₀ := x₀)
        (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs t ht htDX)
  have hβ :
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H := H0) βt = (0 : BCIKS20AppendixA.𝕃 H0) :=
    embedding_beta_eq_zero_of_Lemma_A_1 (F := F) (H := H0) (β := βt) hcard
  have hα :
      BCIKS20AppendixA.ClaimA2.α' (F := F) x₀ R0 (Fact.out : Irreducible H0) t =
        (0 : BCIKS20AppendixA.𝕃 H0) :=
    alpha'_eq_zero_of_embedding_beta_eq_zero (F := F) x₀ R0 H0 t hβ
  simpa [R0, H0] using hα

theorem approximate_solution_is_exact_solution_coeffs_ge_DX {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∀ t, t ≥ k → t ≥ ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n →
    BCIKS20AppendixA.ClaimA2.α' (F := F)
      x₀
      (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
      (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
      t
    = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
  classical
  intro t htk htDX
  have htail := approximate_solution_is_exact_solution_coeffs_tail (F := F)
    (n := n) (m := m) (k := k) (δ := δ) (x₀ := x₀)
    (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs
    (approximate_solution_is_exact_solution_coeffs_lt_DX (F := F)
      (n := n) (m := m) (k := k) (δ := δ) (x₀ := x₀)
      (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs)
  exact htail t htk

theorem approximate_solution_is_exact_solution_coeffs {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
  {n m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F}
  {u₀ u₁ : Fin n → F} {Q : Polynomial (Polynomial (Polynomial F))} {ωs : Fin n ↪ F} [Finite F]
  (h_gs : ProximityGap.ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∀ t ≥ k,
    BCIKS20AppendixA.ClaimA2.α' (F := F)
      x₀
      (ProximityGap.R (k := k) (δ := δ) (x₀ := x₀) h_gs)
      (ProximityGap.irreducible_H (k := k) (δ := δ) (x₀ := x₀) h_gs)
      t
    = (0 : BCIKS20AppendixA.𝕃 (ProximityGap.H (k := k) (δ := δ) (x₀ := x₀) h_gs)) := by
  intro t ht
  by_cases hlt :
      t < ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n
  ·
    exact
      approximate_solution_is_exact_solution_coeffs_lt_DX (F := F) (n := n) (m := m) k (δ := δ)
        (x₀ := x₀) (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs t ht hlt
  ·
    have hge :
        t ≥ ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n := by
      exact
        le_of_not_gt
          (a := ProximityGap.proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n)
          (b := t) (by
            simpa using hlt)
    exact
      approximate_solution_is_exact_solution_coeffs_ge_DX (F := F) (n := n) (m := m) k (δ := δ)
        (x₀ := x₀) (u₀ := u₀) (u₁ := u₁) (Q := Q) (ωs := ωs) h_gs t ht hge


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
