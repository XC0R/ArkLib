/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Polynomial.BigOperators
import ArkLib.Data.CompPoly.Basic

/-!
# CompPoly Types and Computable Operations for Sum-Check

This module provides:

1. **Shared degree-bounded polynomial wrappers** from
   `ArkLib.Data.CompPoly.Basic`.
2. **Computable partial evaluation and domain summation** for `CMvPolynomial`, built
   on top of CompPoly's `bind₁` and `eval₂` APIs:
   - `partialEvalFirst` / `partialEvalLast` — fix the first/last variable to a scalar,
     defined via `bind₁` with `Fin.cons` / `Fin.snoc`.
   - `sumOverLast` — sum out the last variable over a finite domain.
   - `toUnivariate` — convert a 1-variable `CMvPolynomial` to `CPolynomial`,
     defined via `CMvPolynomial.eval₂`.
   - `sumAllButFirst` — iterate `sumOverLast`, keeping only variable 0 free.
   - `roundPoly` — compose `sumAllButFirst` with `toUnivariate`.

All definitions are computable and cast-free. Correctness lemmas relate the computable
definitions to `CMvPolynomial.eval` and `CPolynomial.eval`.

## Design

These types and operations are the CompPoly-native replacements for the Mathlib-facing
`MvPolynomial.restrictDegree` / `Polynomial.degreeLE` types that were used in earlier
versions of the sum-check formalization.

Partial evaluation (`partialEvalFirst`, `partialEvalLast`) is expressed as variable
substitution via `bind₁`, which gives access to the existing `bind₁_eq_aeval`,
`bind₁_X`, `bind₁_C` lemma suite for correctness proofs.

The univariate bridge (`toUnivariate`) uses `CMvPolynomial.eval₂` with a ring
homomorphism `CPolynomial.CRingHom : R →+* CPolynomial R`, so correctness follows
from `eval₂_equiv`.
-/

open CompPoly CPoly Std

attribute [local instance] instDecidableEqOfLawfulBEq

/-! ## Computable partial evaluation and domain summation -/

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-! ### Core primitives -/

/-- Fix variable 0 of a multivariate polynomial to a scalar value `a`.
Defined as `bind₁ (Fin.cons (C a) X) p`: substitute variable 0 with the constant `a`,
and shift variables `i+1` to `X i`. -/
def partialEvalFirst (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  bind₁ (Fin.cons (C a) X) p

/-- Fix the last variable of a multivariate polynomial to a scalar value `a`.
Defined as `bind₁ (Fin.snoc X (C a)) p`: keep variables `i < n` as `X i`,
and substitute variable `n` with the constant `a`. -/
def partialEvalLast (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  bind₁ (Fin.snoc X (C a)) p

variable {m : ℕ}

/-- Sum out the last variable of a polynomial over domain `D`.
Defined as `∑ d ∈ D, partialEvalLast d p`. -/
def sumOverLast (D : Fin m → R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  (Finset.univ : Finset (Fin m)).sum (fun j => partialEvalLast (D j) p)

/-! ### Composed operations -/

/-- Iterate `sumOverLast` to sum out all variables except variable 0.
`sumAllButFirst D k p` takes a polynomial in `k + 1` variables, keeps variable 0 free,
and sums variables 1 through k over domain `D`. -/
def sumAllButFirst (D : Fin m → R) : (k : ℕ) → CMvPolynomial (k + 1) R → CMvPolynomial 1 R
  | 0, p => p
  | k + 1, p => sumAllButFirst D k (sumOverLast D p)

/-! ### Correctness lemmas (core operations) -/

/-- `partialEvalFirst a p` correctly implements partial evaluation:
evaluating the result at `v` equals evaluating `p` at `Fin.cons a v`.
Proof strategy: unfold to `bind₁`, then use `bind₁_eq_aeval` and `eval₂_equiv`. -/
theorem partialEvalFirst_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalFirst a p).eval v = p.eval (Fin.cons a v) := by
  sorry

/-- `partialEvalLast a p` correctly implements partial evaluation of the last variable:
evaluating the result at `v` equals evaluating `p` at `Fin.snoc v a`.
Proof strategy: unfold to `bind₁`, then use `bind₁_eq_aeval` and `eval₂_equiv`. -/
theorem partialEvalLast_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalLast a p).eval v = p.eval (Fin.snoc v a) := by
  sorry

/-- `sumOverLast` evaluates correctly: sums the polynomial over the domain in the last
variable. Follows from `partialEvalLast_eval` and linearity of `eval`. -/
theorem sumOverLast_eval (D : Fin m → R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (sumOverLast D p).eval v =
      (Finset.univ : Finset (Fin m)).sum (fun j => p.eval (Fin.snoc v (D j))) := by
  sorry

/-- Summing out all variables except the first agrees with direct evaluation over the
remaining domain points. Follows by induction from `sumOverLast_eval`. -/
theorem sumAllButFirst_eval (D : Fin m → R) :
    ∀ (k : ℕ) (p : CMvPolynomial (k + 1) R) (x : R),
      (sumAllButFirst D k p).eval (fun _ : Fin 1 => x) =
        (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
          p.eval (Fin.cons x (D ∘ z))) := by
  sorry

/-! ### Degree preservation (core operations) -/

/-- `partialEvalFirst` preserves individual degree bounds.
Proof strategy: use `bind₁` structure — each `X i` has individual degree ≤ 1, and `C a`
has degree 0; substitution preserves the original degree bounds. -/
theorem partialEvalFirst_individualDegreeLE {deg : ℕ} (a : R)
    (p : CMvPolynomial (n + 1) R)
    (hDeg : IndividualDegreeLE (R := R) deg p) :
    IndividualDegreeLE (R := R) deg (partialEvalFirst a p) := by
  sorry

/-! ### Univariate bridge (requires `Nontrivial R`) -/

section Univariate

variable [Nontrivial R]

/-- The embedding `R → CPolynomial R` via the constant polynomial, bundled as a `RingHom`.
This is the CompPoly analogue of Mathlib's `Polynomial.C`.
TODO: upstream to CompPoly as `CPolynomial.CRingHom`. -/
private def cPolyRingHom : R →+* CPolynomial R where
  toFun := CPolynomial.C
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- Convert a single-variable multivariate polynomial to a univariate `CPolynomial`.
Defined via `CMvPolynomial.eval₂` with `CPolynomial.C` as the coefficient ring hom
and `CPolynomial.X` as the single variable image. -/
def toUnivariate (p : CMvPolynomial 1 R) : CPolynomial R :=
  eval₂ cPolyRingHom (fun _ => CPolynomial.X) p

/-- Compute the round polynomial from a "current" multivariate polynomial.
Variable 0 is the free variable; variables 1 through k are summed over D.
Returns a univariate `CPolynomial`. -/
def roundPoly (D : Fin m → R) (k : ℕ) (p : CMvPolynomial (k + 1) R) : CPolynomial R :=
  toUnivariate (sumAllButFirst D k p)

/-! ### Correctness lemmas (univariate bridge) -/

/-- `toUnivariate` preserves evaluation at the unique remaining variable.
Proof strategy: use `eval₂_equiv` to reduce to `MvPolynomial.eval₂`, then relate
to `CPolynomial.eval` via `CPolynomial.eval₂_toPoly`. -/
theorem toUnivariate_eval (p : CMvPolynomial 1 R) (x : R) :
    CPolynomial.eval x (toUnivariate p) = p.eval (fun _ : Fin 1 => x) := by
  sorry

/-- The symbolic round polynomial computes the exact remaining-sum function. -/
theorem roundPoly_eval (D : Fin m → R) (k : ℕ) (p : CMvPolynomial (k + 1) R) (x : R) :
    CPolynomial.eval x (roundPoly D k p) =
      (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
        p.eval (Fin.cons x (D ∘ z))) := by
  unfold roundPoly
  rw [toUnivariate_eval, sumAllButFirst_eval]

/-! ### Degree preservation (univariate bridge) -/

/-- `toUnivariate` preserves degree bounds: if every monomial of `p : CMvPolynomial 1 R`
has `mono.degreeOf 0 ≤ deg`, then `(toUnivariate p).natDegree ≤ deg`.
Proof strategy: use `eval₂_equiv` and `Polynomial.natDegree` bounds on the Mathlib side. -/
theorem toUnivariate_natDegree_le {deg : ℕ}
    (p : CMvPolynomial 1 R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf 0 ≤ deg) :
    (toUnivariate p).natDegree ≤ deg := by
  sorry

/-- The round polynomial has degree at most `deg` when the original polynomial has
individual degree at most `deg` in variable 0. -/
theorem roundPoly_natDegree_le {deg : ℕ} (D : Fin m → R) {k : ℕ}
    (p : CMvPolynomial (k + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf 0 ≤ deg) :
    (roundPoly D k p).natDegree ≤ deg := by
  sorry

end Univariate

end CPoly.CMvPolynomial

/-! ## Sum-check prover residual state -/

namespace Sumcheck

/-- The prover's residual polynomial state during sum-check execution.

After round `i`, the prover holds a polynomial in `k` remaining variables
(where `k = n - i`) with individual degree at most `deg`. At each round:
1. Compute the round polynomial via `roundPoly D` (keep variable 0 free, sum the rest).
2. After receiving the verifier's challenge `r`, update via `partialEvalFirst r`. -/
structure ResidualPoly (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (deg : ℕ) where
  numVars : ℕ
  poly : CMvPolynomial numVars R
  degreeBound : CPoly.CMvPolynomial.IndividualDegreeLE (R := R) deg poly

end Sumcheck
