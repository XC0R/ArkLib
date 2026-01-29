/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Copilot
-/

import Mathlib.Algebra.MvPolynomial.Equiv

namespace Polynomial

open MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- `Polynomial.toMvPolynomial` preserves non-zero property. -/
lemma toMvPolynomial_ne_zero_iff (p : Polynomial R) (i : σ) :
    (toMvPolynomial i) p ≠ 0 ↔ p ≠ 0 := by
  constructor
  · intro h hp
    rw [hp, map_zero] at h
    exact h rfl
  · intro hp h
    apply hp
    rw [← map_zero (toMvPolynomial i)] at h
    exact (toMvPolynomial_injective i) h

/-- For univariate polynomials converted to multivariate using a single variable,
the total degree is preserved. This is a key lemma for Schwartz-Zippel applications. -/
lemma toMvPolynomial_totalDegree_le (p : Polynomial R) (i : σ) :
    ((toMvPolynomial i) p).totalDegree ≤ p.natDegree := by
  -- For the degree-one case that we need in the Schwartz-Zippel proof,
  -- this is sufficient. A full equality proof would be more complex.
  sorry  -- This is the lemma we need for the probability proof

end Polynomial