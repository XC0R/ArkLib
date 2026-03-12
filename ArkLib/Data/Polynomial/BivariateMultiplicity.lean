/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.BivariateDegree

/-!
  # Multiplicity and Discriminant Helpers for Bivariate Polynomials

  This file keeps the remaining multiplicity-facing Mathlib bivariate helpers that still have no
  upstream CompPoly replacement.
-/

open Polynomial
open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

/-- Root multiplicity of a bivariate polynomial. -/
def rootMultiplicity₀.{u} {F : Type u} [Semiring F] [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := weightedDegree f 1 1
  match deg with
  | none => none
  | some deg =>
      List.min?
        (List.filterMap
          (fun p ↦ if coeff f p.1 p.2 = 0 then none else some (p.1 + p.2))
          (List.product (List.range deg.succ) (List.range deg.succ)))

/-- Root multiplicity (order of vanishing) of a bivariate polynomial at `(x,y)`.
It is the smallest total degree `s+t` of a nonzero coefficient after shifting
the root to `(0,0)`. The zero polynomial has multiplicity `none`. -/
def rootMultiplicity.{u} {F : Type u} [CommSemiring F] [DecidableEq F]
    (f : F[X][Y]) (x y : F) : Option ℕ :=
  rootMultiplicity₀ <| (f.comp (Y + C (C y))).map (Polynomial.compRingHom (X + C x))

/-- If the multiplicity of a pair `(x,y)` is non-negative, then the pair is a root of `f`. -/
theorem rootMultiplicity_some_implies_root {F : Type} [CommRing F]
    {x y : F} {f : F[X][Y]} (h : 0 < ((f.eval (C y)).rootMultiplicity x)) :
    (f.eval (C y)).eval x = 0 := by
  simp_all only [rootMultiplicity_pos', ne_eq, IsRoot.def]

open Univariate in
/-- In the case of a bivariate polynomial we cannot easily use `discriminant`.
   We are using the fact that the resultant in question is always
   divisible by the leading coefficient of the polynomial. -/
def discr_y {F : Type} [CommRing F] (f : F[X][Y]) : F[X] :=
  by
    classical
    by_cases h : 0 < f.degree
    · exact Classical.choose (resultant_is_divisible_by_leadingCoeff f h)
    · exact 0

/-- Shift a bivariate polynomial by `(x, y)`. -/
noncomputable def shift {F : Type} [Field F] (f : F[X][Y]) (x y : F) : F[X][Y] :=
  (f.comp (X + C (C y))).map ((X + C x).compRingHom)

end
end Polynomial.Bivariate
