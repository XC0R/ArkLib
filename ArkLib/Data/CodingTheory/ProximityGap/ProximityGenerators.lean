/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

-- import ArkLib.Data.CodingTheory.Basic
-- import ArkLib.Data.CodingTheory.GuruswamiSudan
-- import ArkLib.Data.CodingTheory.Prelims
-- import ArkLib.Data.CodingTheory.ReedSolomon
-- import ArkLib.Data.CodingTheory.InterleavedCode
-- import ArkLib.Data.Polynomial.Bivariate
-- import ArkLib.Data.Polynomial.RationalFunctions
-- import ArkLib.Data.Probability.Notation
-- import Mathlib.Algebra.Field.Basic
-- import Mathlib.Algebra.Lie.OfAssociative
-- import Mathlib.Algebra.Module.Submodule.Defs
-- import Mathlib.Algebra.Polynomial.Basic
-- import Mathlib.Data.Finset.BooleanAlgebra
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Data.Set.Defs
-- import Mathlib.FieldTheory.RatFunc.AsPolynomial
-- import Mathlib.FieldTheory.Separable
-- import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
-- import Mathlib.Probability.Distributions.Uniform
-- import Mathlib.RingTheory.Henselian
-- import Mathlib.RingTheory.PowerSeries.Basic
-- import Mathlib.RingTheory.PowerSeries.Substitution
-- import Mathlib.LinearAlgebra.Matrix.Vec
-- import Mathlib.Data.Matrix.Mul
-- import Mathlib.Order.SetNotation

import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Probability.Notation
import Mathlib.Algebra.Module.Defs
import Mathlib.Topology.UnitInterval
import Mathlib

/-!
# Proximity Generators fundamental definitions

Define the fundamental definitions for proximity gap properties of generic codes and
module codes over (scalar) rings.

## Main Definitions

### Proximity Gap Definitions
- `proximityMeasure`: Counts vectors close to linear combinations with code `C`


## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed–Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654, version 20210703:203025.

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BSGM25]
-/

namespace Generator

open NNReal Finset Function ENNReal
open scoped ProbabilityTheory
open scoped BigOperators
open unitInterval

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ℓ : Type} [Fintype ℓ]

def Generator (S ℓ F : Type) : Type := S → (ℓ → F)

-- noncomputable instance {S : Set (ι → F)} : Fintype S := Fintype.ofFinite ↑S

-- noncomputable def probs {S : Set (ℓ → F)} [Nonempty S] (G : Generator S) : Set ENNReal :=
--   {y | ∃ v : ℓ → F, v ≠ 0 ∧ y = Pr_{let x ←$ᵖ S}[dotProduct (G x) v = 0]}

def IsZeroEvadingGen {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_ze : ℝ≥0∞) : Prop :=
  ε_ze ∈ Set.Icc 0 1 ∧
  (SupSet.sSup {y | ∃ v : ℓ → F, v ≠ 0 ∧ y = Pr_{let x ←$ᵖ S}[dotProduct (G x) v = 0]}) ≤ ε_ze

def IsPolynomialGen {s : ℕ} {S : Fin s → Set F} (G : Generator (∀ i, S i) ℓ F) : Prop :=
  ∃ P : ℓ → MvPolynomial (Fin s) F, LinearIndependent F P ∧
  ∀ x : (∀ i, S i), G x = MvPolynomial.eval (fun i ↦ x i) ∘ P

def M_G {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) : Matrix S ℓ F :=
  Matrix.of G

def IsMDSGen {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) : Prop :=
 IsMDS (LinearCode.fromRowGenMat (M_G G))


/-- A subset of `ι` is dense if `|T| ≥ |ι| * (1 − γ)`, for some γ -/
def IsDenseSet (T : Finset ι) (γ : ℝ) : Prop := Finset.card T ≥ (Fintype.card ι) * (1 - γ)


def Condition {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (U : ℓ → ι → F)
  (T : Finset ι) (γ : ℝ) (LC : LinearCode ι F) (x : S) : Prop :=
  let v := Matrix.vecMul (G x) (Matrix.of U)
  Finset.card T ≥ (Fintype.card ι) * (1 - γ) ∧
  Code.projectedWord v T ∈ Code.projectedCode LC T ∧
  ∃ j : ℓ, Code.projectedWord (U j) T ∉ Code.projectedCode LC T

def IsMCAGen {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
  (ε_mca : Set.Icc 0 1 → Set.Icc 0 1) (U : ℓ → ι → F) (T : Finset ι) (LC : LinearCode ι F) : Prop :=
  ∀ γ ∈ Set.Icc 0 1,
  Pr_{let x ←$ᵖ S}[(Condition G U T γ LC x) ] ≤ Real.toEReal (ε_mca γ)


-- def zeroEvading' {S : Set (ℓ → F)} [Nonempty S] (G : Generator S) (ε_ze : ℝ≥0∞) : Prop :=
--   ε_ze ∈ Set.Icc 0 1 ∧
--   (SupSet.sSup
--     (
--       Set.image
--         (fun (v : ℓ → F) ↦ (Pr_{let x ←$ᵖ S}[dotProduct (G x) v = 0]))
--         {v | v ≠ 0}
--     )
--   ) ≤ ε_ze

end

end Generator
