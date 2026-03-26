/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Probability.Notation
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval



/-!
# Proximity Generators fundamental definitions

Define the fundamental definitions for generators functions.

## Main Definitions

- `generator`: a generator `G` over a field `F` with output size `ℓ` is a function that maps a seed
`x` in a set `S` to a coefficient vector in `F^ℓ`
- `zero-evading generators`: a generator is zero-evading with a zero-evading error `ε_ze` if the
probability of obtaining a zero output from a non-zero vector is bounded above by `ε_ze`
- `polynomial generator`: the output is defined by `ℓ` linearly independent multivariate polynomials
- `MDS generator`: A generator is MDS if the matrix whose rows are the outputs of the generator
function is a generator matrix for an MDS code
- `MCA generator`

## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BSGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

namespace CoreDefinitions

open NNReal ENNReal
open scoped ProbabilityTheory

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ℓ : Type} [Fintype ℓ]

/-- The type of generators, where a generator `G` over a field `F` with output size `ℓ` is a function
that maps a seed `x` in a set `S` to a coefficient vector in `F^ℓ`.
Definition 3.10 [BSGM25]. -/
def Generator (S ℓ F : Type) : Type := S → (ℓ → F)

/-- A generator `G` is zero-evading with a zero-evading error `ε_ze` if the probability of obtaining
a zero output from a non-zero vector is bounded above by `ε_ze`.
Definition 3.11 [BSGM25]. -/
def IsZeroEvadingGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_ze : ℝ≥0∞) :
    Prop :=
    ε_ze ∈ Set.Icc 0 1 ∧
    (SupSet.sSup {y | ∃ v : ℓ → F, v ≠ 0 ∧ y = Pr_{let x ←$ᵖ S}[dotProduct (G x) v = 0]}) ≤ ε_ze

/-- Let the set `S` be a product of `ℓ` subsets of `F`. A polynomial generator is a generator if
there exist `ℓ` linearly independent multivariate polynomials, such that the output is an evaluation
of the seed at each of these polynomials.
Definition 3.19 [BSGM25]. -/
def IsPolynomialGenerator {s : ℕ} {S : Fin s → Set F} (G : Generator (∀ i, S i) ℓ F) : Prop :=
  ∃ P : ℓ → MvPolynomial (Fin s) F, LinearIndependent F P ∧
  ∀ x : (∀ i, S i), G x = MvPolynomial.eval (fun i ↦ x i) ∘ P

/-- A matrix whose rows are the outputs of the generator function.
Defined inside Definition 3.5 [BSGM25]. -/
def M_G {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) : Matrix S ℓ F :=
  Matrix.of G

/-- A generator `G` is MDS if the matrix `M_G` whose rows are the outputs of the generator
function is a generator matrix for an MDS code.
Definition 3.5 [BSGM25]. -/
def IsMDSGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) : Prop :=
 LinearCode.IsMDS (LinearCode.fromRowGenMat (M_G G))

/-- The condition for MCA generator. -/
def Condition {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (U : ℓ → ι → F)
  (T : Finset ι) (γ : ℝ) (LC : LinearCode ι F) (x : S) : Prop :=
  let v := Matrix.vecMul (G x) (Matrix.of U)
  Finset.card T ≥ (Fintype.card ι) * (1 - γ) ∧
  Code.projectedWord v T ∈ Code.projectedCode LC T ∧
  ∃ j : ℓ, Code.projectedWord (U j) T ∉ Code.projectedCode LC T

/-- Definition 3.14 [BSGM25]. -/
def IsMCAGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
  (ε_mca : Set.Icc 0 1 → Set.Icc 0 1) (U : ℓ → ι → F) (T : Finset ι) (LC : LinearCode ι F) : Prop :=
  ∀ γ ∈ Set.Icc 0 1,
  Pr_{let x ←$ᵖ S}[(Condition G U T γ LC x) ] ≤ Real.toEReal (ε_mca γ)

end

end CoreDefinitions
