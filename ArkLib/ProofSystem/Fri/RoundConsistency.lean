import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.Polynomial.SplitFold

/-!
# FRI Round Consistency

Computable round-consistency checks for FRI. The executable path evaluates the
Lagrange basis directly on the queried fiber values instead of constructing a
Mathlib polynomial. Semantic equivalence to the interpolation-based view is kept
as theorem work.
-/

open Polynomial
open scoped BigOperators

namespace RoundConsistency

variable {𝔽 : Type} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Evaluate the `j`-th Lagrange basis polynomial at `γ`, using the point
coordinates stored in `pts`. -/
def lagrangeWeight (γ : 𝔽) (pts : List (𝔽 × 𝔽)) (j : Fin pts.length) : 𝔽 :=
  ∏ k : Fin pts.length,
    if h : k = j then 1 else (γ - (pts.get k).1) / ((pts.get j).1 - (pts.get k).1)

/-- Evaluate the unique degree-`< m` interpolant through `pts` at `γ`, directly
from the Lagrange basis formula. -/
def interpolatedValue (γ : 𝔽) (pts : List (𝔽 × 𝔽)) : 𝔽 :=
  ∑ j : Fin pts.length, (pts.get j).2 * lagrangeWeight γ pts j

/-- The generalized round-consistency check: the interpolated value at `γ` must
equal `β`. -/
def roundConsistencyCheck (γ : 𝔽) (pts : List (𝔽 × 𝔽)) (β : 𝔽) : Bool :=
  interpolatedValue γ pts == β

/--
Completeness of the generalized round-consistency check for honest evaluations.

This is the semantic bridge to the existing Mathlib-polynomial formulation. It
is intentionally deferred while the executable FRI layer is being rebuilt around
computable codewords and index-based domains.
-/
lemma generalised_round_consistency_completeness
    [DecidableEq 𝔽]
    {f : Polynomial 𝔽}
    {n : ℕ} [NeZero n]
    {γ s₀ : 𝔽}
    {ω : Fin n ↪ 𝔽}
    (h : ∀ i, (ω i) ^ n = 1)
    (h₁ : s₀ ≠ 0) :
    roundConsistencyCheck γ
      ((List.finRange n).map fun i => (ω i * s₀, f.eval (ω i * s₀)))
      ((foldNth n f γ).eval (s₀ ^ n)) = true := by
  sorry

end RoundConsistency
