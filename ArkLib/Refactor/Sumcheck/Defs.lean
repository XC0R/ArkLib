/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.PartialEval
import ArkLib.Refactor.Reduction

/-!
# Sumcheck Protocol Definitions

Core types for the general sumcheck protocol:

- `StmtIn` / `StmtOut` — input/output statement types for a single round
- `OStmt` — the oracle statement (the multivariate polynomial being summed)
- `pSpec` — the per-round protocol spec (one degree-bounded polynomial + one challenge)
- `computeRoundPoly` — evaluate-and-interpolate strategy for computing the round polynomial

## Parameters

- `R : Type` — the coefficient field
- `n : ℕ` — number of variables (= number of rounds)
- `deg : ℕ` — degree bound on the round polynomial
- `m : ℕ` — size of the summation domain
- `D : Fin m → R` — the summation domain (injective)
-/

open CompPoly CPoly ProtocolSpec

namespace Sumcheck

variable (R : Type) [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]

/-! ## Statement types -/

/-- The input statement for a single sumcheck round: the target sum value that the
prover claims the polynomial sums to over the remaining variables. -/
abbrev StmtIn := R

/-- The output statement of a single sumcheck round, carrying the new target value
and the challenge used to reduce. -/
structure StmtOut where
  target : R
  challenge : R

/-! ## Multi-round state -/

/-- The multi-round sumcheck statement after `i` rounds: the challenges so far and the current
remaining-sum target. This is the natural “state statement” for composing rounds. -/
structure RoundState where
  i : ℕ
  challenges : Vector R i
  target : R

/-- The oracle statement: the multivariate polynomial being summed.
No degree-bound subtype — degree bounds are enforced by the relation instead. -/
abbrev OStmt (n : ℕ) := CMvPolynomial n R

/-! ## Protocol spec -/

variable (deg : ℕ)

/-- The per-round protocol spec: the prover sends a degree-bounded univariate polynomial,
then the verifier sends a field element as a challenge. -/
@[reducible] def pSpec : ProtocolSpec :=
  [ProtocolSpec.msg (CDegreeLE R deg), ProtocolSpec.chal R]

/-! ## Relations -/

variable {R}

/-- The input language for the full sumcheck protocol: the set of valid target sums.
`target ∈ inputLang poly D` iff `target` equals the sum of `poly` over the full
domain `D^n`. -/
def inputLang {n m : ℕ} (poly : CMvPolynomial n R) (D : Fin m → R) : Set R :=
  { target | target = (Finset.univ : Finset (Fin n → Fin m)).sum (fun z =>
    CMvPolynomial.eval (D ∘ z) poly) }

/-- The input relation for the full sumcheck protocol (with trivial witness). -/
def inputRelation {n m : ℕ} (poly : CMvPolynomial n R) (D : Fin m → R) : Set (R × Unit) :=
  { p | p.1 ∈ inputLang poly D }

variable (R)

/-! ## Computing the round polynomial -/

variable {R} {deg}

/-- Compute the round polynomial using the evaluate-and-interpolate strategy.

Given the multivariate polynomial `poly`, previously fixed challenges `prevChallenges`,
and a summation domain `D`, evaluates the "partial sum" at `deg + 1` distinct points
and interpolates them into a univariate polynomial of degree ≤ `deg`.

The partial sum at point `t` is:
  `∑ z ∈ D^(remaining vars), poly(prevChallenges ++ [t] ++ z)` -/
def computeRoundPoly {n : ℕ} {m : ℕ} {i : ℕ}
    (poly : CMvPolynomial n R) (prevChallenges : Vector R i)
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) : CDegreeLE R deg :=
  let values : Vector R (deg + 1) := evalPoints.map (fun t =>
    (Finset.univ : Finset (Fin (n - i - 1) → Fin m)).sum (fun z =>
      CMvPolynomial.eval
        (fun (k : Fin n) =>
          if h₁ : k.val < i then prevChallenges[k.val]
          else if k.val = i then t
          else
            let remaining := k.val - i - 1
            if h₂ : remaining < n - i - 1 then D (z ⟨remaining, h₂⟩)
            else 0)
        poly))
  ⟨CPolynomial.lagrangeInterpolate evalPoints values,
    CPolynomial.lagrangeInterpolate_natDegree evalPoints values⟩

/-! ## Symbolic prover state -/

/-- A dependent pair packaging a multivariate polynomial with its current number of variables,
together with a witness that every remaining variable still has individual degree at most `deg`.
Used as the prover's witness type: each round, `k` decreases by 1 via `partialEvalFirst`,
and the degree witness is preserved by `partialEvalFirst_individualDegreeLE`. -/
structure SymbolicPoly (deg : ℕ) where
  k : ℕ
  poly : CMvPolynomial k R
  hDegree : CMvPolynomial.IndividualDegreeLE (R := R) deg poly

end Sumcheck
