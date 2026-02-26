/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.General
import ArkLib.Refactor.Security.StateFunction

/-!
# Security Theorems for the Sumcheck Protocol

Security properties for the general sumcheck protocol:

- **Perfect completeness**: If the polynomial truly sums to the claimed target over `D^n`,
  the honest prover always makes the verifier accept (for *all* challenge sequences).
- **Round-by-round soundness**: Each challenge round can "flip" an incorrect claim to
  a correct-looking one with probability at most `deg / |F|`.
- **Soundness** (corollary): A false claim passes all `n` rounds with probability
  at most `n · deg / |F|`.

## Overview

The sumcheck protocol is a reduction from the *sumcheck claim*
  `∑_{x ∈ D^n} poly(x) = target`
to an *evaluation claim*
  `poly(r₁, …, rₙ) = finalTarget`
where `r₁, …, rₙ` are the verifier's challenges.

Sumcheck is a pure interactive proof — no shared oracle is needed. Perfect
completeness holds deterministically for all challenge sequences. Soundness
is over the uniform distribution on challenges.
-/

noncomputable section

open CompPoly CPoly ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R]
variable {n m : ℕ} {deg : ℕ}

/-! ## Challenge sampling instances -/

noncomputable instance instChallengesSampleableGeneralPSpec [SampleableType R] :
    ChallengesSampleable (generalPSpec R deg n) :=
  ChallengesSampleable.ofReplicate n

/-! ## Perfect Completeness

The honest prover makes the verifier accept for every valid input. Since sumcheck has a
deterministic prover and verifier, this holds for *all* challenge sequences. We formulate
it using `Reduction.run` which pairs the prover and verifier. -/

/-- Perfect completeness for the general sumcheck reduction.

If `target = ∑_{x ∈ D^n} poly(x)`, then for any challenge sequence, running the
honest prover against `generalVerifier` yields `some` (acceptance). -/
theorem generalReduction_perfectCompleteness [DecidableEq R]
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1))
    (target : R) (h_valid : target ∈ Sumcheck.inputLang poly D)
    (challenges : Challenges (generalPSpec R deg n)) :
    ((generalReduction poly D evalPoints).run target () challenges).1.isSome := by
  sorry

/-! ## Soundness

The verifier rejects any false claim with high probability over the random challenges.

The soundness argument proceeds round by round. At each round, the adversary commits a
round polynomial `p_i`. If the sum `∑_{x ∈ D} p_i(x)` doesn't match the current target,
then by the Schwartz-Zippel lemma, a uniformly random evaluation point `r_i` yields a
consistent next target with probability at most `deg / |F|`.

By a union bound over `n` rounds, the total soundness error is `n · deg / |F|`. -/

section Soundness

variable [Fintype R] [SampleableType R]

/-- The per-round soundness error: `deg / |F|`. -/
def roundSoundnessError : ℝ≥0 :=
  ⟨deg / Fintype.card R, by positivity⟩

/-- The overall soundness error for `n` rounds: `n · deg / |F|`. -/
def soundnessError : ℝ≥0 :=
  ⟨n * deg / Fintype.card R, by positivity⟩

/-- Core single-round soundness lemma (Schwartz-Zippel).

If a univariate polynomial `p` of degree `≤ deg` does not sum to `target` over the
domain, then for any value `v`, the probability that `p(r) = v` for a uniformly
random `r ← F` is at most `deg / |F|`. -/
theorem singleRound_soundness
    (D : Fin m → R)
    (roundPoly : CDegreeLE R deg)
    (target : R)
    (h_bad : (Finset.univ : Finset (Fin m)).sum
      (fun i => CPolynomial.eval (D i) roundPoly.val) ≠ target)
    (v : R) :
    Pr[fun r => CPolynomial.eval r roundPoly.val = v
      | ($ᵗ R : ProbComp R)
    ] ≤ roundSoundnessError (deg := deg) (R := R) := by
  sorry

/-- Soundness of the general sumcheck verifier.

If `target ∉ inputLang poly D` (the claimed sum is wrong), then for any (possibly
probabilistic) adversarial prover, the probability that `generalVerifier` accepts
is at most `n · deg / |F|`. -/
theorem generalVerifier_soundness [DecidableEq R]
    (poly : CMvPolynomial n R) (D : Fin m → R) :
    ∀ (Output : Type),
    ∀ prover : Prover ProbComp Output (generalPSpec R deg n),
    ∀ target ∉ Sumcheck.inputLang poly D,
    Pr[fun (verResult, _) => verResult.isSome
      | do
        let challenges ← sampleChallenges (generalPSpec R deg n)
        let (tr, out) ← Prover.run (generalPSpec R deg n) prover challenges
        return (generalVerifier (m := m) D target tr, out)
    ] ≤ soundnessError (n := n) (deg := deg) (R := R) := by
  sorry

end Soundness

end Sumcheck
