/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.Defs
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

variable [Fintype R] [SampleableType R] [DecidableEq R]

/-! ### Languages and error parameters -/

/-- Output language for the reduced claim after `n` rounds.

Since sumcheck is modeled as a **reduction**, the verifier outputs the random point
`r` (the sampled challenges) together with the final value `v`. The remaining
obligation is the evaluation relation `poly(r) = v`. -/
def outputLang (poly : CMvPolynomial n R) : Set (EvalClaim (R := R) n) :=
  { c | CMvPolynomial.eval (fun i => c.challenges.get i) poly = c.value }

/-- The per-round soundness error: `deg / |F|`. -/
def roundSoundnessError : ℝ≥0 :=
  ⟨deg / Fintype.card R, by positivity⟩

/-- Per-challenge round-by-round error function (uniform across rounds). -/
def rbrSoundnessError : ChallengeIndex (generalPSpec R deg n) → ℝ≥0 :=
  fun _ => roundSoundnessError (R := R) (deg := deg)

/-- Overall soundness error as the sum of per-challenge RBR errors. -/
def soundnessError : ℝ≥0 :=
  Finset.sum Finset.univ (rbrSoundnessError (R := R) (deg := deg) (n := n))

/-! ### Empty-oracle embedding for framework-native statements

Sumcheck's plain verifier lives in `Verifier Id ...`. The framework security notions
(`Verifier.rbrSoundness` / `Verifier.soundness`) are phrased over
`Verifier (OracleComp oSpec) ...`, so we embed the plain verifier into the empty-oracle
setting. -/

private abbrev EmptySpec : OracleSpec PEmpty := []ₒ

private def emptyImpl : QueryImpl EmptySpec (StateT Unit ProbComp) :=
  fun q => PEmpty.elim q

private def generalVerifierAsOracle (D : Fin m → R) :
    Verifier (OracleComp EmptySpec) R (EvalClaim (R := R) n) (generalPSpec R deg n) :=
  fun target tr => OptionT.mk <| pure
    ((generalVerifier (R := R) (deg := deg) (n := n) (m := m) D target tr).run)

/-- Round-by-round soundness of the `n`-round sumcheck verifier in the framework form. -/
theorem generalVerifier_rbrSoundness
    (poly : CMvPolynomial n R) (D : Fin m → R) :
    rbrSoundness
      (impl := emptyImpl)
      (langIn := Sumcheck.inputLang poly D)
      (langOut := outputLang (R := R) (n := n) poly)
      (verifier := generalVerifierAsOracle (R := R) (deg := deg) (n := n) (m := m) D)
      (Inv := fun _ : Unit => True)
      (rbrError := rbrSoundnessError (R := R) (deg := deg) (n := n)) := by
  sorry

/-! This is expected to be obtained from `generalVerifier_rbrSoundness` via the
framework theorem `rbrSoundness_implies_soundness`. -/
/-- Soundness of the general sumcheck verifier in framework form. -/
theorem generalVerifier_soundness
    (poly : CMvPolynomial n R) (D : Fin m → R) :
    Verifier.soundness
      (init := (pure () : ProbComp Unit))
      (impl := emptyImpl)
      (langIn := Sumcheck.inputLang poly D)
      (langOut := outputLang (R := R) (n := n) poly)
      (verifier := generalVerifierAsOracle (R := R) (deg := deg) (n := n) (m := m) D)
      (soundnessError := soundnessError (R := R) (deg := deg) (n := n)) := by
  sorry

end Soundness

end Sumcheck
