/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.Defs
import ArkLib.Refactor.Sumcheck.SingleRound

/-!
# Multi-Round Sumcheck Protocol

Composes `n` single rounds of the sumcheck protocol into the full multi-round protocol.

- `generalPSpec` — the `n`-round protocol spec (replicate `pSpec` `n` times)
- `generalVerifier` — composed `n`-round plain verifier via `Verifier.compNth`
- `generalOracleVerifier` — composed `n`-round oracle verifier via `OracleVerifier.compNth`
-/

open CompPoly CPoly ProtocolSpec OracleComp OracleSpec

namespace Sumcheck

variable (R : Type) [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
variable (deg : ℕ)

/-! ## Multi-round protocol spec -/

@[reducible] def generalPSpec (n : ℕ) : ProtocolSpec :=
  ProtocolSpec.replicate n (pSpec R deg)

/-! ## Multi-round plain verifier -/

variable {R} {deg}
variable {n m : ℕ}

private def generalVerifierAux (D : Fin m → R) :
    (k : Nat) →
    (i : Nat) →
    (h : i + k = n) →
    Vector R i →
    R →
    Transcript (generalPSpec R deg k) →
    Option (EvalClaim (R := R) n)
  | 0, i, h, prevChallenges, target, _ =>
      let hi : i = n := by simpa using h
      some { challenges := by simpa [hi] using prevChallenges
             value := target }
  | k + 1, i, h, prevChallenges, target, tr => do
      let (tr₁, tr₂) :=
        Transcript.split (pSpec₁ := pSpec R deg) (pSpec₂ := generalPSpec R deg k) tr
      let out ← (Sumcheck.verifier (R := R) (deg := deg) D target tr₁).run
      have h' : (i + 1) + k = n := by
        -- from `h : i + (k + 1) = n`
        omega
      generalVerifierAux D k (i + 1) h' (prevChallenges.push out.challenge) out.target tr₂

/-- Multi-round sumcheck verifier.

Runs the single-round checks sequentially, accumulating the verifier challenges into
`EvalClaim.challenges` and returning the final value claim `EvalClaim.value`. The
final check against the original multivariate polynomial is deferred to the output
relation/language of the reduction. -/
def generalVerifier (D : Fin m → R) :
    Verifier Id R (EvalClaim (R := R) n) (generalPSpec R deg n) :=
  fun target tr =>
    OptionT.mk <| generalVerifierAux (R := R) (deg := deg) (n := n) (m := m) D n 0
      (by simp) ⟨#[], rfl⟩ target tr

/-! ## Multi-round oracle verifier -/

section OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- Single-round oracle verifier that outputs `R` for `compNth` composition.
Queries the round polynomial at domain points, checks the sum, and returns the new target. -/
noncomputable def roundOracleVerifier (D : Fin m → R) :
    OracleVerifier oSpec
      R (fun (_ : Unit) => OStmt R n)
      R (fun (_ : Unit) => OStmt R n)
      (pSpec R deg) where
  verify := fun target challenges => do
    let result ← (oracleVerifier (n := n) (m := m) (deg := deg) (ι := ι) (oSpec := oSpec)
      D).verify target challenges
    pure result.target
  simulate := fun q =>
    liftM (query (spec := [fun (_ : Unit) => OStmt R n]ₒ +
      oracleSpecOfMessages (pSpec R deg)) (Sum.inl q))
  reify := fun oStmtData _ => some oStmtData

noncomputable def generalOracleVerifier (D : Fin m → R) :
    OracleVerifier oSpec
      R (fun (_ : Unit) => OStmt R n)
      R (fun (_ : Unit) => OStmt R n)
      (generalPSpec R deg n) :=
  OracleVerifier.compNth n (roundOracleVerifier D)

end OracleVerifier

/-! ## Multi-round prover

The multi-round prover accumulates challenges across rounds. Each round computes
the round polynomial using all previously received challenges, sends it, receives a
new challenge, and continues. Built by structural recursion on the remaining number
of rounds `k`, with `prevChallenges` tracking all challenges seen so far. -/

def multiRoundProver
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    (k : Nat) → (i : Nat) → (h : i + k = n) → Vector R i → R →
    Prover Id (EvalClaim (R := R) n × Unit) (generalPSpec R deg k)
  | 0, i, h, prevChallenges, target =>
      let hi : i = n := by simpa using h
      ({ challenges := by simpa [hi] using prevChallenges
         value := target }, ())
  | k + 1, i, h, prevChallenges, target =>
      let roundPoly := computeRoundPoly poly prevChallenges D evalPoints
      (roundPoly, fun chal =>
        have h' : (i + 1) + k = n := by omega
        multiRoundProver poly D evalPoints k (i + 1) h' (prevChallenges.push chal)
          (CPolynomial.eval chal roundPoly.val))

/-! ## Multi-round reduction -/

def generalReduction
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    Reduction Id R Unit (EvalClaim (R := R) n) Unit (generalPSpec R deg n) where
  prover := fun (target, ()) =>
    multiRoundProver (R := R) (deg := deg) (n := n) (m := m) poly D evalPoints n 0
      (by simp) ⟨#[], rfl⟩ target
  verifier := generalVerifier D

end Sumcheck
