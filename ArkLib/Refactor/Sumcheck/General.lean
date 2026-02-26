/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
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

/-- Single-round verifier that outputs `R` (the new target) for `compNth` composition.
Projects `StmtOut.target` from the full verifier's output. -/
def roundVerifier (D : Fin m → R) :
    Verifier Id R R (pSpec R deg) :=
  fun target tr => do
    let result ← verifier D target tr
    pure result.target

def generalVerifier (D : Fin m → R) :
    Verifier Id R R (generalPSpec R deg n) :=
  Verifier.compNth n (roundVerifier D)

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

noncomputable def multiRoundProver
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    {i : ℕ} → Vector R i → (k : ℕ) → R →
    Prover Id (R × Unit) (generalPSpec R deg k)
  | _, _, 0, target => (target, ())
  | _, prevChallenges, k + 1, _ =>
    let roundPoly := computeRoundPoly poly prevChallenges D evalPoints
    (roundPoly, fun chal =>
      multiRoundProver poly D evalPoints (prevChallenges.push chal) k
        (CPolynomial.eval chal roundPoly.val))

/-! ## Multi-round reduction -/

noncomputable def generalReduction
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    Reduction Id R Unit R Unit (generalPSpec R deg n) where
  prover := fun (target, ()) =>
    multiRoundProver poly D evalPoints ⟨#[], rfl⟩ n target
  verifier := generalVerifier D

end Sumcheck
