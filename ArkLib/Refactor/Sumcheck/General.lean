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

def initState (target : R) : RoundState (R := R) :=
  { i := 0, challenges := ⟨#[], rfl⟩, target := target }

/-- The single-round verifier, lifted to act on the state statement type `RoundState`. -/
def roundVerifierState (D : Fin m → R) :
    Verifier Id (RoundState (R := R)) (RoundState (R := R)) (pSpec (R := R) deg) :=
  fun st tr => do
    let p : CDegreeLE R deg := tr.head
    let chal : R := (tr.tail).head
    guard ((Finset.univ : Finset (Fin m)).sum (fun j => CPolynomial.eval (D j) p.val) = st.target)
    pure { i := st.i + 1
           challenges := st.challenges.push chal
           target := CPolynomial.eval chal p.val }

/-- Multi-round sumcheck verifier (as a state transformer).

Runs `n` single rounds and returns the final `RoundState`. The final check against the original
multivariate polynomial is deferred to the output language/relation. -/
def generalVerifier (D : Fin m → R) :
    Verifier Id R (RoundState (R := R)) (generalPSpec R deg n) :=
  fun target tr => do
    let st0 := initState (R := R) target
    (Verifier.compNth n (roundVerifierState (R := R) (deg := deg) D)) st0 tr

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

def roundProverStep
    (backend : ∀ i : ℕ, Vector R i → CDegreeLE R deg) :
    (RoundState (R := R) × Unit) → Id (Prover Id (RoundState (R := R) × Unit) (pSpec (R := R) deg))
  | (st, ()) =>
      let roundPoly := backend st.i st.challenges
      pure (roundPoly, pure (fun chal =>
        pure ({ i := st.i + 1
                challenges := st.challenges.push chal
                target := CPolynomial.eval chal roundPoly.val }, ())))

/-! ## Multi-round reduction -/

def generalReduction
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1))
    (backend : ∀ i : ℕ, Vector R i → CDegreeLE R deg :=
      fun i prev => computeRoundPoly (R := R) (deg := deg) (n := n) (m := m) (i := i)
        poly prev D evalPoints) :
    Reduction Id R Unit (RoundState (R := R)) Unit (generalPSpec R deg n) where
  prover := fun (target, ()) => do
    let st0 : RoundState (R := R) := initState (R := R) target
    let out0 : RoundState (R := R) × Unit := (st0, ())
    Prover.iterate (m := Id) (S := RoundState (R := R) × Unit)
      (pSpec (R := R) deg) n
      (roundProverStep (R := R) (deg := deg) backend)
      out0
  verifier := generalVerifier (R := R) (deg := deg) (n := n) (m := m) D

end Sumcheck
