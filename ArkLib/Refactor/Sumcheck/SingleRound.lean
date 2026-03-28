/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.Defs

/-!
# Single Round of the Sumcheck Protocol

Defines the components for one round of the sumcheck protocol:

- `prover` — the honest prover (produces a `Prover` coinductive value)
- `verifier` — the plain verifier (sees the round polynomial directly)
- `oracleVerifier` — the oracle verifier (queries the round polynomial)
- `reduction` — pairs prover with plain verifier
- `oracleReduction` — pairs oracle prover with oracle verifier
-/

open CompPoly CPoly ProtocolSpec OracleComp OracleSpec

namespace Sumcheck

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
variable {n m : ℕ} {deg : ℕ}

/-! ## Prover -/

/-- The honest prover for a single sumcheck round.

Computes the round polynomial via evaluate-and-interpolate, sends it, and
when given a challenge `r`, produces the output statement with new target `p(r)`. -/
def prover {i : ℕ}
    (poly : OStmt R deg n) (prevChallenges : Vector R i)
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    Prover Id (StmtOut R) (pSpec R deg) :=
  let roundPoly := computeRoundPoly poly prevChallenges D evalPoints
  (roundPoly, pure (fun chal =>
    pure { target := CPolynomial.eval chal roundPoly.val, challenge := chal }))

/-! ## Plain verifier -/

/-- The plain verifier for a single sumcheck round.

Reads the round polynomial and challenge from the transcript, checks that the
polynomial's sum over the domain `D` equals the target, then returns the new
target `p(challenge)`. -/
def verifier (D : Fin m → R) :
    Verifier Id (StmtIn R) (StmtOut R) (pSpec R deg) :=
  fun target tr =>
    let poly : CDegreeLE R deg := tr.head
    let chal : R := (tr.tail).head
    if (Finset.univ : Finset (Fin m)).sum (fun i => CPolynomial.eval (D i) poly.val) = target
    then pure { target := CPolynomial.eval chal poly.val, challenge := chal }
    else failure

/-! ## Oracle verifier

The oracle verifier for a single sumcheck round. Instead of reading the round polynomial
directly, queries it at the domain points to check the sum, and at the challenge point to
compute the new target. The oracle statement (multivariate polynomial) passes through
unchanged. -/

section OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

def queryRoundPoly (x : R) :
    OracleComp (oSpec + [fun (_ : Unit) => OStmt R deg n]ₒ +
      oracleSpecOfMessages (pSpec R deg)) R := by
  change OracleComp _ (oracleSpecOfMessages (pSpec R deg) (Sum.inl x))
  exact OracleComp.lift (OracleQuery.query (spec :=
    oSpec + [fun (_ : Unit) => OStmt R deg n]ₒ + oracleSpecOfMessages (pSpec R deg))
    (Sum.inr (Sum.inl x)))

def oracleVerifier (D : Fin m → R) :
    OracleVerifier oSpec
      (StmtIn R) (fun (_ : Unit) => OStmt R deg n)
      (StmtOut R) (fun (_ : Unit) => OStmt R deg n)
      (pSpec R deg) :=
  OracleVerifier.keepInputOracle (oSpec := oSpec)
    (StmtIn := StmtIn R) (StmtOut := StmtOut R)
    (OStmt := fun (_ : Unit) => OStmt R deg n) (pSpec := pSpec R deg)
    (fun target challenges => do
      let evals ← (List.finRange m).mapM (fun i =>
        OptionT.lift (queryRoundPoly (oSpec := oSpec) (n := n) (deg := deg)
          (R := R) (D i)))
      guard (evals.sum = target)
      let chal := challenges.head
      let newTarget ←
        OptionT.lift (queryRoundPoly (oSpec := oSpec) (n := n) (deg := deg)
          (R := R) chal)
      pure { target := newTarget, challenge := chal })

end OracleVerifier

/-! ## Oracle reduction -/

section OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}

/-- A single-round oracle prover for sumcheck.

The concrete multivariate polynomial is carried in the oracle statement data and is
passed through unchanged; the honest prover computes the round polynomial from it and
returns the updated target/challenge pair. -/
def oracleProver {i : ℕ}
    (prevChallenges : Vector R i)
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    OracleProver oSpec
      (StmtIn R) (fun (_ : Unit) => OStmt R deg n) Unit
      (StmtOut R) (fun (_ : Unit) => OStmt R deg n) Unit
      (pSpec R deg) :=
  fun ⟨⟨_, oStmtData⟩, ()⟩ => do
    let roundPoly := computeRoundPoly (R := R) (deg := deg) (n := n) (m := m) (i := i)
      (oStmtData ()) prevChallenges D evalPoints
    pure (roundPoly, pure (fun chal =>
      pure (({
          target := CPolynomial.eval chal roundPoly.val
          challenge := chal
        }, oStmtData), ())))

/-- A single-round oracle reduction pairing the oracle prover with the oracle
verifier. The oracle statement is the underlying multivariate polynomial and is
preserved across the round. -/
def oracleReduction {i : ℕ}
    (prevChallenges : Vector R i)
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    OracleReduction oSpec
      (StmtIn R) (fun (_ : Unit) => OStmt R deg n) Unit
      (StmtOut R) (fun (_ : Unit) => OStmt R deg n) Unit
      (pSpec R deg) where
  prover := oracleProver (oSpec := oSpec) (prevChallenges := prevChallenges) D evalPoints
  verifier := oracleVerifier (oSpec := oSpec) D

end OracleReduction

/-! ## Reduction -/

/-- A single-round sumcheck reduction pairing the honest prover with the plain verifier.

The witness carries the multivariate polynomial, previously fixed challenges,
domain, and evaluation points needed by the prover. -/
def singleRoundReduction {i : ℕ}
    (poly : OStmt R deg n) (prevChallenges : Vector R i)
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    Reduction Id (StmtIn R) Unit (StmtOut R) Unit (pSpec R deg) where
  prover := fun (_, _) => pure <|
    Prover.mapOutput (fun s => (s, ())) (pSpec R deg) <|
      prover poly prevChallenges D evalPoints
  verifier := verifier D

end Sumcheck
