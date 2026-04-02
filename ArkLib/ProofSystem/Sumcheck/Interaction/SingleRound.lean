/- 
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Oracle

/-!
# Interaction-Native Sum-Check: Single Round

A single round of sum-check, expressed canonically as an oracle continuation /
oracle reduction over the **original** polynomial oracle.

The round is indexed by a prefix transcript of already-sampled verifier
challenges. From that prefix, the prover derives the current residual
polynomial, sends the corresponding univariate round polynomial, receives the
next challenge, and keeps the original oracle statement unchanged.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Advance a residual polynomial by fixing its first variable to the sampled
challenge. This is the stateful prover update for one sum-check round. -/
def stepResidual (chal : R)
    {numVars : ℕ} (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    Sumcheck.PolyStmt R deg numVars :=
  ⟨CMvPolynomial.partialEvalFirst chal poly.1,
    CMvPolynomial.partialEvalFirst_individualDegreeLE chal poly.1 poly.2⟩

/-- The residual polynomial obtained by evaluating the first `prefixLen`
variables of the original polynomial at the sampled challenge prefix. -/
private def currentResidualGo :
    (prefixLen : Nat) →
    {n : Nat} →
    (h : prefixLen ≤ n) →
    (vals : Fin prefixLen → R) →
    (poly : Sumcheck.PolyStmt R deg n) →
    Sumcheck.PolyStmt R deg (n - prefixLen)
  | 0, n, _, _, poly => by
      simpa using poly
  | prefixLen + 1, 0, h, _, _ => by
      exact False.elim (Nat.not_succ_le_zero _ h)
  | prefixLen + 1, n + 1, h, vals, poly => by
      simpa using
        currentResidualGo
          prefixLen
          (n := n)
          (Nat.le_of_succ_le_succ h)
          (fun i => vals i.succ)
          (stepResidual (R := R) (deg := deg) (vals 0) poly)
termination_by currentResidualGo prefixLen _ _ _ => prefixLen
decreasing_by simp_wf

/-- The residual polynomial obtained by evaluating the first `prefixLen`
variables of the original polynomial at the sampled challenge prefix. -/
def currentResidual {n prefixLen : Nat} (h : prefixLen ≤ n)
    (vals : Fin prefixLen → R)
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg (n - prefixLen) :=
  currentResidualGo (R := R) (deg := deg) prefixLen h vals poly

/-- The active residual for the round after a prefix of length `prefixLen`. This
is the residual polynomial in `((n - (prefixLen + 1)) + 1)` variables whose
round polynomial will be sent next. -/
def currentRoundResidual {n prefixLen : Nat} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg ((n - (prefixLen + 1)) + 1) := by
  let residual :=
    currentResidual (R := R) (deg := deg) (n := n) (prefixLen := prefixLen)
      (Nat.le_of_lt h)
      (Sumcheck.challengePrefix R deg prefixLen prefixTr)
      poly
  have hk : n - prefixLen = (n - (prefixLen + 1)) + 1 := by
    omega
  simpa [hk] using residual

/-- The honest round polynomial computed from the current active residual. -/
def honestRoundPoly {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    CDegreeLE R deg :=
  ⟨CMvPolynomial.roundPoly D numVars poly.1,
    CMvPolynomial.roundPoly_natDegree_le D poly.1 (fun mono hmono =>
      poly.2 ⟨0, by omega⟩ mono hmono)⟩

/-- The honest round polynomial sent after the prefix transcript `prefixTr`. -/
def honestRoundPolyAtPrefix {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    CDegreeLE R deg :=
  honestRoundPoly (R := R) (deg := deg) D <|
    currentRoundResidual (R := R) (deg := deg) h prefixTr poly

/-- The honest prover step for one round, specialized to the original
polynomial and the already-recorded challenge prefix. -/
def roundProverStep (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState) :
    Spec.Strategy.withRoles m (roundSpec R deg) (roundRoles R deg)
      (fun _ => NextState) :=
  let sentPoly := honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

/-- The honest prover step for one round, specialized to a private residual
polynomial witness that is threaded across rounds. -/
def roundProverStepStateful (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1))
    (computeNext : R → NextState) :
    Spec.Strategy.withRoles m (roundSpec R deg) (roundRoles R deg)
      (fun _ => NextState) :=
  let sentPoly := honestRoundPoly (R := R) (deg := deg) D poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

/-- Oracle continuation for one live sum-check round after a prefix transcript
of previously sampled challenges. The original polynomial oracle is preserved
unchanged. -/
noncomputable def roundContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction.Continuation oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let poly := sWithOracles.oracleStmt ()
    pure <|
      roundProverStep (m := OracleComp oSpec) (R := R) (deg := deg) D h prefixTr poly
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            some <|
              CPolynomial.eval chal
                (honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly).1
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, PUnit.unit⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStep
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg n) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| query (spec := [Sumcheck.PolyFamily R deg n]ₒ) q

/-- Oracle continuation for one live sum-check round with a private residual
polynomial witness. The public oracle statement remains the original polynomial,
but the honest prover updates its residual state incrementally instead of
recomputing it from the prefix transcript. -/
noncomputable def roundContinuationStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {totalVars : ℕ} (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction.Continuation oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) where
  prover _ sWithOracles witness := do
    let sentPoly := honestRoundPoly (R := R) (deg := deg) D witness
    pure <|
      roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg) D witness
        (fun chal =>
          let nextClaim : Option (RoundClaim R) := some (CPolynomial.eval chal sentPoly.1)
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, stepResidual (R := R) (deg := deg) chal witness⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStep
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg totalVars) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| query (spec := [Sumcheck.PolyFamily R deg totalVars]ₒ) q

/-- Oracle continuation for one chained sum-check round after a possibly-failed
claim. The original polynomial oracle is preserved unchanged. -/
noncomputable def roundContinuationOption
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction.Continuation oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let poly := sWithOracles.oracleStmt ()
    pure <|
      roundProverStep (m := OracleComp oSpec) (R := R) (deg := deg) D h prefixTr poly
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            match sWithOracles.stmt with
            | none => none
            | some _ =>
                some (CPolynomial.eval chal
                  (honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly).1)
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, PUnit.unit⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStepOption
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg n) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| query (spec := [Sumcheck.PolyFamily R deg n]ₒ) q

/-- Oracle continuation for one chained sum-check round with a private residual
polynomial witness. After a prior rejection, the witness still advances
syntactically, but the public claim remains `none`. -/
noncomputable def roundContinuationOptionStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {totalVars : ℕ} (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction.Continuation oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) where
  prover _ sWithOracles witness := do
    let sentPoly := honestRoundPoly (R := R) (deg := deg) D witness
    pure <|
      roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg) D witness
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            match sWithOracles.stmt with
            | none => none
            | some _ => some (CPolynomial.eval chal sentPoly.1)
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, stepResidual (R := R) (deg := deg) chal witness⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStepOption
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg totalVars) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| query (spec := [Sumcheck.PolyFamily R deg totalVars]ₒ) q

/-- A single-round sum-check oracle reduction. The input oracle statement is the
original polynomial in `numVars + 1` variables, and it is preserved unchanged
as the output oracle statement. -/
noncomputable def roundOracleReduction
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (Sumcheck.PolyFamily R deg (numVars + 1))
      PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => PUnit) :=
  let prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
    simpa [Sumcheck.fullSpec] using (show Spec.Transcript ((roundSpec R deg).replicate 0) from ⟨⟩)
  (roundContinuation (R := R) (deg := deg) D
    (n := numVars + 1)
    (prefixLen := 0)
    (Nat.succ_pos numVars)
    prefixTr
    sampleChallenge).fix PUnit.unit

/-- A single-round sum-check oracle reduction with a private residual
polynomial witness. The public oracle statement stays fixed as the original
polynomial, while the witness shrinks from `numVars + 1` variables to `numVars`
after the sampled challenge. -/
noncomputable def roundOracleReductionStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (Sumcheck.PolyFamily R deg (numVars + 1))
      (Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) :=
  (roundContinuationStateful (R := R) (deg := deg) D
    (totalVars := numVars + 1) numVars sampleChallenge).fix PUnit.unit

end

end Sumcheck
