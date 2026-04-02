/- 
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import VCVio

/-!
# Interaction-Native Sum-Check: General Oracle Protocol

The canonical interaction-native `n`-round sum-check protocol is an
oracle-native continuation composition over a **fixed original polynomial
oracle**.

The public protocol state is just the current live claim:
- the first round starts from `target : RoundClaim R`;
- later rounds carry `Option (RoundClaim R)`, preserving failure after the first
  rejected check.

The honest prover is stateless at the protocol boundary. At every round it
recomputes the current residual polynomial from the original oracle statement
and the prefix transcript of prior challenges.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec
open scoped NNReal ENNReal

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

section

variable {R} {deg}

/-- The replicated sender-message oracle decoration for the full `n`-round
sum-check surface. -/
abbrev fullOD (n : Nat) :
    OracleDecoration (Sumcheck.fullSpec R deg n) (Sumcheck.fullRoles R deg n) :=
  (roundOracleDecoration R deg).replicate n

/-- Append one more round transcript to the right end of an existing replicated
prefix transcript. -/
private def snocRoundTranscript (prefixLen : Nat)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (tr : Spec.Transcript (roundSpec R deg)) :
    Spec.Transcript (Sumcheck.fullSpec R deg (prefixLen + 1)) :=
  Spec.Transcript.replicateJoin (roundSpec R deg) (prefixLen + 1) fun j =>
    Fin.lastCases tr (fun i => Sumcheck.roundTranscript R deg prefixLen prefixTr i) j

/-- Tail continuation for the remaining `remaining` rounds after a fixed prefix
transcript of length `prefixLen`. The original polynomial oracle remains
unchanged throughout. -/
private noncomputable def tailContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : Nat} (D : Fin m_dom → R)
    (n : Nat)
    (sampleChallenge : OracleComp oSpec R) :
    (remaining prefixLen : Nat) →
    (h : prefixLen + remaining = n) →
    Spec.Transcript (Sumcheck.fullSpec R deg prefixLen) →
    OracleReduction.Continuation oSpec PUnit
      (fun _ => Sumcheck.fullSpec R deg remaining)
      (fun _ => Sumcheck.fullRoles R deg remaining)
      (fun _ => fullOD remaining)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit)
  | 0, _, _, _ => by
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD] using
        (OracleReduction.Continuation.id
          (SharedIn := PUnit)
          (StatementIn := fun _ => Option (RoundClaim R))
          (OStmtIn := fun _ => Sumcheck.PolyFamily R deg n)
          (WitnessIn := fun _ => PUnit))
  | remaining + 1, prefixLen, hEq, prefixTr => by
      have hRound : prefixLen < n := by omega
      have hTail : prefixLen + 1 + remaining = n := by omega
      have cont :
          OracleReduction.Continuation oSpec PUnit
            (fun _ => (roundSpec R deg).append (fun _ => Sumcheck.fullSpec R deg remaining))
            (fun _ =>
              RoleDecoration.append
                (roundRoles R deg)
                (fun _ => Sumcheck.fullRoles R deg remaining))
            (fun _ =>
              Role.Refine.append
                (roundOracleDecoration R deg)
                (fun _ => fullOD remaining))
            (fun _ => Option (RoundClaim R))
            (fun _ => Sumcheck.PolyFamily R deg n)
            (fun _ => PUnit)
            (fun _ _ => Option (RoundClaim R))
            (fun _ _ => Sumcheck.PolyFamily R deg n)
            (fun _ _ => PUnit) :=
        OracleReduction.Continuation.comp
          (StmtMid := fun _ _ => Option (RoundClaim R))
          (ιₛₘ := fun _ _ => Unit)
          (OStmtMid := fun _ _ => Sumcheck.PolyFamily R deg n)
          (WitMid := fun _ _ => PUnit)
          (ctx₂ := fun _ _ => Sumcheck.fullSpec R deg remaining)
          (roles₂ := fun _ _ => Sumcheck.fullRoles R deg remaining)
          (OD₂ := fun _ _ => fullOD remaining)
          (StmtOut := fun _ _ _ => Option (RoundClaim R))
          (ιₛₒ := fun _ _ _ => Unit)
          (OStmtOut := fun _ _ _ => Sumcheck.PolyFamily R deg n)
          (WitOut := fun _ _ _ => PUnit)
          (roundContinuationOption
            (R := R) (deg := deg) D
            (n := n) (prefixLen := prefixLen) hRound prefixTr sampleChallenge)
          (fun _ tr =>
            tailContinuation D n sampleChallenge
              remaining (prefixLen + 1) hTail
              (snocRoundTranscript (R := R) (deg := deg) prefixLen prefixTr tr))
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD, Spec.replicate_succ] using cont

/-- The full continuation-native sum-check protocol over the fixed original
polynomial oracle. -/
private noncomputable def sumcheckContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction.Continuation oSpec PUnit
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => fullOD n)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) := by
  cases n with
  | zero =>
      refine
        { prover := ?_
          verifier := ?_
          simulate := ?_ }
      · intro _ sWithOracles _
        exact pure ⟨⟨some sWithOracles.stmt, sWithOracles.oracleStmt⟩, PUnit.unit⟩
      · intro _ _ _ target
        exact some target
      · intro _ _ q
        exact liftM <| query (spec := [Sumcheck.PolyFamily R deg 0]ₒ) q
  | succ n =>
      let prefix0 : Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
        simpa [Sumcheck.fullSpec] using
          (show Spec.Transcript ((roundSpec R deg).replicate 0) from ⟨⟩)
      have cont :
          OracleReduction.Continuation oSpec PUnit
            (fun _ => (roundSpec R deg).append (fun _ => Sumcheck.fullSpec R deg n))
            (fun _ =>
              RoleDecoration.append
                (roundRoles R deg)
                (fun _ => Sumcheck.fullRoles R deg n))
            (fun _ =>
              Role.Refine.append
                (roundOracleDecoration R deg)
                (fun _ => fullOD n))
            (fun _ => RoundClaim R)
            (fun _ => Sumcheck.PolyFamily R deg (n + 1))
            (fun _ => PUnit)
            (fun _ _ => Option (RoundClaim R))
            (fun _ _ => Sumcheck.PolyFamily R deg (n + 1))
            (fun _ _ => PUnit) :=
        OracleReduction.Continuation.comp
          (StmtMid := fun _ _ => Option (RoundClaim R))
          (ιₛₘ := fun _ _ => Unit)
          (OStmtMid := fun _ _ => Sumcheck.PolyFamily R deg (n + 1))
          (WitMid := fun _ _ => PUnit)
          (ctx₂ := fun _ _ => Sumcheck.fullSpec R deg n)
          (roles₂ := fun _ _ => Sumcheck.fullRoles R deg n)
          (OD₂ := fun _ _ => fullOD n)
          (StmtOut := fun _ _ _ => Option (RoundClaim R))
          (ιₛₒ := fun _ _ _ => Unit)
          (OStmtOut := fun _ _ _ => Sumcheck.PolyFamily R deg (n + 1))
          (WitOut := fun _ _ _ => PUnit)
          (roundContinuation
            (R := R) (deg := deg) D
            (n := n + 1) (prefixLen := 0)
            (Nat.succ_pos n)
            prefix0
            sampleChallenge)
          (fun _ tr =>
            tailContinuation D (n + 1) sampleChallenge
              n 1 (by omega)
              (snocRoundTranscript (R := R) (deg := deg) 0 prefix0 tr))
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD, Spec.replicate_succ] using cont

/-- The canonical `n`-round oracle-native sum-check protocol.

The prover and verifier interact across `n` replicated rounds, but the oracle
statement stays fixed as the original polynomial in `n` variables. The output
statement is the terminal live claim, or `none` after the first rejecting
round. -/
noncomputable def sumcheckReduction
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (Sumcheck.PolyFamily R deg n)
      PUnit
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => fullOD n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) :=
  (sumcheckContinuation (R := R) (deg := deg) n D sampleChallenge).fix PUnit.unit

/-! ## Security placeholders

The canonical object is now an oracle-native continuation composition over a
fixed original polynomial oracle. Completeness and soundness should be restated
against the oracle-side security APIs once that layer is upgraded for the new
sum-check surface.
-/

omit [Nontrivial R] in
theorem sumcheckReduction_completeness
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (poly : Sumcheck.PolyStmt R deg n)
    (_sampleChallenge : OracleComp oSpec R)
    (target : RoundClaim R) (_hValid : fullSum R deg D poly = target) :
    True := by
  trivial

omit [Nontrivial R] in
theorem sumcheckReduction_soundness
    {ι : Type} {oSpec : OracleSpec ι}
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (poly : Sumcheck.PolyStmt R deg n)
    (_sampleChallenge : OracleComp oSpec R)
    (target : RoundClaim R) (_hInvalid : fullSum R deg D poly ≠ target) :
    True := by
  trivial

end

end

end Sumcheck
