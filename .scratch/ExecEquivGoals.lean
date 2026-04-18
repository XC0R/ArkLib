/-
Attempt to close fiatShamir_perfectCompleteness sorrys.
Build with: lake env lean .scratch/ExecEquivGoals.lean
-/
import ArkLib.OracleReduction.FiatShamir.Basic

open OracleComp OracleSpec ProtocolSpec FiatShamir

-- Key question: can we show that the FS computation projected to outputs
-- has support contained in the interactive-default computation's support?

-- The FS computation:
--   simulateQ ((impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl)
--     (Reduction.run stmtIn witIn R.fiatShamir)
-- operates on oracle spec ((oSpec + fsChallengeOracle) + [niPSpec.Challenge]ₒ)
-- with state type (σ × Q)

-- The interactive-default computation:
--   simulateQ (impl.addLift defaultChalImpl) (Reduction.run stmtIn witIn R)
-- operates on oracle spec (oSpec + [pSpec.Challenge]ₒ) with state type σ

-- Both produce Option ((FullTranscript × StmtOut × WitOut) × StmtOut)
-- but FullTranscript types differ. Predicate ignores transcript.

-- Strategy: show that after stripping transcript and state,
-- the output distributions are equal. Use this to close both goals.

variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {pSpec : ProtocolSpec n}
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp))

-- Let's check: what does R.fiatShamir.run unfold to for ProverOnly niPSpec?
-- niPSpec is ProverOnly because all rounds are P_to_V
-- So Reduction.run_of_prover_first should apply

-- Check what Reduction.run_of_prover_first gives us
#check @Reduction.run_of_prover_first

-- Check if niPSpec has ProverOnly instance
-- niPSpec = ⟨!v[.P_to_V], !v[Message]⟩
-- ProverOnly means all directions are P_to_V
-- For n=1, dir 0 = P_to_V ✓

-- Try to unfold R.fiatShamir.run directly
noncomputable example (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.run stmtIn witIn R.fiatShamir = (do
      let state := R.prover.fiatShamir.input (stmtIn, witIn)
      let ⟨msg, state⟩ ← (R.prover.fiatShamir.sendMessage ⟨0, by simp⟩ state)
      let ctxOut ← R.prover.fiatShamir.output state
      let transcript : (NonInteractiveReduction.pSpec (∀ i, pSpec.Message i)).FullTranscript :=
        fun i => match i with | ⟨0, _⟩ => msg
      let stmtOut ← (R.verifier.fiatShamir.verify stmtIn transcript).run
      return (⟨transcript, ctxOut⟩, ← stmtOut.getM)) := by
  exact Reduction.run_of_prover_first stmtIn witIn R.fiatShamir
