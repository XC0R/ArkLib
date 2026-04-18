/-
Task D: Goal state extraction for fiatShamir_perfectCompleteness

This file extracts the exact goal states for the NeverFail and AllSucceed sorrys.
-/

import ArkLib.OracleReduction.FiatShamir.Basic

open OracleComp OracleSpec ProtocolSpec FiatShamir

variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {pSpec : ProtocolSpec n}
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp))

-- Simulate the proof state after `constructor` in fiatShamir_perfectCompleteness
-- to capture the exact goal types

-- The context after `probEvent_eq_one_iff.mpr` and `constructor`:
-- We need to prove: NeverFail ∧ AllSucceed

-- Let's check what the FS computation looks like
#check @Reduction.fiatShamir

-- The FS side: R.fiatShamir.run with fsChallengeQueryImpl'
-- oSpec side is (oSpec + fsChallengeOracle StmtIn pSpec)
-- impl side is (impl.addLift fsChallengeQueryImpl')
-- state type is (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id)

-- The interactive side: R.run with challengeQueryImpl
-- oSpec side is (oSpec + [pSpec.Challenge]ₒ)
-- impl side is (impl.addLift challengeQueryImpl)
-- state type is σ

-- Key: fsChallengeOracle and [pSpec.Challenge]ₒ are BOTH srChallengeOracle StmtIn pSpec
-- So the oracle specs are the same underlying type!

#check @fsChallengeOracle
#check @ProtocolSpec.challengeOracle

-- Let's verify this:
-- fsChallengeOracle StmtIn pSpec : OracleSpec (ChallengeIdx pSpec)
-- [pSpec.Challenge]ₒ = challengeOracle pSpec : OracleSpec (ChallengeIdx pSpec)
-- Both are srChallengeOracle StmtIn pSpec !

-- This means the oracle specs for the combined spec are:
-- FS: oSpec + srChallengeOracle StmtIn pSpec
-- Interactive: oSpec + srChallengeOracle StmtIn pSpec (since [pSpec.Challenge]ₒ = srChallengeOracle)

-- Wait, let me check if challengeOracle = srChallengeOracle
example : @ProtocolSpec.challengeOracle n pSpec = @srChallengeOracle n StmtIn pSpec := by
  sorry -- Check if this is rfl or needs proof

-- The goal after constructor should be:
-- 1. NeverFail: Pr[⊥ | FS_computation] = 0
-- 2. AllSucceed: ∀ x ∈ support(FS_computation), success_pred x

-- where FS_computation is:
-- OptionT.mk do (simulateQ (impl.addLift fsChallengeQueryImpl') (R.fiatShamir.run stmtIn witIn)).run' (← fsInit)
-- and fsInit = do { let s ← init; return (s, defaultFSImpl) }
