import ArkLib.OracleReduction.FiatShamir.Basic

-- Minimal reproduction to see the goal types

set_option maxHeartbeats 800000

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

-- Just check what probEvent_eq_one_iff.mpr needs:
-- Pr[p | OptionT.mk mx] = 1 ← Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, p x
-- where mx : ProbComp (Option α) and p : α → Prop

-- So after the split, goal 1 is: Pr[⊥ | <the FS inner computation>] = 0
-- and goal 2 is: ∀ x ∈ support(<the FS inner computation>), <the event> x

-- The key question: what IS the FS inner computation?
-- It's: do let (s, ci) ← (do return (← init, defaultFSImpl)); ...
-- = do let s ← init; (simulateQ (impl.addLift fsChallengeQueryImpl') (R.fiatShamir.run stmtIn witIn)).run' (s, defaultFSImpl)

-- And the interactive inner computation is:
-- do let s ← init; (simulateQ (impl.addLift challengeQueryImpl) (R.run stmtIn witIn)).run' s
