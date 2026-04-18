import ArkLib.OracleReduction.FiatShamir.Basic

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
  (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
  (stmtIn : StmtIn) (witIn : WitIn)

-- What is the type of R.fiatShamir.run?
#check Reduction.run stmtIn witIn R.fiatShamir

-- What is the type of the OptionT-unwrapped version?
#check (Reduction.run stmtIn witIn R.fiatShamir).run

-- What about after simulateQ?
noncomputable example : StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp _ :=
  simulateQ ((impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl)
    (Reduction.run stmtIn witIn R.fiatShamir).run
