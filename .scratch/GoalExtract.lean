import ArkLib.OracleReduction.FiatShamir.Basic

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

-- Check: what type does simulateQ produce for R.fiatShamir.run?
#check fun (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (s : σ) =>
  ((simulateQ ((impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl)
    (Reduction.run stmtIn witIn R.fiatShamir) :
    StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp _).run
      (s, defaultFSImpl))

-- Check: what's the OptionT structure?
example (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.run stmtIn witIn R.fiatShamir =
      Reduction.run stmtIn witIn R.fiatShamir := rfl

-- Let me see if the NI challenge oracle simplifies
-- The NI pSpec is ⟨!v[.P_to_V], !v[∀ i, pSpec.Message i]⟩
-- ChallengeIdx for this is empty (no V_to_P rounds)
-- So [niPSpec.Challenge]ₒ has empty domain

-- Can I simplify addLift challengeQueryImpl away for the NI case?
-- challengeQueryImpl for NI spec: QueryImpl [niPSpec.Challenge]ₒ ProbComp
-- Since ChallengeIdx niPSpec is empty, this should be vacuous

-- Let me check ChallengeIdx for NI spec
#check @ProtocolSpec.ChallengeIdx 1 ⟨!v[.P_to_V], !v[∀ i, pSpec.Message i]⟩

-- Test: is the addLift challengeQueryImpl vacuous?
-- If ChallengeIdx is Fin 0 or Empty, then no queries ever reach it
