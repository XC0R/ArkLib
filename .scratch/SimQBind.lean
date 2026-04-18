/-
Test: decompose simulateQ through Reduction.run's bind chain.
Build: lake env lean .scratch/SimQBind.lean
-/
import ArkLib.OracleReduction.FiatShamir.Basic

open OracleComp ProtocolSpec FiatShamir

noncomputable section

variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {pSpec : ProtocolSpec n}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  (impl : QueryImpl oSpec (StateT σ ProbComp))
  (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
  (stmtIn : StmtIn) (witIn : WitIn) (s : σ)

-- Test: can we unfold Reduction.run + OptionT inside simulateQ and distribute?
set_option maxHeartbeats 800000 in
example (h : none ∈ support (
    (simulateQ ((impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl)
      (Reduction.run stmtIn witIn R.fiatShamir) :
      StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp _).run'
        (s, defaultFSImpl))) :
    True := by
  -- Step 1: unfold Reduction.run
  unfold Reduction.run at h
  -- Step 2: unfold OptionT.bind to expose OracleComp.bind
  unfold OptionT.bind OptionT.mk at h
  -- Step 3: distribute simulateQ through the binds
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    StateT.run'] at h
  -- See what remains
  trivial

end
