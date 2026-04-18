/-
Isolate the two sorrys from fiatShamir_perfectCompleteness.
Build with: lake env lean .scratch/SorryChase.lean
-/
import ArkLib.OracleReduction.FiatShamir.Basic

open OracleComp ProtocolSpec FiatShamir

noncomputable section

variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  {σ : Type}
  {init : ProbComp σ}
  {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
  {stmtIn : StmtIn} {witIn : WitIn}

-- Sorry A: NeverFail transfer
-- Given none ∈ support(FS), prove none ∈ support(int-default)
example
    (hmem : none ∈ support (do
       let s ← init
       StateT.run'
         (simulateQ ((impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl)
           (Reduction.run stmtIn witIn R.fiatShamir))
         (s, fun ⟨i, _⟩ => (default : pSpec.Challenge i)))) :
    none ∈ support (do
       let s ← init
       StateT.run'
         (simulateQ (impl.addLift (defaultChalImpl (σ := σ)))
           (Reduction.run stmtIn witIn R))
         s) := by
  -- Step 1: Decompose both via mem_support_bind_iff
  rw [mem_support_bind_iff] at hmem ⊢
  obtain ⟨s, hs_init, hmem_s⟩ := hmem
  refine ⟨s, hs_init, ?_⟩
  -- hmem_s : none ∈ support((simulateQ FS_impl (R.fiatShamir.run)).run' (s, defaultFSImpl))
  -- Goal: none ∈ support((simulateQ default_impl (R.run)).run' s)
  sorry
