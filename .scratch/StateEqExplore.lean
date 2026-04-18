/-
Scratch file: Explore the goal state for runToRoundFS_default_state_eq Fin.induction step.
Focus: P_to_V case — simplest because no challenge query.
-/

import ArkLib.OracleReduction.FiatShamir.Basic

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

variable {σ : Type}
  (impl : QueryImpl oSpec (StateT σ ProbComp))
  [∀ i, SampleableType (pSpec.Challenge i)]

-- The P_to_V step: after expanding processRound(FS), simulateQ_bind, etc.
-- Both sides bind on the previous computation, then do sendMessage.
-- The inner function after proj only depends on (PrvState, σ) — not on messages/transcript.
-- So we can use bind_eq_of_map_eq_of_comp IF we can show the factoring.

-- Key observation: the inner function is
--   fun a => proj <$> (simulateQ impl (liftM (sendMessage prvState(a)) >>= pure_pack(a))).run state(a)
-- Where prvState(a) and state(a) are extracted from a.
-- The pure_pack builds the output tuple using parts of a that get projected away.
-- So proj <$> (... pure_pack).run state = proj <$> (sendMessage_result).run state
-- because the pure just packs and proj removes the packing.

-- Let me try to simplify the inner computation using simulateQ lemmas
-- and show it factors.

-- First, let me check: does simulateQ_add_liftComp_left fire on liftM?
-- liftM in OracleComp context = OracleComp.liftComp
-- So simulateQ (impl.addLift chalImpl) (liftM oa) = simulateQ impl.liftTarget oa
-- via addLift_def + simulateQ_add_liftComp_left

-- For the FS side: simulateQ (impl.addLift fsChallengeQueryImpl') (liftM (sendMessage ...))
--   = simulateQ (impl.liftTarget (StateT (σ × Q) ProbComp)) (sendMessage ...)
-- For the int side: simulateQ (impl.addLift defaultChalImpl) (liftM (sendMessage ...))
--   = simulateQ (impl.liftTarget (StateT σ ProbComp)) (sendMessage ...)
--   which should equal simulateQ impl (sendMessage ...) since liftTarget with identity = impl

-- Then full_run_simulateQ_liftTarget_eq bridges the FS StateT (σ × Q) to StateT σ.

set_option maxHeartbeats 1200000 in
example [∀ i, VCVCompatible (pSpec.Challenge i)]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin (n + 1)) (stmt : StmtIn) (wit : WitIn) (s : σ) :
    (fun p => (p.1.2.2, p.2)) <$>
      ((simulateQ (impl.addLift fsChallengeQueryImpl')
        (P.runToRoundFS i stmt (P.input (stmt, wit))) :
        StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp _).run
          (s, (defaultFSImpl : QueryImpl (srChallengeOracle StmtIn pSpec) Id)))
    = (fun p => (p.1.2, (p.2, (defaultFSImpl : QueryImpl (srChallengeOracle StmtIn pSpec) Id)))) <$>
      ((simulateQ (impl.addLift (defaultChalImpl (σ := σ)))
        (P.runToRound i stmt wit) :
        StateT σ ProbComp _).run s) := by
  induction i using Fin.induction with
  | zero =>
    simp [Prover.runToRoundFS, Prover.runToRound, simulateQ_pure, StateT.run_pure]
  | succ j ih =>
    simp only [Prover.runToRoundFS, Prover.runToRound, Fin.induction_succ]
    simp only [Prover.processRoundFS, Prover.processRound]
    simp only [simulateQ_bind, StateT.run_bind, map_bind]
    -- Now both sides are: prev >>= inner
    -- IH gives: proj <$> prev_FS = proj <$> prev_int
    -- Need to show the inner functions match after projection
    -- The inner function depends on the full result from prev, but after projection
    -- only uses (PrvState, σ × Q) / (PrvState, σ, defaultFSImpl)
    -- Let's try: use congr_arg Bind.bind on the prev parts, then funext on the inner

    -- Use simulateQ_bind + simulateQ_pure to simplify the inner do-blocks
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      map_bind, bind_pure_comp, Functor.map_map]
    -- Now try to use simulateQ_add_liftComp_left on the liftM parts
    simp only [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left]
    -- Use full_run_simulateQ_liftTarget_eq to bridge FS StateT (σ×Q) to StateT σ
    simp only [full_run_simulateQ_liftTarget_eq impl]
    sorry
