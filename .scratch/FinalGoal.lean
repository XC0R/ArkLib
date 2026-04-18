import ArkLib.OracleReduction.Security.Basic

-- Just check what the goal looks like after the simp in the main proof
-- by reading the sorry message from the build output

-- The key question: after `simp only [Reduction.fiatShamir, ...]`,
-- what does the goal become?

-- Let's instead try to understand the types by checking what `R.fiatShamir.run` unfolds to.
-- R.fiatShamir is a NonInteractiveReduction, so Reduction.run gives:
--   do let proverResult ← R.fiatShamir.prover.run stmtIn witIn
--      let stmtOut ← liftM (R.fiatShamir.verifier.run stmtIn proverResult.1).run
--      return ⟨proverResult, ← stmtOut.getM⟩
--
-- R.fiatShamir.prover.run =
--   do let ⟨transcript, state⟩ ← R.fiatShamir.prover.runToRound (Fin.last 0) stmtIn witIn
--      return ⟨transcript, ← R.fiatShamir.prover.output state⟩
--
-- R.fiatShamir.prover.runToRound (Fin.last 0) =
--   Fin.induction (pure ⟨default, P.input(stmtIn, witIn)⟩) (processRound) (Fin.last 0)
--   = processRound 0 (pure ⟨default, P.input(stmtIn, witIn)⟩)
-- Since NI protocol has dir 0 = P_to_V:
--   processRound = do
--     let ⟨_, state⟩ ← pure ⟨default, (stmtIn, P.input(stmtIn, witIn))⟩
--     let ⟨msg, newState⟩ ← P.fiatShamir.sendMessage ⟨0, _⟩ state
--     return ⟨default.concat _ msg, newState⟩
-- where P.fiatShamir.sendMessage ⟨0, _⟩ ⟨stmtIn, state⟩ =
--   do let ⟨messages, _, state⟩ ← P.runToRoundFS (Fin.last n) stmtIn state
--      return ⟨messages, state⟩
