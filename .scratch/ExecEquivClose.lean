import ArkLib.OracleReduction.FiatShamir.Basic

-- Explore the exec-equiv proof for fiatShamir_perfectCompleteness.
-- The key is: under defaultFSImpl, the FS computation produces same
-- (Option StmtOut × (StmtOut × WitOut)) as interactive under defaultChalImpl.

-- Let's look at what Reduction.run_of_prover_first gives us for the NI case.
-- R.fiatShamir is a NonInteractiveReduction, so its pSpec is ⟨!v[.P_to_V], !v[Message]⟩
-- which is ProverOnly. So run_of_prover_first applies.

-- Let's check ProverOnly instance for the NI pSpec
example : ProverOnly ⟨!v[Direction.P_to_V], !v[Unit]⟩ := inferInstance

-- The FS computation via run_of_prover_first:
-- R.fiatShamir.run stmtIn witIn = do
--   let state := R.fiatShamir.prover.input (stmtIn, witIn)
--   let ⟨msg, state⟩ ← R.fiatShamir.prover.sendMessage ⟨0, ...⟩ state
--   let ctxOut ← R.fiatShamir.prover.output state
--   let transcript := fun i => match i with | ⟨0, _⟩ => msg
--   let stmtOut ← (R.fiatShamir.verifier.verify stmtIn transcript).run
--   return (⟨transcript, ctxOut⟩, ← stmtOut.getM)
