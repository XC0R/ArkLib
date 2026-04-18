import ArkLib.OracleReduction.FiatShamir.Basic

-- Prove: the FS computation's Option structure matches the interactive-default's.
-- Under defaultFSImpl, both produce the same Option ((StmtOut × WitOut) × StmtOut)
-- after projecting away transcripts.
--
-- Key existing lemmas:
-- runToRoundFS_default_messages_state_eq: FS prover ≈ interactive prover (messages + state)
-- deriveTranscriptFS_default_eq: FS transcript derivation = ofMsgChal(messages, default)
-- equivMessagesChallenges.left_inv: transcript = ofMsgChal(toMessages t, toChallenges t)

set_option maxHeartbeats 1600000

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

-- Let's understand the Reduction.run structure for both cases.
-- For the interactive case:
-- R.run stmtIn witIn : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)
-- = do let proverResult ← R.prover.run stmtIn witIn; let stmtOut ← ...; ...

-- For the FS case:
-- R.fiatShamir.run stmtIn witIn : OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + [niPSpec.Challenge]ₒ)) ((niTranscript × StmtOut × WitOut) × StmtOut)
-- = do let proverResult ← R.fiatShamir.prover.run stmtIn witIn; let stmtOut ← ...; ...

-- After simulateQ, the FS computation is in StateT (σ × Q) ProbComp
-- and the interactive is in StateT σ ProbComp.

-- The key: R.fiatShamir.prover.run calls runToRoundFS, and R.prover.run calls runToRound.
-- Under defaultFSImpl/defaultChalImpl, these produce the same messages + state.

-- Rather than trying to prove full distributional equality, let me prove a weaker statement:
-- for every element in FS support, the same Option constructor (none/some) and the same
-- (StmtOut × WitOut) × StmtOut appear in int_default support.

-- Actually, let me just try to see if Lean can handle a direct `show` with sorry.
-- The challenge is getting the types right.

-- Let me check: what is the type of the FS inner computation?
-- It should be ProbComp (Option ((niTranscript × StmtOut × WitOut) × StmtOut))
-- where niTranscript = FullTranscript ⟨!v[.P_to_V], !v[∀ i, pSpec.Message i]⟩

-- And the interactive inner: ProbComp (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))

-- For the exec-equiv, I need to relate these two types.
-- The approach: show the FS inner computation, after mapping with
--   Option.map (fun ⟨⟨_, ctx⟩, so⟩ => ⟨ctx, so⟩),
-- equals the interactive-default inner computation after the same mapping.

-- Let me try to state this.
-- First, let me establish the types.
-- fsInner s := ((simulateQ fsImpl (R.fiatShamir.run stmtIn witIn) : StateT (σ × Q) ProbComp _).run' (s, defaultFSImpl))
-- intDefInner s := ((simulateQ defImpl (R.run stmtIn witIn) : StateT σ ProbComp _).run' s)

-- The claim: ∀ s,
--   Option.map (fun ⟨⟨_, ctx⟩, so⟩ => ⟨ctx, so⟩) <$> fsInner s
--   = Option.map (fun ⟨⟨_, ctx⟩, so⟩ => ⟨ctx, so⟩) <$> intDefInner s

-- Let me try to state this with the correct types.

-- Actually, this will require a LOT of type annotation.
-- Let me try: maybe I can prove it by showing both sides are equal to a third thing.
-- Or by using congr/convert to strip the transcript layer.

-- Hmm, let me try yet another approach.
-- What if the FS computation, after applying Option.map to forget the NI transcript,
-- is equal to the int-default computation after applying Option.map to forget the full transcript,
-- because both reduce to:
-- do
--   (messages, prvState) ← simulateQ ... (runToRound/runToRoundFS ...)
--   ctxOut ← simulateQ ... (P.output prvState)
--   transcript ← simulateQ ... (deriveTranscript/identity)
--   stmtOut ← simulateQ ... (V.verify stmtIn transcript)
--   return match stmtOut with
--     | some so => some (ctxOut, so)
--     | none => none

-- After forgetting the transcript, both return:
-- do
--   (_, prvState) ← ...
--   ctxOut ← P.output prvState
--   transcript ← ...  (both get same transcript under default)
--   stmtOut ← V.verify stmtIn transcript  (same transcript → same verify)
--   return match stmtOut with | some so => some (ctxOut, so) | none => none

-- So the projected computation is:
-- do
--   (_, prvState) ← ... (same prv state by _messages_state_eq)
--   ctxOut ← P.output prvState  (same)
--   stmtOut ← V.verify stmtIn (ofMsgChal(messages, default))  (same transcript)
--   return match stmtOut with | some so => some (ctxOut, so) | none => none

-- Both projected computations are identical!
-- This is the key insight. The proof should show this by unfolding both sides.
-- But the unfolding is tricky because of the monadic structure (StateT, simulateQ, etc.)

-- Let me try to prove it by induction on the monadic computation structure.
-- Or maybe I can use bind_congr to show the bind chains match.

-- Actually, I think the cleanest approach is to prove a stronger statement:
-- the FS computation (projected) IS EQUAL to the interactive-default computation (projected).
-- This is a distributional equality, not just support inclusion.

-- Let me try a simple test: can I even state this claim without errors?

example (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (s : σ) :
    let niPS : ProtocolSpec 1 := ⟨!v[Direction.P_to_V], !v[∀ i, pSpec.Message i]⟩
    let τ := σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id
    let fsOSpec := oSpec + fsChallengeOracle StmtIn pSpec
    let fsImpl : QueryImpl (fsOSpec + [niPS.Challenge]ₒ) (StateT τ ProbComp) :=
      (impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl
    (Option.map (fun (x : (_ × StmtOut × WitOut) × StmtOut) => (x.1.2, x.2))) <$>
      ((simulateQ fsImpl (Reduction.run stmtIn witIn R.fiatShamir) :
        StateT τ ProbComp _).run'
          (s, (defaultFSImpl : QueryImpl (srChallengeOracle StmtIn pSpec) Id)))

    = (Option.map (fun (x : (_ × StmtOut × WitOut) × StmtOut) => (x.1.2, x.2))) <$>
      ((simulateQ (impl.addLift (defaultChalImpl (σ := σ)))
        (Reduction.run stmtIn witIn R) :
        StateT σ ProbComp _).run' s) := by
  sorry
