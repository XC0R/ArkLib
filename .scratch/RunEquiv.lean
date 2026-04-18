/-
Scratch: Develop the Reduction.run level exec equiv for fiatShamir_perfectCompleteness.

Goal: Show that projected support of FS computation ⊆ projected support of interactive-default.

Strategy: Use run'_simulateQ_eq_of_query_map_eq on a COMMON oracle spec.

Key insight: Both R.fiatShamir.run and R.run, after partial simulation of challenge oracles,
become OracleComp oSpec computations. If we can show these are equal, we're done.
-/

import ArkLib.OracleReduction.FiatShamir.Basic

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

-- What we need to prove (projected to non-transcript components):
-- For each s : σ,
--   projected(FS_comp (s, defaultFSImpl)) = projected(intDefault_comp s)
-- where projection maps Option ((T × StmtOut × WitOut) × StmtOut) to
-- Option ((StmtOut × WitOut) × StmtOut) by dropping T.

-- Let's first understand the structure of R.fiatShamir.run stmtIn witIn.
-- R.fiatShamir is a NonInteractiveReduction over oSpec + fsChallengeOracle.
-- Reduction.run unfolds to:
--   do let pr ← prover.run stmt wit
--      let vr ← liftM (verifier.run stmt pr.1).run
--      return (pr, ← vr.getM)

-- The NI prover.run calls runToRound for the NI spec.
-- The NI verifier.run calls V.fiatShamir.verify.

-- After simulateQ, the computation becomes StateT (σ × Q) ProbComp.

-- Let me try to prove the following: for any OracleComp over (spec + emptySpec),
-- the emptySpec part is never queried, so addLift with a vacuous impl is a no-op.

-- First, let's check what ChallengeIdx looks like for the NI spec.
-- NI spec: ⟨!v[.P_to_V], !v[∀ i, pSpec.Message i]⟩ : ProtocolSpec 1
-- ChallengeIdx = {i : Fin 1 // dir i = .V_to_P}
-- Since dir 0 = .P_to_V, this is empty.

-- So [niPSpec.Challenge]ₒ has empty domain. The addLift challengeQueryImpl for
-- the NI spec should be simplifiable.

-- Let me check if there's a lemma for simulateQ with empty oracle spec.

#check @simulateQ_id -- OracleComp.SimSemantics.Basic

-- Try: what if addLift for empty challenge oracle is just liftTarget?
-- impl.addLift emptyImpl = impl.liftTarget when emptyImpl is vacuous

-- Actually, let me try a different approach entirely.
-- Instead of simplifying the NI challenge layer, let me DIRECTLY prove
-- the perfectCompleteness sorrys by establishing the exec equiv.

-- The exec equiv I want to prove:
-- For each s : σ and each x in support of the FS computation after simulation,
-- there is a corresponding element in the interactive-default computation's support
-- with the same non-transcript components.

-- But since the computations have different types, I can't use support inclusion directly.
-- Instead, I'll prove a MAP EQUALITY:
--
-- projFS <$> fsComp (s, Q) = projInt <$> intComp s
--
-- where projFS/projInt project away the transcript.

-- From this equality: support(projFS <$> fsComp) = support(projInt <$> intComp)
-- So if none ∈ support(projFS <$> fsComp), then none ∈ support(projInt <$> intComp).
-- And since projFS(none) = none = projInt(none), none ∈ support(fsComp) iff none ∈ support(intComp).

-- Let me state this precisely. The FS computation type is:
-- ProbComp (Option ((NI_FullTranscript × StmtOut × WitOut) × StmtOut))
-- The interactive computation type is:
-- ProbComp (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))

-- After projecting away transcripts:
-- ProbComp (Option ((StmtOut × WitOut) × StmtOut))

-- The projections:
-- projFS : Option ((NI_FT × StmtOut × WitOut) × StmtOut) → Option ((StmtOut × WitOut) × StmtOut)
-- projFS = Option.map (fun ⟨⟨_, sww⟩, so⟩ => ⟨sww, so⟩)

-- projInt : Option ((FT × StmtOut × WitOut) × StmtOut) → Option ((StmtOut × WitOut) × StmtOut)
-- projInt = Option.map (fun ⟨⟨_, sww⟩, so⟩ => ⟨sww, so⟩)

-- Now, the FS computation after .run' is:
-- (simulateQ fsFullImpl (R.fiatShamir.run stmtIn witIn)).run' (s, defaultFSImpl)
-- : ProbComp (Option ((NI_FT × StmtOut × WitOut) × StmtOut))

-- Wait, the fsFullImpl includes the NI challengeQueryImpl layer.
-- Let me see if I can strip that layer first.

-- Alternative: work with .run instead of .run', to keep the state visible.
-- Then the state types are:
-- FS: σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id
-- Int: σ

-- Let me try stating the key theorem.

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
  (stmtIn : StmtIn) (witIn : WitIn) (s : σ)

-- The FS computation after simulateQ (with JUST impl.addLift fsChallengeQueryImpl',
-- ignoring the NI challenge layer for now):
-- (simulateQ (impl.addLift fsChallengeQueryImpl') (something)).run (s, defaultFSImpl)

-- The interactive computation:
-- (simulateQ (impl.addLift defaultChalImpl) (R.run stmtIn witIn)).run s

-- Key question: what is "something" on the FS side?
-- It's R.fiatShamir.run stmtIn witIn MINUS the NI challenge oracle queries.
-- Since the NI spec has no challenges, no challenge queries are made.
-- So "something" is R.fiatShamir.run stmtIn witIn coerced to OracleComp (oSpec + fsChallengeOracle).

-- But R.fiatShamir.run is typed as:
-- OptionT (OracleComp ((oSpec + fsChallengeOracle) + [niPSpec.Challenge]ₒ))
--   ((NI_FT × StmtOut × WitOut) × StmtOut)

-- If [niPSpec.Challenge]ₒ has empty index, then no queries to it occur.
-- So R.fiatShamir.run : OptionT (OracleComp ((oSpec + fsChallengeOracle) + emptySpec)) ...
-- And after removing the empty spec: OracleComp (oSpec + fsChallengeOracle) ...

-- To remove it, I need a coercion or a simulation lemma.

-- Let me try: can I use simulateQ_id or similar to strip the empty oracle?

-- Actually, let me take yet another approach.
-- The perfectCompleteness_eq_prob_one rewrites the goal to use
-- (impl.addLift fsChallengeQueryImpl').addLift challengeQueryImpl
-- where challengeQueryImpl is for the NI spec.
-- Since the NI spec has no challenges, challengeQueryImpl is for an empty oracle.
-- The addLift with it just wraps the computation without adding any behavior.

-- In the Security section, this was set up by rw [Reduction.perfectCompleteness_eq_prob_one].
-- After this rewrite, the goal uses the combined impl with the NI challenge layer.

-- In the proof, I need to show that this combined impl gives the same result
-- as if the NI challenge layer wasn't there.

-- One approach: prove that for the NI spec, the addLift challengeQueryImpl is equivalent
-- to not adding it (since no queries are made to it).

-- Let me check if processRound for the NI spec (with just 1 P_to_V round) ever queries
-- the challenge oracle. Answer: NO, because the only round is P_to_V, so no V_to_P
-- challenge queries happen. The Prover.run for the NI spec:
-- - runToRound (Fin.last 0): just one step, P_to_V → sendMessage, no challenge query
-- - output: doesn't query challenges
-- The Verifier.run for the NI spec:
-- - V.fiatShamir.verify: queries fsChallengeOracle (NOT [niPSpec.Challenge]ₒ)

-- So indeed, [niPSpec.Challenge]ₒ is NEVER queried. The addLift challengeQueryImpl is vacuous.

-- Therefore: the computation R.fiatShamir.run stmtIn witIn never queries [niPSpec.Challenge]ₒ.
-- After simulateQ (impl'.addLift challengeQueryImpl):
-- All queries go to impl' = impl.addLift fsChallengeQueryImpl'
-- The challengeQueryImpl part is never triggered.

-- Now, does run'_simulateQ_eq_of_query_map_eq help?
-- It needs the SAME oracle spec. But R.fiatShamir.run and R.run have DIFFERENT specs.

-- I think the cleanest path is:
-- 1. Show that simulateQ with the NI challenge layer is equivalent to without it
--    (since no queries are made to it). This gives:
--    (simulateQ (impl'.addLift niChalImpl) (R.fiatShamir.run ...)).run' (s, Q)
--    = (simulateQ impl' (R.fiatShamir.run' ...)).run' (s, Q)
--    where R.fiatShamir.run' is R.fiatShamir.run coerced to the smaller spec.
--
-- 2. Show R.fiatShamir.run' (OracleComp (oSpec + fsChallengeOracle))
--    projected ≈ R.run (OracleComp (oSpec + [pSpec.Challenge]ₒ))
--    under appropriate simulations.

-- But step 1 requires a coercion between OracleComp (spec + emptySpec) and OracleComp spec,
-- which may not exist definitionally.

-- I think the REAL path forward is:
-- Don't try to strip the NI challenge layer.
-- Instead, prove the projected equality directly between the two ProbComp computations
-- after FULL simulation (including the NI challenge layer).

-- The key observation: after full simulation to ProbComp, both are just ProbComp values.
-- The FS one has extra state (QueryImpl) but after .run', the state is discarded.

-- Let me try to prove it by structural induction. The computation R.fiatShamir.run
-- unfolds to a specific sequence of operations. After simulateQ, each operation
-- becomes a ProbComp operation. I can trace through and show equality.

-- This is essentially "proof by computation": unfold everything, simplify, and show equality.

-- Let me try:

noncomputable example
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (s : σ) :
    -- After full simulation and projection, FS = interactive-default
    (Option.map (fun (z : (_ × StmtOut × WitOut) × StmtOut) =>
      ((z.1.2, z.2) : (StmtOut × WitOut) × StmtOut))) <$>
    ((simulateQ (impl.addLift (defaultChalImpl (σ := σ)))
      (Reduction.run stmtIn witIn R) :
      StateT σ ProbComp _).run' s)
    = (Option.map (fun (z : (_ × StmtOut × WitOut) × StmtOut) =>
      ((z.1.2, z.2) : (StmtOut × WitOut) × StmtOut))) <$>
    ((simulateQ (impl.addLift (defaultChalImpl (σ := σ)))
      (Reduction.run stmtIn witIn R) :
      StateT σ ProbComp _).run' s) := by
  rfl

-- ^ That's trivially true (both sides are the same). Let me state the actual non-trivial version.
-- The issue is stating it with the FS side.
