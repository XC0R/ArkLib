/-
Scratch exploration for Fiat-Shamir execution equivalence (Task A, Request 06).

Goal: Establish that FS prover execution with default challenges produces same
      final outputs as interactive prover execution with default challenges.

Key insight from VCVio analysis (Task D):
  - `run'_simulateQ_eq_of_query_map_eq` and `relTriple_simulateQ_run` lemmas could help
  - But FS and interactive use DIFFERENT oracle specs, so direct application fails

Strategy: Work at the OracleComp level, not the simulateQ level.
  - Show that R.fiatShamir.run (over oSpec + fsChallengeOracle) produces same outputs
    as R.run (over oSpec + [pSpec.Challenge]ₒ) when both use default challenges.
  - This requires structural reasoning about how processRoundFS vs processRound
    interact with the respective oracles.
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import VCVio.ProgramLogic.Relational.SimulateQ

open ProtocolSpec OracleComp OracleSpec

universe u

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]

variable {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

/-!
## Key observation

The FS prover uses `fsChallengeQueryImpl'` which, given state `f : QueryImpl (srChallengeOracle StmtIn pSpec) Id`,
returns `(f ⟨i, t⟩, f)` for query `⟨i, t⟩`.

When `f = defaultFSImpl = fun ⟨i, _⟩ => default`, this returns `(default, f)`.

The interactive prover with `defaultChalImpl` returns `pure default`.

Both give `default` for every challenge — the key is to show the state projection
makes them equivalent.

## Approach: Use `run'_simulateQ_eq_of_query_map_eq`

From VCVio.ProgramLogic.Relational.SimulateQ:

```
theorem run'_simulateQ_eq_of_query_map_eq
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s, Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s)
```

If we can establish this at the combined oracle level, we bypass Fin.induction entirely!
-/

namespace FSExecEquiv

-- State types:
-- FS prover state: σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id
-- Interactive prover state: σ

-- Oracle types:
-- FS computation: oSpec + fsChallengeOracle StmtIn pSpec
-- Interactive computation: oSpec + [pSpec.Challenge]ₒ

-- The key challenge: these are DIFFERENT oracle specs, so `run'_simulateQ_eq_of_query_map_eq`
-- doesn't directly apply. We need a different approach.

-- Alternative: Compare both AFTER simulation to ProbComp
-- Both FS and interactive computations, after simulateQ with appropriate impls,
-- become StateT τ ProbComp computations for some τ.

-- Let's define the implementations more concretely:

-- Implementation 1: FS prover side
-- Uses impl.addLift fsChallengeQueryImpl' : QueryImpl (oSpec + srChallengeOracle ...)
--   (StateT (σ × QueryImpl (srChallengeOracle ...) Id) ProbComp)

-- Implementation 2: Interactive prover side
-- Uses impl.addLift defaultChalImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)

-- Key insight: The oracle SPECS are different:
--   FS uses: oSpec + fsChallengeOracle StmtIn pSpec
--   Interactive uses: oSpec + [pSpec.Challenge]ₒ

-- fsChallengeOracle requires (StmtIn, MessagesUpTo) as query input
-- [pSpec.Challenge]ₒ only requires the round index

-- This means we can't directly compare simulateQ results — the COMPUTATIONS themselves
-- are in different monads (OracleComp over different specs).

-- REVISED APPROACH: Prove equivalence via structural induction on rounds.
-- For round j:
--   FS: processRoundFS queries fsChallengeOracle, gets default from fsChallengeQueryImpl'
--   Interactive: processRound queries [pSpec.Challenge]ₒ, gets default from defaultChalImpl

-- Both pass `default` to prover.receiveChallenge, producing the same next PrvState.

-- The difference is in the BOOKKEEPING state:
--   FS carries: MessagesUpTo × StmtIn × PrvState
--   Interactive carries: Transcript × PrvState

-- So we compare only the PrvState component.

/-- The projection from FS state to interactive state (PrvState component). -/
def fsPrvStateProj (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin (n + 1)) :
    (pSpec.MessagesUpTo i × StmtIn × P.PrvState i) → P.PrvState i :=
  fun ⟨_, _, state⟩ => state

-- After both executions are simulated to ProbComp, we want to show:
-- (simulateQ fsImpl (P.runToRoundFS i stmt state)) projects to the same PrvState distribution
-- as (simulateQ defaultChalImpl' (P.runToRound i stmt wit))

-- where fsImpl = impl.addLift fsChallengeQueryImpl' (with f = defaultFSImpl)
-- and defaultChalImpl' = impl.addLift defaultChalImpl

-- The proof by Fin.induction:
-- Base case: i = 0
--   runToRoundFS 0 = pure ⟨default, stmt, state⟩
--   runToRound 0 = pure ⟨default, prover.input (stmt, wit)⟩
--   If state = prover.input (stmt, wit), both project to the same PrvState.

-- Inductive step: i → i.succ
--   Unfold processRoundFS and processRound, match on pSpec.dir i:
--
--   Case V_to_P:
--     FS: f ← prover.receiveChallenge; challenge ← query fsChallengeOracle; return (_, _, f challenge)
--     After simulation with fsChallengeQueryImpl' (state = defaultFSImpl):
--       challenge = default, so result PrvState = f default
--     Interactive: challenge ← query [pSpec.Challenge]ₒ; f ← prover.receiveChallenge; return (_, f challenge)
--     After simulation with defaultChalImpl:
--       challenge = default, so result PrvState = f default
--     Same!
--
--   Case P_to_V:
--     Both call prover.sendMessage, same newState.

-- This is the structural argument. Let me write a lemma statement:

-- First, let's check what happens when we simulate processRoundFS vs processRound

lemma processRoundFS_prvState_eq_processRound_prvState
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (j : Fin n)
    (stmt : StmtIn) (messages : pSpec.MessagesUpTo j.castSucc) (state : P.PrvState j.castSucc)
    (transcript : pSpec.Transcript j.castSucc)
    -- The FS impl with default state:
    -- After simulation, challenge queries return `default`
    :
    -- Goal: After simulation with appropriate impls, the PrvState components agree
    True := by
  sorry

/-!
## The core challenge

The L319 sorry requires showing:
  support(R.fiatShamir.run with default FS impl) ⊆ support(R.run with default chal impl)

But these computations live in DIFFERENT monads:
  - R.fiatShamir.run : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) ...
  - R.run : OracleComp (oSpec + [pSpec.Challenge]ₒ) ...

After simulation:
  - FS uses impl.addLift fsChallengeQueryImpl' : StateT (σ × QueryImpl ...) ProbComp
  - Interactive uses impl.addLift defaultChalImpl : StateT σ ProbComp

Key observation: When fsChallengeQueryImpl' state is defaultFSImpl, every challenge
query returns default (same as defaultChalImpl). The difference is:
  1. State type: FS carries extra `QueryImpl` state that never changes
  2. Oracle query type: FS queries include (StmtIn, MessagesUpTo) context

Proof strategy for support inclusion:
  For any output in FS support, construct the corresponding interactive execution
  that produces the same output. This works because:
  - oSpec queries: both use `impl`, identical
  - Challenge queries: both return `default`
  - Prover state evolution: identical given same challenges
  - Verifier execution: identical given same transcript

The Fin.induction lemma needed is:
  After simulating runToRoundFS with default FS impl and projecting to PrvState,
  we get the same distribution as simulating runToRound with defaultChalImpl.
-/

/-- The core bridging lemma: The PrvState after runToRoundFS (with default FS oracle)
    equals the PrvState after runToRound (with default challenge oracle).

    Note: This is stated at the OracleComp level, NOT after simulateQ.
    We need to show that after simulation with appropriate impls, the PrvState agrees.
-/
theorem runToRoundFS_prvState_eq_runToRound_aux
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (state₀ : P.PrvState 0) (i : Fin (n + 1))
    (s : σ) :
    -- We want to show that for any execution of runToRoundFS with default FS impl,
    -- there exists a corresponding execution of runToRound with defaultChalImpl
    -- that produces the same PrvState.
    --
    -- This is subtle because the two computations have different types.
    -- The cleanest statement might be via probOutput equality.
    True := by
  -- Placeholder - need to think about the right statement
  trivial

/-!
## Alternative approach: Work at the Reduction.run level directly

Instead of proving equality of runToRound variants, we can prove:

For any z in support(R.fiatShamir.run after FS simulation with default impl),
z is also in support(R.run after interactive simulation with default impl).

This avoids Fin.induction on runToRound and directly addresses the L319 goal.
-/

/-!
## Detailed type analysis for L319

The goal after `apply probEvent_eq_one_iff.mpr` is:
  `⟨Pr[⊥ | FS_comp] = 0, ∀ x ∈ support(FS_comp), success x⟩`

Where:
  - `FS_comp := OptionT.mk do (simulateQ fsImpl (R.fiatShamir.run stmtIn witIn)).run' (← fsInit)`
  - `fsInit := (← init, defaultFSImpl)`
  - `fsImpl := impl.addLift fsChallengeQueryImpl'`

We have:
  - `hNoFail : Pr[⊥ | int_comp_random] = 0`
  - `hAllSucceed : ∀ x ∈ support(int_comp_random), success x`
  - `hDefaultSubRandom : support(int_comp_default) ⊆ support(int_comp_random)`

Where:
  - `int_comp_random := OptionT.mk do (simulateQ (impl.addLift challengeQueryImpl) (R.run stmtIn witIn)).run' (← init)`
  - `int_comp_default := OptionT.mk do (simulateQ (impl.addLift defaultChalImpl) (R.run stmtIn witIn)).run' (← init)`

**What we need to prove:**
  `support(FS_comp) ⊆ support(int_comp_default)`

Then by transitivity: `support(FS_comp) ⊆ support(int_comp_random)`, and the goals follow.

**Type difference:**
  - `R.fiatShamir.run` : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec + [NI_Challenge]ₒ)) ...
  - `R.run` : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) ...

Wait - `R.fiatShamir` is a NI reduction, so it has its OWN challenge oracle for the NI protocol.
But that NI protocol has NO challenges (it's prover-only), so that challenge oracle is trivial.

Actually, the NI pSpec is `⟨!v[.P_to_V], !v[∀ i, pSpec.Message i]⟩` which has NO V→P rounds,
so `[NI_pSpec.Challenge]ₒ = []ₒ` (empty).

So `R.fiatShamir.run` lives in: OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) ...

And the `impl` used is: `impl.addLift fsChallengeQueryImpl'`
Which handles oSpec queries via `impl` and fsChallengeOracle queries via `fsChallengeQueryImpl'`.

The key insight: when `fsChallengeQueryImpl'` is given state `defaultFSImpl`, it returns `default`
for every challenge query (and keeps the state unchanged).

So conceptually:
  - FS execution queries fsChallengeOracle → gets default
  - Interactive execution with defaultChalImpl queries [pSpec.Challenge]ₒ → gets default

Both get the same challenge values! The difference is just:
  1. Oracle query TYPE (fsChallengeOracle includes context vs [pSpec.Challenge]ₒ doesn't)
  2. State threading (FS threads QueryImpl state, interactive doesn't)

For support inclusion, we need to show that the OUTPUT of the FS computation
(projected appropriately) is in the support of the interactive computation.

The outputs are:
  - FS: `((NI_Transcript × StmtOut × WitOut) × StmtOut)`
    where NI_Transcript = `∀ i, pSpec.Message i` (just the messages)
  - Interactive: `((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut)`
    where FullTranscript includes both messages AND challenges

For the probEvent predicate `(stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut`,
only `(StmtOut × WitOut) × StmtOut` matters, which is the same in both!

So the key lemma is: project both outputs to `(StmtOut × WitOut) × StmtOut`,
and show FS support (projected) ⊆ interactive support (projected).
-/

-- The projection from full output to the relevant components
def projectOutput {Proof : Type} {pSpec' : ProtocolSpec 1}
    (x : ((pSpec'.FullTranscript × StmtOut × WitOut) × StmtOut)) :
    (StmtOut × WitOut) × StmtOut :=
  ((x.1.2.1, x.1.2.2), x.2)

-- For NI transcript, it's just the messages
-- For interactive transcript, it includes challenges

-- The theorem we need for L319 (informally stated):
-- For any (prvStmtOut, witOut, stmtOut) in support of FS execution,
-- that same tuple is in support of interactive execution with default challenges.

-- This follows because:
-- 1. Prover evolution is determined by: oSpec queries + challenges received
-- 2. Both receive `default` for all challenges
-- 3. oSpec queries are handled identically by `impl`
-- 4. Verifier receives the same messages (from same prover state evolution)
-- 5. Verifier.fiatShamir.verify reconstructs transcript via fsChallengeOracle queries → default
--    Interactive Verifier.verify receives transcript with challenges already in it
-- 6. Both V.verify and V.fiatShamir.verify should produce the same stmtOut
--    (since transcript.messages is the same and transcript.challenges is default in both)

-- The subtlety is in (5) and (6): V.fiatShamir.verify uses deriveTranscriptFS which
-- queries fsChallengeOracle. When fsChallengeOracle returns default, the reconstructed
-- transcript has all challenges = default, which matches the interactive case.

/-!
## Task C: Intermediate lemma signatures

Based on the analysis, here are the key intermediate lemmas needed:
-/

section IntermediateLemmas

variable (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
variable (V : Verifier oSpec StmtIn StmtOut pSpec)
variable (stmt : StmtIn) (wit : WitIn) (s : σ)

-- Lemma 1: runToRoundFS with default FS oracle has same PrvState as runToRound with default chal
-- Note: The COMPUTATIONS are over different specs, so we compare AFTER simulation

/-- After simulation with default impls, runToRoundFS and runToRound produce the same PrvState
    (and same messages, though bookkeeping differs). -/
theorem runToRoundFS_simulated_prvState_eq (i : Fin (n + 1)) :
    -- We need to show this for all initial states
    -- The claim: for any state₀, the PrvState at round i is the same
    -- in both FS and interactive executions when challenges are default
    True := by trivial -- placeholder

-- Lemma 2: deriveTranscriptFS with default FS oracle produces transcript with default challenges
-- This is simpler because it's just iterating over messages and querying for challenges

/-- deriveTranscriptFS produces a transcript where all challenges are default
    when the FS oracle returns default. -/
theorem deriveTranscriptFS_default_challenges (messages : pSpec.Messages) :
    -- After simulation with default FS impl, deriveTranscriptFS produces
    -- a transcript where transcript.challenges i = default for all i
    True := by trivial -- placeholder

-- Lemma 3: V.fiatShamir.verify equals V.verify on the same transcript

/-- The FS verifier's verify function, after querying FS oracle to reconstruct transcript,
    equals the interactive verifier's verify function on that transcript. -/
theorem fiatShamir_verify_eq_verify (messages : pSpec.Messages)
    (transcript : pSpec.FullTranscript)
    (h_msg : ∀ i, transcript.messages i = messages i)
    (h_chal : ∀ i, transcript.challenges i = default) :
    -- V.fiatShamir.verify stmt (fun _ => messages) should equal V.verify stmt transcript
    -- after simulation with default FS impl
    True := by trivial -- placeholder

-- Lemma 4: Combining the above into support inclusion

/-- Main support inclusion lemma for fiatShamir_perfectCompleteness.

    The FS execution's support (projected to relevant outputs) is contained in
    the interactive execution's support with default challenges.

    Note: Both R.fiatShamir.run and R.run return OptionT (OracleComp ...) ..., so we
    need to handle the Option layer. The actual simulation happens on the OptionT.mk'd
    computation.
-/
theorem fiatShamir_support_subset_default_support
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    -- The statement is complex due to type differences. Informally:
    -- For any successful FS execution outcome (Some z), there exists a corresponding
    -- successful interactive execution outcome (Some z') with the same (StmtOut × WitOut × StmtOut).
    --
    -- The actual proof in Basic.lean uses probEvent on OptionT computations.
    -- The key insight is that after simulation:
    -- - FS prover produces messages via runToRoundFS with default challenges
    -- - Interactive prover produces transcript via runToRound with default challenges
    -- - Both give same PrvState evolution → same prover output
    -- - V.fiatShamir.verify reconstructs transcript with default challenges
    -- - V.verify receives transcript with default challenges (from runToRound)
    -- - Both verify the same transcript → same verifier output
    True := by trivial -- Placeholder for the actual complex statement

end IntermediateLemmas

end FSExecEquiv
