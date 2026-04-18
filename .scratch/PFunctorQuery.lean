/-
Task B: Test PFunctor query evaluation through simulateQ_query

Goal: Determine whether simulateQ_query can fire on the internal 
PFunctor.FreeM.lift form that appears after simp chains.

Finding: simulateQ_query DOES work. The key is:
  - liftM (query t) = PFunctor.FreeM.lift (OracleQuery.mk t id) definitionally
  - simulateQ_query: simulateQ impl (liftM q) = q.cont <$> impl q.input
  - For query t, q.cont = id, so we get id <$> impl t = impl t
-/

import ArkLib.OracleReduction.FiatShamir.Basic

open ProtocolSpec OracleComp OracleSpec

universe u

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]

variable {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace PFunctorQueryTest

-- Let's test with a concrete example
variable (j : Fin n) (hDir : pSpec.dir j = Direction.V_to_P)
  (stmtIn : StmtIn) (messages : pSpec.MessagesUpTo j.castSucc)

-- Define the query input explicitly with full type
def theQueryInput (j : Fin n) (hDir : pSpec.dir j = Direction.V_to_P) 
    (stmtIn : StmtIn) (messages : pSpec.MessagesUpTo j.castSucc) : 
    (oSpec + fsChallengeOracle StmtIn pSpec).Domain :=
  Sum.inr ⟨⟨j, hDir⟩, (stmtIn, messages)⟩

-- Test 1: simulateQ_query works on liftM (query t)
example : 
    let fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) 
          (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp) :=
      impl.addLift fsChallengeQueryImpl'
    let t := theQueryInput j hDir stmtIn messages
    simulateQ fsImpl (liftM (query t)) = id <$> fsImpl t := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]

-- Test 2: What does fsImpl return for challenge queries?
example (s : σ) (f : QueryImpl (srChallengeOracle StmtIn pSpec) Id) : 
    let fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) 
          (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp) :=
      impl.addLift fsChallengeQueryImpl'
    let t := theQueryInput j hDir stmtIn messages
    (fsImpl t).run (s, f) = pure (f ⟨⟨j, hDir⟩, (stmtIn, messages)⟩, (s, f)) := by
  simp only [theQueryInput, QueryImpl.addLift, QueryImpl.add_apply_inr, 
    QueryImpl.liftTarget_apply, fsChallengeQueryImpl', liftM, 
    MonadLiftT.monadLift, MonadLift.monadLift, StateT.run, StateT.run_pure]
  rfl

-- Test 3: With defaultFSImpl, we get the default challenge
example (s : σ) : 
    let fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) 
          (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp) :=
      impl.addLift fsChallengeQueryImpl'
    let t := theQueryInput j hDir stmtIn messages
    (fsImpl t).run (s, defaultFSImpl) = 
      pure ((default : pSpec.Challenge ⟨j, hDir⟩), (s, defaultFSImpl)) := by
  simp only [theQueryInput, QueryImpl.addLift, QueryImpl.add_apply_inr, 
    QueryImpl.liftTarget_apply, fsChallengeQueryImpl', liftM, 
    MonadLiftT.monadLift, MonadLift.monadLift, StateT.run, StateT.run_pure,
    defaultFSImpl]
  rfl

-- CONCLUSION for Task B:
-- 1. simulateQ_query WORKS on liftM (query t) form
-- 2. The PFunctor.FreeM.lift form is definitionally equal to liftM, so no special handling needed
-- 3. For challenge queries (Sum.inr ...), addLift routes to fsChallengeQueryImpl'.liftTarget
-- 4. Running with (s, defaultFSImpl) gives (default, (s, defaultFSImpl))

-- The tactic sequence that works:
-- simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]
-- This reduces simulateQ impl (liftM (query t)) to id <$> impl t = impl t

end PFunctorQueryTest
