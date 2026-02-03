import VCVio

open OracleComp OracleSpec

section simp_lemmas -- Some extra lemmas that still need to move to vcv

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ ω : Type u}

@[simp]
lemma probFailure_bind_eq_zero_iff [spec.FiniteRange]
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    [⊥ | oa >>= ob] = 0 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, [⊥ | ob x] = 0 := by
  simp [probFailure_bind_eq_tsum, ← imp_iff_not_or]

@[simp] -- TODO: more general version/class for query impls that never have failures
lemma loggingOracle.probFailure_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
    [⊥ | (simulateQ loggingOracle oa).run] = [⊥ | oa] := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [ih, probFailure_bind_eq_tsum]
  | failure => simp

@[simp]
lemma probFailure_liftComp {ι' : Type w} {superSpec : OracleSpec ι'}
    [spec.FiniteRange] [superSpec.FiniteRange]
    [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : [⊥ | liftComp oa superSpec] = [⊥ | oa] := by
  simp only [OracleComp.probFailure_def, OracleComp.evalDist_liftComp]

/-- Spec-lifting preserves the failure probability. -/
@[simp]
lemma probFailure_liftComp_eq {ι' : Type} {superSpec : OracleSpec ι'}
    [spec.FiniteRange] [superSpec.FiniteRange]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : [⊥ | liftComp oa superSpec] = [⊥ | oa] := by
  simp only [OracleComp.probFailure_def, OracleComp.evalDist_liftComp]

@[simp]
lemma liftComp_support {ι' : Type w} {superSpec : OracleSpec ι'}
    [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : (liftComp oa superSpec).support = oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [ih]
  | failure => simp

-- Stub lemma for now, will be available in the next VCVio update
lemma neverFails_map_iff' (oa : OracleComp spec α) (f : α → β) :
    neverFails (f <$> oa) ↔ neverFails oa := by
  rw [map_eq_bind_pure_comp]
  simp [neverFails, neverFailsWhen, Function.comp_apply, implies_true, and_true]

/-- Bridge between monadic support and deterministic results for pure ProbComp. -/
@[simp]
lemma support_pure_bind_pure {α β : Type} (x : α) (f : α → ProbComp β) :
    (pure x >>= f).support = (f x).support :=
by simp

alias support_pure_bind := support_pure_bind_pure

/-- Simplifies the probability event of a deterministic pure result. -/
@[simp]
lemma probEvent_pure_iff {α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p] (x : α) :
    [p | (pure x : ProbComp α)] = 1 ↔ p x :=
by
  simp only [probEvent_pure, ite_eq_left_iff]
  exact ⟨fun h => by simpa using h, fun h => by simp [h]⟩

alias probEvent_eq_one_pure_iff := probEvent_pure_iff

end simp_lemmas

/-! ### StateT Helper Lemmas

Generic helper lemmas for `StateT` operations that simplify reasoning about
`run`, `run'`, and monadic operations in the probability monad.

These lemmas unfold stateful computations into their underlying probability distributions.
-/

namespace StateT

universe u v w

variable {m : Type u → Type v} {σ α β : Type u}

/-- Unfolding lemma for `run'` on `pure`. -/
@[simp]
theorem run'_pure_lib [Monad m] [LawfulMonad m] (x : α) (s : σ) :
    (pure x : StateT σ m α).run' s = (pure x : m α) := by
  simp only [run', pure, StateT.pure, map_pure]

/-- Unfolding lemma for `run'` on `bind`. -/
@[simp]
theorem run'_bind_lib [Monad m] [LawfulMonad m] (ma : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (ma >>= f).run' s = ((ma.run s) >>= fun (a, s') => (f a).run' s') := by
  simp only [run', bind, StateT.bind, map_bind, run]

/-- Unfolding lemma for `run` on `liftM`. -/
@[simp]
theorem run_liftM_lib [Monad m] [LawfulMonad m] (ma : m α) (s : σ) :
    (liftM ma : StateT σ m α).run s = (ma >>= fun a => pure (a, s)) := by
  simp only [run, liftM, bind_pure_comp]
  rw [map_eq_pure_bind]; rfl

/-- Simplify a bind following a pure initialization of state. -/
@[simp]
theorem run'_bind_pure [Monad m] [LawfulMonad m] {s : σ} (x : α) (f : α → StateT σ m β) :
    (StateT.run' (pure x >>= f) s) = (StateT.run' (f x) s) :=
by simp [StateT.run']

alias run'_pure_bind := run'_bind_pure

@[simp]
lemma mem_support_pure_stateT_run {ι σ α : Type} {spec : OracleSpec ι} (x : α) (s s' : σ) (y : α) :
  (y, s') ∈ OracleComp.support ((pure x : StateT σ (OracleComp spec) α).run s) ↔ y = x ∧ s' = s :=
by simp only [StateT.run_pure, OracleComp.support_pure, Set.mem_singleton_iff, Prod.mk.injEq]

@[simp]
lemma mem_support_pure_state {ι σ α : Type} {spec : OracleSpec ι} (x : α) (s s' : σ) (y : α) :
  (y, s') ∈ OracleComp.support ((pure x : StateT σ (OracleComp spec) α) s) ↔ y = x ∧ s' = s := by
    apply mem_support_pure_stateT_run

section MapLemmas

variable {ι : Type} {spec : OracleSpec ι}

/-- StateT.map distributes over if-then-else. -/
@[simp]
theorem map_ite [Monad m] (f : α → β) (p : Prop) [Decidable p]
    (ma ma' : StateT σ m α) (s : σ) :
    (if p then ma else ma').map f s =
    if p then ma.map f s else ma'.map f s := by
  split_ifs <;> rfl

/-- StateT.map over pure for OracleComp. -/
@[simp]
theorem map_pure (f : α → β) (a : α) (s : σ) :
    (pure a : StateT σ (OracleComp spec) α).map f s =
    pure (f a, s) := by
  rfl

/-- StateT.map over failure for OracleComp. -/
@[simp]
theorem map_failure (f : α → β) (s : σ) :
    (failure : StateT σ (OracleComp spec) α).map f s =
    failure := by
  rfl

/-- Support of StateT.map over pure. -/
@[simp]
theorem support_map_pure (f : α → β) (a : α) (s : σ) :
    ((pure a : StateT σ (OracleComp spec) α).map f s).support =
    {(f a, s)} := by
  simp only [map_pure, support_pure]

/-- Support of StateT.map over failure. -/
@[simp]
theorem support_map_failure (f : α → β) (s : σ) :
    ((failure : StateT σ (OracleComp spec) α).map f s).support =
    ∅ := by
  simp only [map_failure, support_failure]

/-- StateT.map with constant function over pure. Useful for `map (fun _ => result) (pure x)`. -/
@[simp]
theorem map_const_pure {γ : Type u} (result : β) (x : γ) (s : σ) :
    (pure x : StateT σ (OracleComp spec) γ).map (fun _ => result) s =
    pure (result, s) := by
  rfl

/-- Support of StateT.map with constant function over pure. -/
@[simp]
theorem support_map_const_pure {γ : Type u} (result : β) (x : γ) (s : σ) :
    ((pure x : StateT σ (OracleComp spec) γ).map (fun _ => result) s).support =
    {(result, s)} := by
  simp only [map_const_pure, support_pure]

/-- Support distributes over if-then-else for StateT with OracleComp. -/
@[simp]
theorem support_ite (p : Prop) [Decidable p]
    (ma ma' : StateT σ (OracleComp spec) α) (s : σ) :
    ((if p then ma else ma') s).support =
    if p then (ma s).support else (ma' s).support := by
  split_ifs <;> rfl

end MapLemmas

end StateT
