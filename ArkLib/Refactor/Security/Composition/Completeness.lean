/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Composition.Util

/-!
# Completeness Composition

Theorems about how completeness composes under `Reduction.comp` and `Reduction.compNth`.

## Main results

- `Reduction.completeness_comp` — completeness composes with error addition
- `Reduction.perfectCompleteness_comp` — perfect completeness composes
- `Reduction.completeness_compNth` — `n`-fold completeness with error `n * ε`
- `Reduction.perfectCompleteness_compNth` — `n`-fold perfect completeness
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal BigOperators

namespace ProtocolSpec

/-! ## Completeness Composition -/

section Completeness

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Reduction

open ProtocolSpec.Reduction

variable {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
  {pSpec₁ pSpec₂ : ProtocolSpec}
  {r₁ : Reduction (OracleComp oSpec) S₁ W₁ S₂ W₂ pSpec₁}
  {r₂ : Reduction (OracleComp oSpec) S₂ W₂ S₃ W₃ pSpec₂}

/-- Structural decomposition of a composed run with split challenges.

The key point is that we can run `r₁`'s verifier "between" the two prover stages, since
`hV₁` implies it makes no oracle queries and therefore does not affect the shared oracle state. -/
lemma run_comp_join_eq_bind
    (hV₁ : Verifier.OracleFree (oSpec := oSpec) r₁.verifier)
    (stmtIn : S₁) (witIn : W₁)
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    (r₁.comp r₂).run stmtIn witIn (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂) =
      (do
        let out₁ ← r₁.run stmtIn witIn ch₁
        let prover₂ ← r₂.prover out₁.2
        let (tr₂, out) ← Prover.run pSpec₂ prover₂ ch₂
        let ver₂ ←
          match out₁.1 with
          | none => pure none
          | some midStmt => (r₂.verifier midStmt tr₂).run
        return (ver₂, out)) := by
  classical
  rcases hV₁ with ⟨g₁, hg₁⟩
  have hv₁ : ∀ stmt tr, r₁.verifier stmt tr = OptionT.mk (pure (g₁ stmt tr)) := by
    intro stmt tr
    ext
    simpa using hg₁ stmt tr
  -- Unfold the composed run, rewrite the prover run using `run_comp_join_bind`,
  -- and simplify the transcript split `split (join tr₁ tr₂)`.
  simp only [run, comp, HonestProver.comp, Prod.mk.eta, Verifier.comp, OptionT.instMonad,
    OptionT.bind, OptionT.mk, Function.comp_apply, OptionT.pure, hv₁, pure_bind, bind_pure_comp,
    map_eq_bind_pure_comp, bind_assoc, Prover.run_comp_join_bind, Transcript.split_join,
    OptionT.run]
  -- What's left is purely a `match`/`bind` normalization: push the final continuation
  -- under the shared prefix of binds and split on `g₁ stmtIn tr₁`.
  refine bind_congr (x := r₁.prover (stmtIn, witIn)) (fun prover₁ => ?_)
  refine bind_congr (x := Prover.run pSpec₁ prover₁ ch₁) (fun a => ?_)
  refine bind_congr (x := r₂.prover a.2) (fun prover₂ => ?_)
  refine bind_congr (x := Prover.run pSpec₂ prover₂ ch₂) (fun b => ?_)
  cases h : g₁ stmtIn a.1 <;> simp only [pure_bind, Function.comp_apply]

end Reduction

/-- Completeness composes: if `r₁` has completeness error `ε₁` (relIn → relMid) and
`r₂` has completeness error `ε₂` (relMid → relOut), then `r₁.comp r₂` has
completeness error at most `ε₁ + ε₂` (relIn → relOut). -/
theorem Reduction.completeness_comp
    {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂]
    {relIn : Set (S₁ × W₁)} {relMid : Set (S₂ × W₂)} {relOut : Set (S₃ × W₃)}
    {r₁ : Reduction (OracleComp oSpec) S₁ W₁ S₂ W₂ pSpec₁}
    {r₂ : Reduction (OracleComp oSpec) S₂ W₂ S₃ W₃ pSpec₂}
    {Inv : σ → Prop}
    {ε₁ ε₂ : ℝ≥0}
    (hV₁ : Verifier.OracleFree (oSpec := oSpec) r₁.verifier)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h₁ : r₁.completeness impl Inv relIn relMid ε₁)
    (h₂ : r₂.completeness impl Inv relMid relOut ε₂) :
    @Reduction.completeness S₁ W₁ S₃ W₃ ι oSpec (pSpec₁ ++ pSpec₂)
      ChallengesSampleable.ofAppend σ impl Inv relIn relOut
      (r₁.comp r₂) (ε₁ + ε₂) := by
  classical
  -- Unfold definitions and reduce to a union bound over the two stages.
  intro stmtIn witIn hIn σ0 hσ0
  -- Materialize the `letI` instance from the statement so typeclass search can find it.
  letI : ChallengesSampleable (pSpec₁ ++ pSpec₂) :=
    ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
  -- Stage success predicates.
  let good₁ : (Option S₂ × (S₂ × W₂)) → Prop :=
    fun (ver1, mid) => ver1 = some mid.1 ∧ mid ∈ relMid
  let good₂ : (Option S₃ × (S₃ × W₃)) → Prop :=
    fun (ver2, out) => ver2 = some out.1 ∧ out ∈ relOut
  -- Stage 2 computation, parameterized by stage 1 output and stage 2 challenges.
  let stage₂OA (out₁ : Option S₂ × (S₂ × W₂)) (ch₂ : Challenges pSpec₂) :
      OracleComp oSpec (Option S₃ × (S₃ × W₃)) := do
    let prover₂ ← r₂.prover out₁.2
    let (tr₂, out) ← Prover.run pSpec₂ prover₂ ch₂
    let ver₂ ←
      match out₁.1 with
      | none => pure none
      | some midStmt => (r₂.verifier midStmt tr₂).run
    return (ver₂, out)
  -- Work with the stateful `run` (keeping the oracle state) and project to outputs via `Prod.fst`.
  let stage₁Run (ch₁ : Challenges pSpec₁) : StateT σ ProbComp (Option S₂ × (S₂ × W₂)) :=
    simulateQ impl (r₁.run stmtIn witIn ch₁)
  let stage₂Run (out₁ : Option S₂ × (S₂ × W₂)) (ch₂ : Challenges pSpec₂) :
      StateT σ ProbComp (Option S₃ × (S₃ × W₃)) :=
    simulateQ impl (stage₂OA out₁ ch₂)
  -- The composed experiment in stateful form (sampling split challenges explicitly).
  let exp : ProbComp ((Option S₃ × (S₃ × W₃)) × σ) := do
    let ch₁ ← sampleChallenges pSpec₁
    let ch₂ ← sampleChallenges pSpec₂
    (simulateQ impl ((r₁.comp r₂).run stmtIn witIn (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run σ0
  -- Rewrite `exp` using the structural decomposition lemma and `simulateQ_bind`.
  have hexp :
      exp =
        (do
          let ch₁ ← sampleChallenges pSpec₁
          let ch₂ ← sampleChallenges pSpec₂
          (stage₁Run ch₁).run σ0 >>= fun z₁ =>
            (stage₂Run z₁.1 ch₂).run z₁.2) := by
    -- unfold `exp` and rewrite the inner `run` using `run_comp_join_eq_bind`
    unfold exp
    -- rewrite the composed `run` under `simulateQ`
    simp_rw [ProtocolSpec.Reduction.run_comp_join_eq_bind (oSpec := oSpec) (r₁ := r₁) (r₂ := r₂)
      hV₁ stmtIn witIn]
    -- push `simulateQ` through the bind and unfold `stage₁Run` / `stage₂Run`
    simp [stage₁Run, stage₂Run, stage₂OA, simulateQ_bind]
  -- Swap `ch₂` sampling after stage 1 (at the level of probabilities).
  let swapped : ProbComp ((Option S₃ × (S₃ × W₃)) × σ) :=
    (do
      let ch₁ ← sampleChallenges pSpec₁
      let z₁ ← (stage₁Run ch₁).run σ0
      let ch₂ ← sampleChallenges pSpec₂
      (stage₂Run z₁.1 ch₂).run z₁.2)
  -- Define the stage-wise bind form.
  let mx : ProbComp ((Option S₂ × (S₂ × W₂)) × σ) := do
    let ch₁ ← sampleChallenges pSpec₁
    (stage₁Run ch₁).run σ0
  let my : ((Option S₂ × (S₂ × W₂)) × σ) → ProbComp ((Option S₃ × (S₃ × W₃)) × σ) :=
    fun z₁ => do
      let ch₂ ← sampleChallenges pSpec₂
      (stage₂Run z₁.1 ch₂).run z₁.2
  have hswapped_eq : swapped = mx >>= my := by
    simp [swapped, mx, my, bind_assoc]
  -- Convert the stage 1 completeness bound into a failure bound on `mx`.
  have h₁_success :
      Pr[(fun z₁ => good₁ z₁.1) | mx] ≥ (1 : ℝ≥0∞) - (ε₁ : ℝ≥0∞) := by
    -- Start from the `run'`-based completeness statement.
    have h₁' := h₁ stmtIn witIn hIn σ0 hσ0
    have h₁_good :
        Pr[good₁ | do
            let challenges ← sampleChallenges pSpec₁
            (stage₁Run challenges).run' σ0] ≥ (1 : ℝ≥0∞) - (ε₁ : ℝ≥0∞) := by
      simpa [good₁, stage₁Run, Reduction.completeness] using h₁'
    have hmx_run' :
        (do
            let challenges ← sampleChallenges pSpec₁
            (stage₁Run challenges).run' σ0) = Prod.fst <$> mx := by
      simp [mx, StateT.run', StateT.run, map_eq_bind_pure_comp, bind_assoc]
    have : Pr[good₁ | Prod.fst <$> mx] ≥ (1 : ℝ≥0∞) - (ε₁ : ℝ≥0∞) := by
      exact (hmx_run'.symm ▸ h₁_good)
    have : Pr[good₁ ∘ Prod.fst | mx] ≥ (1 : ℝ≥0∞) - (ε₁ : ℝ≥0∞) := by
      simpa [probEvent_map] using this
    simpa [Function.comp] using this
  have h₁_fail :
      Pr[(fun z₁ => ¬ good₁ z₁.1) | mx] ≤ (ε₁ : ℝ≥0∞) :=
    probEvent_compl_le_of_ge (by simp) h₁_success
  -- Stage 2 failure bound conditional on stage 1 success.
  have h₂_fail :
      ∀ z₁ ∈ support mx, good₁ z₁.1 →
        Pr[(fun z₂ => ¬ good₂ z₂.1) | my z₁] ≤ (ε₂ : ℝ≥0∞) := by
    intro z₁ hz₁ hgood₁
    rcases hgood₁ with ⟨hver, hrel⟩
    -- From stage 1 output in support, obtain invariant on the post-state.
    have hInv₁ : Inv z₁.2 := by
      -- peel off the `sampleChallenges` bind in `mx`
      simp only [mx, mem_support_bind_iff] at hz₁
      rcases hz₁ with ⟨ch₁, hch₁, hz₁'⟩
      -- apply the invariant-preservation lemma to the stage 1 oracle computation
      exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
        (oa := r₁.run stmtIn witIn ch₁) σ0 hσ0 _ hz₁')
    -- Instantiate stage 2 completeness on the mid statement/witness.
    have h₂' := h₂ z₁.1.2.1 z₁.1.2.2 hrel z₁.2 hInv₁
    -- Rewrite `my z₁` under `hver` to match `r₂.run` on the same input statement.
    have : Pr[(fun z₂ => good₂ z₂.1) | my z₁] ≥ (1 : ℝ≥0∞) - (ε₂ : ℝ≥0∞) := by
      -- First transfer `h₂'` (a `run'`-based bound) to the stateful experiment `my z₁`.
      let myRun' : ProbComp (Option S₃ × (S₃ × W₃)) := do
        let ch₂ ← sampleChallenges pSpec₂
        (stage₂Run z₁.1 ch₂).run' z₁.2
      have hmyRun'_eq : myRun' = (fun z => z.1) <$> (my z₁) := by
        simp [myRun', my, StateT.run', StateT.run]
      have hstage₂OA_eq (ch₂ : Challenges pSpec₂) :
          stage₂OA z₁.1 ch₂ = r₂.run z₁.1.2.1 z₁.1.2.2 ch₂ := by
        -- Under `hver`, stage 2 is exactly `r₂.run`.
        simp [stage₂OA, ProtocolSpec.Reduction.run, hver, OptionT.run]
      have h₂_good : Pr[good₂ | myRun'] ≥ (1 : ℝ≥0∞) - (ε₂ : ℝ≥0∞) := by
        -- Under `hver`, stage 2 is exactly `r₂.run`.
        simpa [myRun', stage₂Run, hstage₂OA_eq, good₂, Reduction.completeness] using h₂'
      have h₂_good_map : Pr[good₂ | (fun z => z.1) <$> (my z₁)] ≥
          (1 : ℝ≥0∞) - (ε₂ : ℝ≥0∞) := by
        simpa [hmyRun'_eq] using h₂_good
      -- Now rewrite back using `probEvent_map`.
      simpa [probEvent_map] using h₂_good_map
    exact probEvent_compl_le_of_ge (by simp) this
  -- Apply the union bound lemma on the swapped experiment.
  have hfail_swapped :
      Pr[(fun z₂ => ¬ good₂ z₂.1) | swapped] ≤ (ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞) := by
    rw [hswapped_eq]
    exact probEvent_bind_le_add (mx := mx) (my := my)
      (p := fun z₁ => good₁ z₁.1) (q := fun z₂ => good₂ z₂.1)
      h₁_fail (by
        intro z₁ hz₁ hp
        exact h₂_fail z₁ hz₁ hp)
  -- Transfer the failure bound back to the original `exp`.
  have hfail_exp :
      Pr[(fun z₂ => ¬ good₂ z₂.1) | exp] ≤ (ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞) := by
    have hPr_bad :
        Pr[(fun z₂ => ¬ good₂ z₂.1) | exp] =
          Pr[(fun z₂ => ¬ good₂ z₂.1) | swapped] := by
      rw [hexp]
      refine probEvent_bind_congr fun ch₁ _ => ?_
      exact probEvent_bind_bind_swap
        (mx := sampleChallenges pSpec₂)
        (my := (stage₁Run ch₁).run σ0)
        (f := fun ch₂ z₁ => (stage₂Run z₁.1 ch₂).run z₁.2)
        (q := fun z₂ => ¬ good₂ z₂.1)
    simpa [hPr_bad] using hfail_swapped
  have hsucc_exp :
      Pr[(fun z₂ => good₂ z₂.1) | exp] ≥
        (1 : ℝ≥0∞) - ((ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞)) :=
    probEvent_ge_of_compl_le (by simp) hfail_exp
  -- Map from `exp` (stateful `run`) back to the `run'`-based probability.
  -- Convert the stateful `exp` bound to the `run'`-based experiment.
  have hsucc_exp' :
      Pr[good₂ | Prod.fst <$> exp] ≥ (1 : ℝ≥0∞) - ((ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞)) := by
    simpa [probEvent_map] using hsucc_exp
  -- Identify `Prod.fst <$> exp` with the `run'`-based experiment in `Reduction.completeness`.
  have hexp' :
      Prod.fst <$> exp =
        (do
          let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
          (simulateQ impl ((r₁.comp r₂).run stmtIn witIn challenges)).run' σ0) := by
    have hsample : sampleChallenges (pSpec₁ ++ pSpec₂) = do
        let ch₁ ← sampleChallenges pSpec₁
        let ch₂ ← sampleChallenges pSpec₂
        return Challenges.join pSpec₁ pSpec₂ ch₁ ch₂ := rfl
    simp [exp, hsample, StateT.run', StateT.run]
  have : Pr[good₂ | do
        let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
        (simulateQ impl ((r₁.comp r₂).run stmtIn witIn challenges)).run' σ0] ≥
        (1 : ℝ≥0∞) - ((ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞)) := by
    simpa [hexp'] using hsucc_exp'
  simpa [Reduction.completeness, good₂] using this

/-- The identity reduction has perfect completeness. -/
lemma Reduction.id_perfectCompleteness
    {S W : Type} {rel : Set (S × W)} {Inv : σ → Prop} :
    (Reduction.id : Reduction (OracleComp oSpec) S W S W []).perfectCompleteness
      impl Inv rel rel := by
  intro stmtIn witIn hIn σ0 _
  have hrun : Reduction.id.run (m := OracleComp oSpec) stmtIn witIn
      (HVector.nil : Challenges ([] : ProtocolSpec)) =
      (pure (some stmtIn, (stmtIn, witIn)) : OracleComp oSpec _) := by
    unfold Reduction.run
    simp only [Reduction.id, Prover.run, pure_bind]
    change (do
      let verResult ← (pure (some stmtIn) : OracleComp oSpec (Option S))
      pure (verResult, stmtIn, witIn)) = _
    simp only [pure_bind]
  simp only [sampleChallenges, ChallengesSampleable.sampleChallenges, pure_bind]
  rw [hrun, simulateQ_pure]
  simp only [StateT.run']
  simp only [show (pure (some stmtIn, (stmtIn, witIn)) : StateT σ ProbComp _) σ0 =
    (pure ((some stmtIn, (stmtIn, witIn)), σ0) : ProbComp _) from rfl]
  simp only [map_pure]
  rw [show (1 : ℝ≥0∞) - ((0 : ℝ≥0) : ℝ≥0∞) = 1 from by simp]
  exact le_of_eq (probEvent_eq_one ⟨probFailure_pure _, fun x hx => by
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact ⟨rfl, hIn⟩⟩).symm

/-- Perfect completeness composes. -/
theorem Reduction.perfectCompleteness_comp
    {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂]
    {relIn : Set (S₁ × W₁)} {relMid : Set (S₂ × W₂)} {relOut : Set (S₃ × W₃)}
    {r₁ : Reduction (OracleComp oSpec) S₁ W₁ S₂ W₂ pSpec₁}
    {r₂ : Reduction (OracleComp oSpec) S₂ W₂ S₃ W₃ pSpec₂}
    {Inv : σ → Prop}
    (hV₁ : Verifier.OracleFree (oSpec := oSpec) r₁.verifier)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h₁ : r₁.perfectCompleteness impl Inv relIn relMid)
    (h₂ : r₂.perfectCompleteness impl Inv relMid relOut) :
    @Reduction.perfectCompleteness S₁ W₁ S₃ W₃ ι oSpec (pSpec₁ ++ pSpec₂)
      ChallengesSampleable.ofAppend σ impl Inv relIn relOut
      (r₁.comp r₂) := by
  have := @Reduction.completeness_comp ι oSpec σ impl
    S₁ W₁ S₂ W₂ S₃ W₃ pSpec₁ pSpec₂ _ _
    relIn relMid relOut r₁ r₂ Inv 0 0 hV₁ hPres h₁ h₂
  simpa [Reduction.perfectCompleteness] using this

section CompNth

set_option allowUnsafeReducibility true
attribute [local irreducible] Reduction.completeness

/-- Perfect completeness of `n`-fold composition: if one round is perfectly complete,
then `n` rounds are perfectly complete. -/
theorem Reduction.perfectCompleteness_compNth
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {r : Reduction (OracleComp oSpec) S W S W pSpec}
    {Inv : σ → Prop}
    (hV : Verifier.OracleFree (oSpec := oSpec) r.verifier)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : r.perfectCompleteness impl Inv rel rel) (n : Nat) :
    @Reduction.perfectCompleteness S W S W ι oSpec (pSpec.replicate n)
      (ChallengesSampleable.ofReplicate n) σ impl Inv rel rel (r.compNth n) := by
  induction n with
  | zero => exact Reduction.id_perfectCompleteness impl
  | succ n ih =>
      exact @Reduction.perfectCompleteness_comp ι oSpec σ impl
        S W S W S W pSpec (pSpec.replicate n)
        ‹ChallengesSampleable pSpec› (ChallengesSampleable.ofReplicate n)
        rel rel rel r (r.compNth n) Inv
        hV hPres h ih

/-- Completeness of `n`-fold composition with error `n * ε`. -/
theorem Reduction.completeness_compNth
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {r : Reduction (OracleComp oSpec) S W S W pSpec}
    {Inv : σ → Prop}
    {ε : ℝ≥0}
    (hV : Verifier.OracleFree (oSpec := oSpec) r.verifier)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : r.completeness impl Inv rel rel ε) (n : Nat) :
    @Reduction.completeness S W S W ι oSpec (pSpec.replicate n)
      (ChallengesSampleable.ofReplicate n) σ impl Inv rel rel (r.compNth n) (n * ε) := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul]
      exact Reduction.id_perfectCompleteness impl
  | succ n ih =>
      rw [show (↑(n + 1) : ℝ≥0) * ε = ε + ↑n * ε from by push_cast; ring]
      exact @Reduction.completeness_comp ι oSpec σ impl
        S W S W S W pSpec (pSpec.replicate n)
        ‹ChallengesSampleable pSpec› (ChallengesSampleable.ofReplicate n)
        rel rel rel r (r.compNth n) Inv ε (↑n * ε)
        hV hPres h ih

end CompNth

end Completeness

end ProtocolSpec
