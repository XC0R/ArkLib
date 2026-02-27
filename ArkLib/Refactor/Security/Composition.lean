/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.StateFunction
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import VCVio.EvalDist.Fintype
import VCVio.EvalDist.Monad.Map

/-!
# Composition of Security Properties

Theorems about how completeness, soundness, and round-by-round (RBR) soundness
compose under `Reduction.comp` and `Reduction.compNth`.

## Main results

### Completeness
- `Reduction.completeness_comp` — completeness composes with error addition
- `Reduction.perfectCompleteness_comp` — perfect completeness composes
- `Reduction.completeness_compNth` — `n`-fold completeness with error `n * ε`
- `Reduction.perfectCompleteness_compNth` — `n`-fold perfect completeness

### Soundness
- `rbrSoundness_implies_soundness` — RBR soundness implies overall soundness
- `Verifier.soundness_compNth` — soundness of `n`-fold composition

### Knowledge Soundness
- `rbrKnowledgeSoundness_implies_knowledgeSoundness` — RBR k.s. implies overall k.s.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal BigOperators

namespace HVector

lemma splitAt_append {α : Type*} {A : α → Type*}
    (l₁ l₂ : List α) (v₁ : HVector A l₁) (v₂ : HVector A l₂) :
    HVector.splitAt (A := A) l₁ (HVector.append v₁ v₂) = (v₁, v₂) := by
  induction l₁ with
  | nil =>
      simp [HVector.splitAt, HVector.append]
  | cons _ tl ih =>
      cases v₁ with
      | mk hd tlv =>
          simp [HVector.splitAt, HVector.append, ih (v₁ := tlv)]

end HVector

namespace ProtocolSpec

namespace Verifier

/-- `OracleFree v` means `v` does not query the shared oracle: its underlying `OracleComp`
computation is `pure` (hence independent of oracle state and query history). -/
def OracleFree {ι : Type} {oSpec : OracleSpec ι} {SIn SOut : Type} {pSpec : ProtocolSpec}
    (v : Verifier (OracleComp oSpec) SIn SOut pSpec) : Prop :=
  ∃ g : SIn → Transcript pSpec → Option SOut,
    ∀ stmt tr, (v stmt tr).run = pure (g stmt tr)

/-- `StatePreserving impl v` means that, after simulating the verifier under `impl`,
running it never changes the shared oracle state. -/
def StatePreserving {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) {SIn SOut : Type} {pSpec : ProtocolSpec}
    (v : Verifier (OracleComp oSpec) SIn SOut pSpec) : Prop :=
  ∀ stmt tr, StateT.StatePreserving (simulateQ impl (v stmt tr).run)

/-- `OutputIndependent impl Inv v` means the simulated verifier's output distribution
does not depend on the initial oracle state, as long as it satisfies `Inv`. -/
def OutputIndependent {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (Inv : σ → Prop)
    {SIn SOut : Type} {pSpec : ProtocolSpec}
    (v : Verifier (OracleComp oSpec) SIn SOut pSpec) : Prop :=
  ∀ stmt tr, StateT.OutputIndependent (simulateQ impl (v stmt tr).run) Inv

lemma oracleFree_statePreserving {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {SIn SOut : Type} {pSpec : ProtocolSpec}
    {v : Verifier (OracleComp oSpec) SIn SOut pSpec}
    (h : OracleFree v) :
    StatePreserving impl v := by
  rcases h with ⟨g, hg⟩
  intro stmt tr
  -- rewrite to `pure`
  simp [hg]

lemma oracleFree_outputIndependent {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (Inv : σ → Prop)
    {SIn SOut : Type} {pSpec : ProtocolSpec}
    {v : Verifier (OracleComp oSpec) SIn SOut pSpec}
    (h : OracleFree v) :
    OutputIndependent impl Inv v := by
  rcases h with ⟨g, hg⟩
  intro stmt tr
  -- rewrite to `pure`
  simp [hg]

/-!
### Why this hypothesis appears

In `Reduction.run` for a sequentially composed reduction `r₁.comp r₂`, we run the *full* composed
prover first (which executes `r₁`'s prover and then `r₂`'s prover), and only afterwards run the
composed verifier (which runs `r₁`'s verifier and then `r₂`'s verifier).

When the two stages share a stateful oracle implementation
`impl : QueryImpl oSpec (StateT σ ProbComp)`,
`r₂`'s prover may query the oracle and mutate the shared state *before* `r₁`'s verifier runs.
Thus, the usual textbook completeness composition argument is not valid without an additional
non-interference hypothesis. The minimal such hypothesis in the current model is that `r₁.verifier`
is oracle-free; we use `OracleFree` as a convenient sufficient condition.
-/

lemma oracleFree_comp {ι : Type} {oSpec : OracleSpec ι}
    {S₁ S₂ S₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    {v₁ : Verifier (OracleComp oSpec) S₁ S₂ pSpec₁}
    {v₂ : Verifier (OracleComp oSpec) S₂ S₃ pSpec₂}
    (hV₁ : OracleFree v₁) (hV₂ : OracleFree v₂) :
    OracleFree (Verifier.comp v₁ v₂) := by
  rcases hV₁ with ⟨g₁, hg₁⟩
  rcases hV₂ with ⟨g₂, hg₂⟩
  have hv₁ : ∀ stmt tr, v₁ stmt tr = OptionT.mk (pure (g₁ stmt tr)) := by
    intro stmt tr; ext; simpa using hg₁ stmt tr
  have hv₂ : ∀ stmt tr, v₂ stmt tr = OptionT.mk (pure (g₂ stmt tr)) := by
    intro stmt tr; ext; simpa using hg₂ stmt tr
  refine ⟨fun stmt tr =>
    let (tr₁, tr₂) := Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) tr
    (g₁ stmt tr₁).bind (fun mid => g₂ mid tr₂), fun stmt tr => ?_⟩
  simp only [Verifier.comp, hv₁, hv₂, OptionT.instMonad, OptionT.bind, OptionT.mk,
    OptionT.run, pure_bind]
  cases g₁ stmt (Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) tr).1 <;> simp

end Verifier

namespace Reduction

lemma oracleFree_compNth_verifier {ι : Type} {oSpec : OracleSpec ι}
    {S W : Type} {pSpec : ProtocolSpec}
    {r : Reduction (OracleComp oSpec) S W S W pSpec}
    (hV : Verifier.OracleFree r.verifier) :
    (n : Nat) → Verifier.OracleFree (r.compNth n).verifier
  | 0 => ⟨fun stmt _ => some stmt, fun _ _ => rfl⟩
  | n + 1 => Verifier.oracleFree_comp hV (oracleFree_compNth_verifier hV n)

end Reduction

namespace Transcript

lemma split_join {pSpec₁ pSpec₂ : ProtocolSpec}
    (tr₁ : Transcript pSpec₁) (tr₂ : Transcript pSpec₂) :
    Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (Transcript.join tr₁ tr₂) =
      (tr₁, tr₂) := by
  simp [Transcript.split, Transcript.join, HVector.splitAt_append]

end Transcript

namespace Prover

open ProtocolSpec.Prover

lemma run_comp_join {m : Type → Type} [Monad m] [LawfulMonad m]
    {Mid Output : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : Prover m Mid pSpec₁)
    (f : Mid → m (Prover m Output pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    (do
      let prover ← Prover.comp (m := m) (Mid := Mid) (Output := Output) (pSpec₂ := pSpec₂)
        pSpec₁ prover₁ f
      Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
        (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂)) =
      (do
        let (tr₁, mid) ← Prover.run (m := m) (Output := Mid) pSpec₁ prover₁ ch₁
        let prover₂ ← f mid
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ prover₂ ch₂
        return (Transcript.join tr₁ tr₂, out)) := by
  -- Induction on `pSpec₁`, mirroring the definitions of `Prover.comp` and `Prover.run`.
  revert prover₁ ch₁
  induction pSpec₁ with
  | nil =>
      intro prover₁ ch₁
      simp [Prover.comp, Prover.run, Challenges.join, Transcript.join, HVector.append]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover₁ ch₁
          rcases prover₁ with ⟨msg, cont⟩
          -- `P_to_V` consumes no challenges.
          -- Both sides are `cont >>= fun next => ...`; apply the IH pointwise.
          simp only [List.cons_append, comp, List.append_eq, Challenges.join, run, bind_pure_comp,
            pure_bind, bind_assoc, Transcript.join, bind_map_left]
          refine congrArg (fun k => cont >>= k) ?_
          funext next
          simpa [Prover.comp, Prover.run, Challenges.join, Transcript.join] using
            congrArg (fun z =>
              (fun a : Transcript (tl ++ pSpec₂) × Output =>
                (Transcript.cons (r := .P_to_V T oi) msg a.1, a.2)) <$> z)
              (ih (prover₁ := next) (ch₁ := ch₁))
      | V_to_P T =>
          intro prover₁ ch₁
          -- `V_to_P` consumes one challenge from `ch₁`.
          cases ch₁ with
          | mk chal chTail =>
              simp only [List.cons_append, comp, List.append_eq, Challenges.join, id_eq, run,
                HVector.head_cons, HVector.tail_cons, bind_pure_comp, pure_bind, bind_assoc,
                Transcript.join, bind_map_left]
              refine congrArg (fun k => prover₁ chal >>= k) ?_
              funext next
              simpa [Prover.comp, Prover.run, Challenges.join, Transcript.join] using
                congrArg (fun z =>
                  (fun a : Transcript (tl ++ pSpec₂) × Output =>
                    (Transcript.cons (r := .V_to_P T) chal a.1, a.2)) <$> z)
                  (ih (prover₁ := next) (ch₁ := chTail))

/-- Variant of `run_comp_join` with an extra continuation `k` after the run. -/
lemma run_comp_join_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    {Mid Output α : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : Prover m Mid pSpec₁)
    (f : Mid → m (Prover m Output pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂)
    (k : Transcript (pSpec₁ ++ pSpec₂) × Output → m α) :
    (do
      let prover ← Prover.comp (m := m) (Mid := Mid) (Output := Output) (pSpec₂ := pSpec₂)
        pSpec₁ prover₁ f
      let z ← Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
        (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂)
      k z) =
      (do
        let (tr₁, mid) ← Prover.run (m := m) (Output := Mid) pSpec₁ prover₁ ch₁
        let prover₂ ← f mid
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ prover₂ ch₂
        k (Transcript.join tr₁ tr₂, out)) := by
  -- Apply `>>= k` to both sides of `run_comp_join`.
  simpa [bind_assoc] using congrArg (fun z => z >>= k) (run_comp_join (m := m)
    (prover₁ := prover₁) (f := f) (ch₁ := ch₁) (ch₂ := ch₂))

/-- Extract the first-stage prover from a prover over `pSpec₁ ++ pSpec₂`.
Running the extracted prover over `pSpec₁` returns the residual prover for `pSpec₂`. -/
def splitPrefix {m : Type → Type} [Monad m] {Output : Type} :
    (pSpec₁ : ProtocolSpec) → {pSpec₂ : ProtocolSpec} →
    Prover m Output (pSpec₁ ++ pSpec₂) → Prover m (Prover m Output pSpec₂) pSpec₁
  | [], _, prover => prover
  | (.P_to_V _ _) :: tl, _, prover =>
      let (msg, cont) := prover
      (msg, do
        let next ← cont
        return splitPrefix tl next)
  | (.V_to_P _) :: tl, _, prover =>
      fun chal => do
        let next ← prover chal
        return splitPrefix tl next

end Prover

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

The key point is that we can run `r₁`'s verifier “between” the two prover stages, since
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

/-! ## RBR Soundness → Soundness -/

section Soundness

variable {StmtIn StmtOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

lemma probEvent_exists_finset_le_sum
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {α : Type} {ι : Type} (s : Finset ι) (mx : m α) (E : ι → α → Prop)
    :
    Pr[(fun x => ∃ i ∈ s, E i x) | mx] ≤ Finset.sum s (fun i => Pr[E i | mx]) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hE :
        (fun x => ∃ i ∈ insert a s, E i x) = fun x => E a x ∨ ∃ i ∈ s, E i x := by
      funext x
      apply propext
      constructor
      · rintro ⟨i, hi, hix⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact Or.inl hix
        · exact Or.inr ⟨i, hi', hix⟩
      · intro hx
        cases hx with
        | inl hax => exact ⟨a, Finset.mem_insert_self _ _, hax⟩
        | inr hx' =>
            rcases hx' with ⟨i, hi, hix⟩
            exact ⟨i, Finset.mem_insert_of_mem hi, hix⟩
    have hor :
        Pr[(fun x => E a x ∨ ∃ i ∈ s, E i x) | mx]
          ≤ Pr[E a | mx] + Pr[(fun x => ∃ i ∈ s, E i x) | mx] := by
      rw [probEvent_eq_tsum_ite (mx := mx) (p := fun x => E a x ∨ ∃ i ∈ s, E i x)]
      rw [probEvent_eq_tsum_ite (mx := mx) (p := E a)]
      rw [probEvent_eq_tsum_ite (mx := mx) (p := fun x => ∃ i ∈ s, E i x)]
      have hle :
          (∑' y : α, if (E a y ∨ ∃ i ∈ s, E i y) then Pr[= y | mx] else 0)
            ≤ (∑' y : α, ((if E a y then Pr[= y | mx] else 0)
                + (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0))) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases ha' : E a y <;> by_cases hs' : (∃ i ∈ s, E i y) <;>
          simp [ha', hs']
      have hspl :
          (∑' y : α, ((if E a y then Pr[= y | mx] else 0)
              + (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)))
            =
          (∑' y : α, (if E a y then Pr[= y | mx] else 0))
            + (∑' y : α, (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)) := by
        simpa using (ENNReal.tsum_add
          (f := fun y : α => (if E a y then Pr[= y | mx] else 0))
          (g := fun y : α => (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)))
      exact le_trans hle (le_of_eq hspl)
    have hsum :
        Pr[E a | mx] + Pr[(fun x => ∃ i ∈ s, E i x) | mx]
          ≤ Pr[E a | mx] + Finset.sum s (fun i => Pr[E i | mx]) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih (Pr[E a | mx])
    have :
        Pr[(fun x => E a x ∨ ∃ i ∈ s, E i x) | mx]
          ≤ Pr[E a | mx] + Finset.sum s (fun i => Pr[E i | mx]) :=
      le_trans hor hsum
    simpa [hE, Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using this

private lemma cast_cons_hvector {r : Round} {l₁ l₂ : List Round}
    (h : l₁ = l₂) (hd : r.type) (tltr : HVector Round.type l₁) :
    (hd, cast (congrArg (fun l => HVector Round.type l) h) tltr) =
      cast (congrArg (fun l => HVector Round.type (r :: l)) h) (hd, tltr) := by
  cases h
  rfl

private lemma hvector_take_length_eq {pSpec : ProtocolSpec} (tr : Transcript pSpec) :
    HVector.take pSpec.length pSpec tr = PartialTranscript.ofTranscript tr := by
  induction pSpec with
  | nil =>
      cases tr
      rfl
  | cons r tl ih =>
      cases tr with
      | mk hd tltr =>
          simpa [HVector.take, PartialTranscript.ofTranscript, ih tltr, List.take_length]
            using cast_cons_hvector (h := (List.take_length (l := tl)).symm) hd tltr

private lemma hvector_take_succ_eq_concat {pSpec : ProtocolSpec}
    (k : Nat) (hk : k < pSpec.length) (tr : Transcript pSpec) :
    HVector.take (k + 1) pSpec tr =
      PartialTranscript.concat pSpec hk (HVector.take k pSpec tr)
        (HVector.get pSpec tr ⟨k, hk⟩) := by
  induction pSpec generalizing k with
  | nil =>
      cases hk
  | cons r tl ih =>
      cases k with
      | zero =>
          cases tr
          simp [HVector.take, PartialTranscript.concat, HVector.get, HVector.cons]
      | succ k =>
          cases tr with
          | mk hd tltr =>
              have hk' : k < tl.length := by simpa using hk
              simpa [HVector.take, PartialTranscript.concat, HVector.get, HVector.cons,
                HVector.head, HVector.tail] using
                congrArg (fun t => (hd, t)) (ih k hk' tltr)

set_option maxHeartbeats 800000 in
-- This theorem performs several large dependent rewrites over `ProbComp` binds and
-- transcript casts; the default heartbeat budget times out during elaboration.
/-- RBR soundness implies overall soundness. The total soundness error is bounded by
the sum of per-round RBR errors over all challenge rounds.

**Proof strategy**:
1. Extract the state function `sf` from `rbrSoundness`.
2. For `stmtIn ∉ langIn`, `¬sf.toFun 0 stmtIn HVector.nil` (by `toFun_empty`).
3. Bound `Pr[accept]` by `Pr[sf.toFun pSpec.length stmtIn tr]` using `toFun_full` and
   `PreservesInv` (the verifier cannot accept when the state function is false at the end).
4. By `toFun_next`, the state can only flip from false to true at challenge rounds.
5. Union bound: `Pr[∃ i, flip at i] ≤ Σ Pr[flip at i] ≤ Σ rbrError i`.
-/
theorem rbrSoundness_implies_soundness
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrSoundness impl langIn langOut verifier Inv rbrError) :
    verifier.soundness init impl langIn langOut
      (Finset.sum Finset.univ rbrError) := by
  classical
  obtain ⟨sf, hrbr⟩ := h
  intro Output prover stmtIn hstmtIn
  have _hstart : ¬ sf.toFun 0 stmtIn HVector.nil :=
    fun hf => hstmtIn ((sf.toFun_empty stmtIn).mpr hf)
  let ε : ℝ≥0∞ := (Finset.sum Finset.univ rbrError : ℝ≥0)
  let accept : (Option StmtOut × Output) → Prop :=
    fun z => ∃ s ∈ langOut, z.1 = some s
  let expPair : σ → ProbComp (Option StmtOut × Output) := fun σ0 => do
    let z ← (do
      let challenges ← sampleChallenges pSpec
      (simulateQ impl (Prover.run pSpec prover challenges)).run σ0)
    let verResult ← (simulateQ impl (verifier stmtIn z.1.1)).run' z.2
    return (verResult, z.1.2)
  have probEvent_some_eq_optionT :
      ∀ (mxo : ProbComp (Option StmtOut)),
        Pr[(fun o => ∃ s ∈ langOut, o = some s) | mxo] =
          Pr[(· ∈ langOut) | (OptionT.mk mxo : OptionT ProbComp StmtOut)] := by
    intro mxo
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    rw [tsum_option (f := fun o : Option StmtOut =>
      if (∃ s ∈ langOut, o = some s) then Pr[= o | mxo] else 0) ENNReal.summable]
    simp [OptionT.probOutput_eq]
  have htake_full (tr : Transcript pSpec) :
      HVector.take pSpec.length pSpec tr = PartialTranscript.ofTranscript tr := by
    exact hvector_take_length_eq (tr := tr)
  have hσbound : ∀ σ0, Inv σ0 → Pr[accept | expPair σ0] ≤ ε := by
    intro σ0 hσ0
    let mxRun : ProbComp ((Transcript pSpec × Output) × σ) := do
      let challenges ← sampleChallenges pSpec
      (simulateQ impl (Prover.run pSpec prover challenges)).run σ0
    let mx0 : ProbComp (Transcript pSpec × Output) := do
      let challenges ← sampleChallenges pSpec
      (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    let my : ((Transcript pSpec × Output) × σ) → ProbComp (Option StmtOut × Output) := fun z => do
      let verResult ← (simulateQ impl (verifier stmtIn z.1.1)).run' z.2
      return (verResult, z.1.2)
    let finalRun : ((Transcript pSpec × Output) × σ) → Prop := fun z =>
      sf.toFun pSpec.length stmtIn (PartialTranscript.ofTranscript z.1.1)
    let final0 : (Transcript pSpec × Output) → Prop := fun z =>
      sf.toFun pSpec.length stmtIn (PartialTranscript.ofTranscript z.1)
    let flip : ChallengeIndex pSpec → (Transcript pSpec × Output) → Prop := fun i z =>
      ¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec z.1) ∧
        sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec z.1)
    have hexpPair_eq_bind : expPair σ0 = mxRun >>= my := by
      unfold expPair mxRun my
      simp [StateT.run', StateT.run, bind_assoc]
    have hmx0_eq_mapfst : mx0 = Prod.fst <$> mxRun := by
      simp [mx0, mxRun, StateT.run', StateT.run, map_eq_bind_pure_comp, bind_assoc]
    have hInv_on_support : ∀ z ∈ support mxRun, Inv z.2 := by
      intro z hz
      simp only [mxRun, mem_support_bind_iff] at hz
      rcases hz with ⟨ch, hch, hz'⟩
      exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
        (oa := Prover.run pSpec prover ch) σ0 hσ0 z hz')
    have h_acc_le_finalRun :
        Pr[accept | expPair σ0] ≤ Pr[finalRun | mxRun] := by
      rw [hexpPair_eq_bind, probEvent_bind_eq_tsum]
      rw [probEvent_eq_tsum_ite (mx := mxRun) (p := finalRun)]
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : z ∈ support mxRun
      · have hInvz : Inv z.2 := hInv_on_support z hz
        by_cases hft : finalRun z
        · calc
            Pr[= z | mxRun] * Pr[accept | my z] ≤ Pr[= z | mxRun] * 1 := by
              exact mul_le_mul' le_rfl probEvent_le_one
            _ = Pr[= z | mxRun] := by simp
            _ = (if finalRun z then Pr[= z | mxRun] else 0) := by simp [hft]
        · have hopt0 :
            Pr[(fun verResult => ∃ s ∈ langOut, verResult = some s) |
              (simulateQ impl (verifier stmtIn z.1.1)).run' z.2] = 0 := by
            rw [probEvent_some_eq_optionT]
            exact sf.toFun_full stmtIn z.1.1 z.2 hInvz hft
          have hinner0 : Pr[accept | my z] = 0 := by
            unfold my accept
            simpa [probEvent_map, Function.comp] using hopt0
          simp [hft, hinner0]
      · have hz0 : Pr[= z | mxRun] = 0 := probOutput_eq_zero_of_not_mem_support hz
        by_cases hft : finalRun z <;> simp [hft, hz0]
    have h_final0_eq_finalRun : Pr[final0 | mx0] = Pr[finalRun | mxRun] := by
      rw [hmx0_eq_mapfst]
      rw [probEvent_map]
      rfl
    have h_final_false_of_noFlip :
        ∀ tr : Transcript pSpec,
          (∀ i : ChallengeIndex pSpec,
            ¬ (¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) ∧
                sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec tr))) →
          ¬ sf.toFun pSpec.length stmtIn (PartialTranscript.ofTranscript tr) := by
      intro tr hNoFlip
      have hfalse_prefix :
          ∀ k, k ≤ pSpec.length →
            ¬ sf.toFun k stmtIn (HVector.take k pSpec tr) := by
        intro k hkLe
        induction k with
        | zero =>
            simpa using _hstart
        | succ k ih =>
            have hkLt : k < pSpec.length := Nat.lt_of_succ_le hkLe
            have hkFalse : ¬ sf.toFun k stmtIn (HVector.take k pSpec tr) := ih (Nat.le_of_lt hkLt)
            by_cases hchal : (pSpec.get ⟨k, hkLt⟩).isChallenge = true
            · have hNoFlipK :
                ¬ (¬ sf.toFun k stmtIn (HVector.take k pSpec tr) ∧
                    sf.toFun (k + 1) stmtIn (HVector.take (k + 1) pSpec tr)) := by
                simpa using hNoFlip ⟨⟨k, hkLt⟩, hchal⟩
              exact fun hkSucc => hNoFlipK ⟨hkFalse, hkSucc⟩
            · have hnon : (pSpec.get ⟨k, hkLt⟩).isChallenge = false := by
                exact Bool.eq_false_iff.mpr hchal
              have hstep :=
                sf.toFun_next k hkLt hnon stmtIn (HVector.take k pSpec tr) hkFalse
                  (HVector.get pSpec tr ⟨k, hkLt⟩)
              have htake := hvector_take_succ_eq_concat (k := k) (hk := hkLt) (tr := tr)
              simpa [htake] using hstep
      have hlenFalse :
          ¬ sf.toFun pSpec.length stmtIn (HVector.take pSpec.length pSpec tr) :=
        hfalse_prefix pSpec.length le_rfl
      have hfullEq := htake_full tr
      simpa [hfullEq] using hlenFalse
    have h_final_implies_exists :
        ∀ x : Transcript pSpec × Output, final0 x → ∃ i : ChallengeIndex pSpec, flip i x := by
      intro x hxFinal
      by_contra hNone
      push_neg at hNone
      exact (h_final_false_of_noFlip x.1 hNone) hxFinal
    have h_final_le_exists :
        Pr[final0 | mx0] ≤
          Pr[(fun x => ∃ i ∈ (Finset.univ : Finset (ChallengeIndex pSpec)), flip i x) | mx0] := by
      refine probEvent_mono ?_
      intro x hx hxFinal
      rcases h_final_implies_exists x hxFinal with ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ i, hi⟩
    have h_union :
        Pr[(fun x => ∃ i ∈ (Finset.univ : Finset (ChallengeIndex pSpec)), flip i x) | mx0] ≤
          Finset.sum Finset.univ (fun i => Pr[flip i | mx0]) := by
      exact probEvent_exists_finset_le_sum
        (s := (Finset.univ : Finset (ChallengeIndex pSpec))) (mx := mx0)
        (E := fun i x => flip i x)
    have h_each : ∀ i : ChallengeIndex pSpec, Pr[flip i | mx0] ≤ rbrError i := by
      intro i
      simpa [mx0, flip] using hrbr stmtIn hstmtIn Output prover i σ0 hσ0
    have h_final0_le_sum : Pr[final0 | mx0] ≤ ε := by
      calc
        Pr[final0 | mx0]
            ≤ Pr[(fun x => ∃ i ∈ (Finset.univ : Finset (ChallengeIndex pSpec)), flip i x) | mx0] :=
              h_final_le_exists
        _ ≤ Finset.sum Finset.univ (fun i => Pr[flip i | mx0]) :=
              h_union
        _ ≤ Finset.sum Finset.univ (fun i => (rbrError i : ℝ≥0∞)) := by
              exact Finset.sum_le_sum (fun i _ => h_each i)
        _ = ε := by
              simp [ε]
    calc
      Pr[accept | expPair σ0] ≤ Pr[finalRun | mxRun] := h_acc_le_finalRun
      _ = Pr[final0 | mx0] := h_final0_eq_finalRun.symm
      _ ≤ ε := h_final0_le_sum
  have hInitBound :
      Pr[accept | do
        let σ0 ← init
        expPair σ0] ≤ ε := by
    rw [probEvent_bind_eq_tsum]
    calc
      ∑' σ0, Pr[= σ0 | init] * Pr[accept | expPair σ0]
          ≤ ∑' σ0, Pr[= σ0 | init] * ε := by
            refine ENNReal.tsum_le_tsum fun σ0 => ?_
            by_cases hσ0 : σ0 ∈ support init
            · exact mul_le_mul' le_rfl (hσbound σ0 (hInit σ0 hσ0))
            · simp [probOutput_eq_zero_of_not_mem_support hσ0]
      _ = (∑' σ0, Pr[= σ0 | init]) * ε := by
            rw [ENNReal.tsum_mul_right]
      _ ≤ 1 * ε := by
            exact mul_le_mul' tsum_probOutput_le_one le_rfl
      _ = ε := by simp
  let f : Challenges pSpec → σ → ProbComp (Option StmtOut × Output) := fun challenges σ0 => do
    let z ← (simulateQ impl (Prover.run pSpec prover challenges)).run σ0
    let verResult ← (simulateQ impl (verifier stmtIn z.1.1)).run' z.2
    return (verResult, z.1.2)
  have hswap :
      Pr[accept | do
        let challenges ← sampleChallenges pSpec
        let σ0 ← init
        f challenges σ0] =
      Pr[accept | do
        let σ0 ← init
        let challenges ← sampleChallenges pSpec
        f challenges σ0] := by
    simpa [f] using
      (probEvent_bind_bind_swap
        (mx := sampleChallenges pSpec) (my := init) (f := f) (q := accept))
  have hmain :
      Pr[accept | do
        let challenges ← sampleChallenges pSpec
        (f challenges (← init))] ≤ ε := by
    calc
      Pr[accept | do
        let challenges ← sampleChallenges pSpec
        (f challenges (← init))]
          = Pr[accept | do
              let challenges ← sampleChallenges pSpec
              let σ0 ← init
              f challenges σ0] := by
                simp
      _ = Pr[accept | do
            let σ0 ← init
            let challenges ← sampleChallenges pSpec
            f challenges σ0] := hswap
      _ = Pr[accept | do
            let σ0 ← init
            expPair σ0] := by
              simp [expPair, f, bind_assoc]
      _ ≤ ε := hInitBound
  simpa [accept, expPair, f, ε] using hmain

/-- `soundnessFromState` is `Verifier.soundness` with explicit initial state `σ0`,
assuming `Inv σ0`. -/
private def Verifier.soundnessFromState
    {StmtIn StmtOut : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (Inv : σ → Prop)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ stmtIn ∉ langIn,
  ∀ σ0 : σ,
  (Inv σ0) →
    Pr[fun (verResult, _) => ∃ s ∈ langOut, verResult = some s
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (do
          let (tr, out) ← Prover.run pSpec prover challenges
          let verResult ← (verifier stmtIn tr).run
          return (verResult, out))).run' σ0
    ] ≤ soundnessError

private theorem soundnessFromState_of_rbr
    {StmtIn StmtOut : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrSoundness impl langIn langOut verifier Inv rbrError) :
    Verifier.soundnessFromState impl Inv langIn langOut verifier
      (Finset.sum Finset.univ rbrError) := by
  intro Output prover stmtIn hstmtIn σ0 hσ0
  have hInitPure : InitSatisfiesInv (init := (pure σ0 : ProbComp σ)) Inv := by
    intro σ' hσ'
    have hEq : σ' = σ0 := by simpa [support_pure] using hσ'
    simpa [hEq] using hσ0
  have hSound :
      verifier.soundness (pure σ0) impl langIn langOut
        (Finset.sum Finset.univ rbrError) :=
    rbrSoundness_implies_soundness (init := (pure σ0 : ProbComp σ)) (impl := impl)
      (hInit := hInitPure) (hPres := hPres) (h := h)
  simpa [Verifier.soundness] using
    (hSound (Output := Output) (prover := prover) (stmtIn := stmtIn) hstmtIn)

set_option maxHeartbeats 800000 in
-- This helper performs large bind reassociations and event rewrites over `ProbComp`.
private theorem soundness_of_soundnessFromState
    {StmtIn StmtOut : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {soundnessError : ℝ≥0}
    (hInit : InitSatisfiesInv init Inv)
    (hσbound : Verifier.soundnessFromState impl Inv langIn langOut verifier soundnessError) :
    verifier.soundness init impl langIn langOut soundnessError := by
  intro Output prover stmtIn hstmtIn
  let ε : ℝ≥0∞ := (soundnessError : ℝ≥0∞)
  let accept : (Option StmtOut × Output) → Prop := fun z => ∃ s ∈ langOut, z.1 = some s
  let exp : σ → ProbComp (Option StmtOut × Output) := fun σ0 => do
    let challenges ← sampleChallenges pSpec
    (simulateQ impl (do
      let (tr, out) ← Prover.run pSpec prover challenges
      let verResult ← (verifier stmtIn tr).run
      return (verResult, out))).run' σ0
  have hσbound' : ∀ σ0, Inv σ0 → Pr[accept | exp σ0] ≤ ε := by
    intro σ0 hσ0
    simpa [ε, accept, exp, Verifier.soundnessFromState] using
      (hσbound (Output := Output) (prover := prover) (stmtIn := stmtIn) hstmtIn σ0 hσ0)
  have hInitBound :
      Pr[accept | do
        let σ0 ← init
        exp σ0] ≤ ε := by
    rw [probEvent_bind_eq_tsum]
    calc
      ∑' σ0, Pr[= σ0 | init] * Pr[accept | exp σ0]
          ≤ ∑' σ0, Pr[= σ0 | init] * ε := by
            refine ENNReal.tsum_le_tsum fun σ0 => ?_
            by_cases hσ0 : σ0 ∈ support init
            · exact mul_le_mul' le_rfl (hσbound' σ0 (hInit σ0 hσ0))
            · simp [probOutput_eq_zero_of_not_mem_support hσ0]
      _ = (∑' σ0, Pr[= σ0 | init]) * ε := by
            rw [ENNReal.tsum_mul_right]
      _ ≤ 1 * ε := by
            exact mul_le_mul' tsum_probOutput_le_one le_rfl
      _ = ε := by simp
  let f : Challenges pSpec → σ → ProbComp (Option StmtOut × Output) := fun challenges σ0 => do
    (simulateQ impl (do
      let (tr, out) ← Prover.run pSpec prover challenges
      let verResult ← (verifier stmtIn tr).run
      return (verResult, out))).run' σ0
  have hswap :
      Pr[accept | do
        let challenges ← sampleChallenges pSpec
        let σ0 ← init
        f challenges σ0] =
      Pr[accept | do
        let σ0 ← init
        let challenges ← sampleChallenges pSpec
        f challenges σ0] := by
    simpa [f] using
      (probEvent_bind_bind_swap
        (mx := sampleChallenges pSpec) (my := init) (f := f) (q := accept))
  have hmain :
      Pr[accept | do
        let challenges ← sampleChallenges pSpec
        (f challenges (← init))] ≤ ε := by
    calc
      Pr[accept | do
        let challenges ← sampleChallenges pSpec
        (f challenges (← init))]
          = Pr[accept | do
              let challenges ← sampleChallenges pSpec
              let σ0 ← init
              f challenges σ0] := by
                simp
      _ = Pr[accept | do
            let σ0 ← init
            let challenges ← sampleChallenges pSpec
            f challenges σ0] := hswap
      _ = Pr[accept | do
            let σ0 ← init
            exp σ0] := by
              simp [exp, f]
      _ ≤ ε := hInitBound
  simpa [Verifier.soundness, accept, exp, f, ε] using hmain

/-- Soundness of `n`-fold composition: if each copy has RBR soundness error `rbrError`,
the composed protocol has total soundness error at most `n * Σᵢ rbrError(i)`.

**Proof strategy** (currently `sorry`):
1. Apply `rbrSoundness_implies_soundness` to get single-step soundness `Σ rbrError`.
2. Prove identity verifier has soundness 0 (base case).
3. Prove soundness composition: `ε₁ + ε₂` bound (inductive step).
-/
theorem Verifier.soundness_compNth
    {S : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {lang : Set S}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrSoundness impl lang lang v Inv rbrError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).soundness init impl lang lang
      (n * Finset.sum Finset.univ rbrError) := by
  sorry

end Soundness

/-! ## RBR Knowledge Soundness → Knowledge Soundness -/

section KnowledgeSoundness

variable {StmtIn WitIn StmtOut WitOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- RBR knowledge soundness implies overall knowledge soundness. The total knowledge
error is bounded by the sum of per-round RBR knowledge errors.

**Proof strategy** (currently `sorry`): analogous to `rbrSoundness_implies_soundness`
with the knowledge state function in place of the state function. The extractor is
composed round-by-round. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv relIn relOut verifier extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) :
    verifier.knowledgeSoundness init impl relIn relOut
      (Finset.sum Finset.univ rbrKnowledgeError) := by
  sorry

/-- Knowledge soundness of `n`-fold composition: if each copy has RBR knowledge
soundness error `rbrKnowledgeError`, the composed protocol has total knowledge
soundness error at most `n * Σᵢ rbrKnowledgeError(i)`.

**Proof strategy** (currently `sorry`): analogous to `Verifier.soundness_compNth`. -/
theorem Verifier.knowledgeSoundness_compNth
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound S W W pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv rel rel v extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).knowledgeSoundness init impl rel rel
      (n * Finset.sum Finset.univ rbrKnowledgeError) := by
  sorry

end KnowledgeSoundness

end ProtocolSpec
