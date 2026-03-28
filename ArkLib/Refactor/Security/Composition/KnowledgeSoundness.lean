/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Composition.Util
import ArkLib.Refactor.Security.Composition.Soundness

/-!
# Knowledge Soundness Composition

Theorems about how (RBR) knowledge soundness composes.

## Main results

- `rbrKnowledgeSoundness_implies_knowledgeSoundness` — RBR k.s. implies overall k.s.
- `Verifier.knowledgeSoundness_compNth` — knowledge soundness of n-fold composition
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal BigOperators

@[simp] lemma StateT.run'_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {σ α β : Type} (f : α → β) (x : StateT σ m α) (s : σ) :
    (f <$> x).run' s = f <$> x.run' s := by
  change (fun x : β × σ => x.1) <$> (f <$> x).run s =
      f <$> ((fun x : α × σ => x.1) <$> x.run s)
  rw [StateT.run_map]
  simp [Functor.map_map]

namespace ProtocolSpec

section KnowledgeSoundness

variable {StmtIn WitIn StmtOut WitOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

private theorem knowledgeSoundness_of_soundness_choose
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {ε : ℝ≥0}
    (hSound :
      verifier.soundness init impl
        {s | ∃ w, (s, w) ∈ relIn}
        {s | ∃ w, (s, w) ∈ relOut} ε) :
    verifier.knowledgeSoundness init impl relIn relOut ε := by
  classical
  let slExtractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
    fun stmtIn _ _ =>
      OptionT.mk <| pure <|
        if hRel : ∃ w : WitIn, (stmtIn, w) ∈ relIn then
          some (Classical.choose hRel)
        else
          none
  refine ⟨slExtractor, ?_⟩
  intro stmtIn prover
  let extResult : Option WitIn :=
    if hRel : ∃ w : WitIn, (stmtIn, w) ∈ relIn then some (Classical.choose hRel) else none
  let baseComp : ProbComp (Option StmtOut × WitOut) := do
    let challenges ← sampleChallenges pSpec
    (simulateQ impl (do
      let (tr, witOut) ← Prover.run pSpec prover challenges
      let verResult ← (verifier stmtIn tr).run
      return (verResult, witOut))).run' (← init)
  have hOcEq : ∀ challenges,
      (do
        let (tr, witOut) ← Prover.run pSpec prover challenges
        let verResult ← (verifier stmtIn tr).run
        let extractedWit ← (slExtractor stmtIn witOut tr).run
        return (verResult, witOut, extractedWit)
        : OracleComp oSpec _) =
      (fun z => (z.1, z.2, extResult)) <$> (do
        let (tr, witOut) ← Prover.run pSpec prover challenges
        let verResult ← (verifier stmtIn tr).run
        return (verResult, witOut)) := by
    intro challenges
    simp only [slExtractor, extResult]
    dsimp only [OptionT.run, OptionT.mk]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  by_cases hStmtIn : ∃ w : WitIn, (stmtIn, w) ∈ relIn
  · have hChoose : (stmtIn, Classical.choose hStmtIn) ∈ relIn :=
      Classical.choose_spec hStmtIn
    suffices hzero : Pr[fun (verResult, witOut, extractedWit) =>
        (∃ stmtOut, verResult = some stmtOut ∧ (stmtOut, witOut) ∈ relOut) ∧
          (extractedWit.isNone ∨ ∃ w, extractedWit = some w ∧ (stmtIn, w) ∉ relIn)
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (do
          let (tr, witOut) ← Prover.run pSpec prover challenges
          let verResult ← (verifier stmtIn tr).run
          let extractedWit ← (slExtractor stmtIn witOut tr).run
          return (verResult, witOut, extractedWit))).run' (← init)] = 0 by
      exact le_of_eq hzero |>.trans (by positivity)
    rw [probEvent_eq_zero_iff]
    intro z hz ⟨_, hBad⟩
    have hExtVal : z.2.2 = some (Classical.choose hStmtIn) := by
      rw [mem_support_bind_iff] at hz
      obtain ⟨ch, _, hz₁⟩ := hz
      rw [mem_support_bind_iff] at hz₁
      obtain ⟨σ0, _, hz₂⟩ := hz₁
      rw [hOcEq, simulateQ_map, StateT.run'_map] at hz₂
      simp only [support_map, Set.mem_image] at hz₂
      obtain ⟨a, _, rfl⟩ := hz₂
      simp [extResult, hStmtIn]
    rcases hBad with hnone | ⟨w, hw, hnotRel⟩
    · simp [hExtVal] at hnone
    · have : w = Classical.choose hStmtIn :=
        (Option.some.inj (hExtVal.symm.trans hw)).symm
      subst this
      exact hnotRel hChoose
  · have hstmtIn_not_lang : stmtIn ∉ {s | ∃ w, (s, w) ∈ relIn} := by
      simpa using hStmtIn
    have hExtNone : extResult = none := dif_neg hStmtIn
    have hSoundBound := hSound WitOut prover stmtIn hstmtIn_not_lang
    have hInnerEq : ∀ ch σ0,
        (simulateQ impl (do
          let (tr, witOut) ← Prover.run pSpec prover ch
          let verResult ← (verifier stmtIn tr).run
          let extractedWit ← (slExtractor stmtIn witOut tr).run
          return (verResult, witOut, extractedWit))).run' σ0 =
        (fun z : Option StmtOut × WitOut => (z.1, z.2, extResult)) <$>
          (simulateQ impl (do
            let (tr, witOut) ← Prover.run pSpec prover ch
            let verResult ← (verifier stmtIn tr).run
            return (verResult, witOut))).run' σ0 := by
      intro ch σ0
      rw [hOcEq, simulateQ_map, StateT.run'_map]
    have map_bind_eq : ∀ {α β γ : Type _} (mx : ProbComp α) (g : α → ProbComp β) (f : β → γ),
        (mx >>= fun a => f <$> g a) = f <$> (mx >>= g) := by
      intro α β γ mx g f
      simp only [map_eq_bind_pure_comp, bind_assoc]
    have hCompEq :
        (do
          let ch ← sampleChallenges pSpec
          (simulateQ impl (do
            let (tr, witOut) ← Prover.run pSpec prover ch
            let verResult ← (verifier stmtIn tr).run
            let extractedWit ← (slExtractor stmtIn witOut tr).run
            return (verResult, witOut, extractedWit))).run' (← init)) =
        (fun z : Option StmtOut × WitOut => (z.1, z.2, extResult)) <$> baseComp := by
      simp_rw [hInnerEq, map_bind_eq]
      rfl
    rw [hCompEq, probEvent_map]
    refine le_trans (probEvent_mono ?_) hSoundBound
    intro z _ hBad
    simp only [Function.comp, hExtNone, Option.isNone_none, true_or, and_true] at hBad
    rcases hBad with ⟨stmtOut, hEq, hRelOut⟩
    exact ⟨stmtOut, ⟨z.2, hRelOut⟩, hEq⟩

/-- RBR knowledge soundness implies overall knowledge soundness. The total knowledge
error is bounded by the sum of per-round RBR knowledge errors. -/
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
  let hRbrSound :
      rbrSoundness impl
        {s | ∃ w, (s, w) ∈ relIn}
        {s | ∃ w, (s, w) ∈ relOut}
        verifier Inv rbrKnowledgeError :=
    rbrKnowledgeSoundness_implies_rbrSoundness (impl := impl) h
  have hSound :
      verifier.soundness init impl
        {s | ∃ w, (s, w) ∈ relIn}
        {s | ∃ w, (s, w) ∈ relOut}
        (Finset.sum Finset.univ rbrKnowledgeError) :=
    rbrSoundness_implies_soundness (init := init) (impl := impl) hInit hPres hRbrSound
  exact knowledgeSoundness_of_soundness_choose (init := init) (impl := impl) hSound

/-- Knowledge soundness of `n`-fold composition: if each copy has RBR knowledge
soundness error `rbrKnowledgeError`, the composed protocol has total knowledge
soundness error at most `n * Σᵢ rbrKnowledgeError(i)`. -/
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
    (hOut : Verifier.OutputIndependent impl Inv v)
    (hState : Verifier.StatePreserving impl v)
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).knowledgeSoundness init impl rel rel
      (n * Finset.sum Finset.univ rbrKnowledgeError) := by
  letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
  let lang : Set S := {s | ∃ w, (s, w) ∈ rel}
  have hRbrSound : rbrSoundness impl lang lang v Inv rbrKnowledgeError :=
    rbrKnowledgeSoundness_implies_rbrSoundness (impl := impl) h
  have hSound :
      letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
      (v.compNth n).soundness init impl lang lang
        (n * Finset.sum Finset.univ rbrKnowledgeError) :=
    Verifier.soundness_compNth init impl hOut hState hInit hPres hRbrSound n
  exact knowledgeSoundness_of_soundness_choose (init := init) (impl := impl) hSound

theorem Verifier.knowledgeSoundness_compNth_of_rbrKnowledgeSoundness
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound S W W pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv rel rel v extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (hOut : Verifier.OutputIndependent impl Inv v)
    (hState : Verifier.StatePreserving impl v)
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).knowledgeSoundness init impl rel rel
      (n * Finset.sum Finset.univ rbrKnowledgeError) := by
  exact Verifier.knowledgeSoundness_compNth
    (init := init) (impl := impl) hOut hState hInit hPres h n

end KnowledgeSoundness

end ProtocolSpec
