/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Composition.Util

/-!
# Soundness Composition

Theorems about how (RBR) soundness composes.

## Main results

- `rbrSoundness_implies_soundness` — RBR soundness implies overall soundness
- `Verifier.soundness_compNth` — soundness of `n`-fold composition
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal BigOperators

namespace ProtocolSpec

/-! ## RBR Soundness → Soundness -/

section Soundness

variable {StmtIn StmtOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

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

/-- Composition step for `soundnessFromState`: if stage 1 and stage 2 are sound from any
invariant-satisfying state, then their verifier composition is sound from state with additive
error. -/
private theorem Verifier.soundnessFromState_id
    {S : Type}
    {lang : Set S}
    {Inv : σ → Prop} :
    Verifier.soundnessFromState (pSpec := ([] : ProtocolSpec)) impl Inv lang lang
      ((fun stmt _ => (pure stmt : OptionT (OracleComp oSpec) S)) :
        Verifier (OracleComp oSpec) S S []) 0 := by
  intro Output prover stmtIn hstmtIn σ0 _hσ0
  have hinner : (do
      let (tr, out) ← Prover.run (m := OracleComp oSpec)
        ([] : ProtocolSpec) prover (HVector.nil : Challenges [])
      let verResult ←
        ((fun stmt (_ : Transcript []) =>
          (pure stmt : OptionT (OracleComp oSpec) S)) stmtIn tr).run
      return (verResult, out)) =
    (pure (some stmtIn, prover) : OracleComp oSpec _) := by
    simp only [Prover.run, pure_bind]
    change (do
      let verResult ← (pure (some stmtIn) : OracleComp oSpec (Option S))
      pure (verResult, prover)) = _
    simp only [pure_bind]
  simp only [sampleChallenges, ChallengesSampleable.sampleChallenges,
    pure_bind, hinner, simulateQ_pure]
  unfold StateT.run'
  simp only [Functor.map, ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  intro x hx
  subst hx
  exact fun ⟨s, hs, heq⟩ =>
    hstmtIn (show stmtIn ∈ lang by rwa [Option.some.inj heq])

set_option maxHeartbeats 4000000 in
-- Large bind reassociations and event rewrites over `ProbComp`.
private theorem Verifier.soundnessFromState_comp
    {S : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂]
    {lang : Set S}
    {v₁ : Verifier (OracleComp oSpec) S S pSpec₁}
    {v₂ : Verifier (OracleComp oSpec) S S pSpec₂}
    {Inv : σ → Prop}
    {ε₁ ε₂ : ℝ≥0}
    (hOut₁ : Verifier.OutputIndependent impl Inv v₁)
    (hState₁ : Verifier.StatePreserving impl v₁)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h₁ : Verifier.soundnessFromState impl Inv lang lang v₁ ε₁)
    (h₂ : Verifier.soundnessFromState impl Inv lang lang v₂ ε₂) :
    letI := ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    Verifier.soundnessFromState impl Inv lang lang (Verifier.comp v₁ v₂) (ε₁ + ε₂) := by
  classical
  intro Output prover stmtIn hstmtIn σ0 hσ0
  letI : ChallengesSampleable (pSpec₁ ++ pSpec₂) :=
    ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
  let accept : Option S → Prop := fun o => ∃ s ∈ lang, o = some s
  let p₁ := Prover.splitPrefix (m := OracleComp oSpec) (Output := Output) pSpec₁ prover
  let stage₁Run (ch₁ : Challenges pSpec₁) :=
    simulateQ impl (Prover.run (m := OracleComp oSpec)
      (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ ch₁)
  let stage₂Run (p₂ : Prover (OracleComp oSpec) Output pSpec₂) (ch₂ : Challenges pSpec₂) :=
    simulateQ impl (Prover.run (m := OracleComp oSpec) (Output := Output) pSpec₂ p₂ ch₂)
  let v₁Run (tr₁ : Transcript pSpec₁) := simulateQ impl ((v₁ stmtIn tr₁).run)
  let v₂Run (mid : S) (tr₂ : Transcript pSpec₂) := simulateQ impl ((v₂ mid tr₂).run)
  -- The swapped experiment: run stage 1 → evaluate v₁ → run stage 2 → evaluate v₂
  let expSwap : ProbComp (Option S) := do
    let ch₁ ← sampleChallenges pSpec₁
    let z₁ ← (stage₁Run ch₁).run σ0
    let mid ← (v₁Run z₁.1.1).run' z₁.2
    let ch₂ ← sampleChallenges pSpec₂
    let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
    match mid with
    | none => pure none
    | some s => (v₂Run s z₂.1.1).run' z₂.2
  -- Step 1: Show the goal probability equals Pr[accept | expSwap]
  suffices hBound : Pr[accept | expSwap] ≤ (ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞) by
    -- Transfer from the original computation to expSwap
    suffices hEq :
        Pr[fun (verResult, _) => ∃ s ∈ lang, verResult = some s | do
          let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
          (simulateQ impl (do
            let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
              (pSpec₁ ++ pSpec₂) prover challenges
            let verResult ← (Verifier.comp v₁ v₂ stmtIn tr).run
            return (verResult, out))).run' σ0] =
        Pr[accept | expSwap] by
      rw [hEq]; exact_mod_cast hBound
    have hsample : sampleChallenges (pSpec₁ ++ pSpec₂) = do
        let ch₁ ← sampleChallenges pSpec₁
        let ch₂ ← sampleChallenges pSpec₂
        return Challenges.join pSpec₁ pSpec₂ ch₁ ch₂ := rfl
    have probEvent_bind_of_evalDist_eq :
        ∀ {α β : Type} (mx my : ProbComp α) (g : α → ProbComp β) (q : β → Prop),
          evalDist mx = evalDist my →
            Pr[q | mx >>= g] = Pr[q | my >>= g] := by
      intro α β mx my g q hdist
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      have hprob : ∀ x : α, Pr[= x | mx] = Pr[= x | my] := (evalDist_ext_iff.mp hdist)
      exact tsum_congr (fun x => by rw [hprob x])
    have hVerCompState :
        ∀ tr₁ tr₂ (σs : σ),
          Pr[accept | (simulateQ impl
            ((Verifier.comp v₁ v₂ stmtIn (Transcript.join tr₁ tr₂)).run)).run' σs] =
          Pr[accept | do
            let mid ← (v₁Run tr₁).run' σs
            match mid with
            | none => pure none
            | some s => (v₂Run s tr₂).run' σs] := by
      intro tr₁ tr₂ σs
      let mxv : StateT σ ProbComp (Option S) := v₁Run tr₁
      let A : (Option S × σ) → ProbComp (Option S) := fun us =>
        match us.1 with
        | none => pure none
        | some s => (fun x => x.1) <$> (v₂Run s tr₂).run us.2
      let B : (Option S × σ) → ProbComp (Option S) := fun us =>
        match us.1 with
        | none => pure none
        | some s => (fun x => x.1) <$> (v₂Run s tr₂).run σs
      have hLeftProb :
          Pr[accept | (simulateQ impl
            ((Verifier.comp v₁ v₂ stmtIn (Transcript.join tr₁ tr₂)).run)).run' σs] =
          Pr[accept | mxv.run σs >>= A] := by
        let leftPair : ProbComp (Option S × σ) :=
          (simulateQ impl
            ((Verifier.comp v₁ v₂ stmtIn (Transcript.join tr₁ tr₂)).run)) σs
        let pairStep : ProbComp (Option S × σ) := do
          let us ← mxv.run σs
          match us.1 with
          | none => pure (none, us.2)
          | some s => (v₂Run s tr₂).run us.2
        have hCompEq : leftPair = pairStep := by
          unfold leftPair pairStep mxv v₁Run v₂Run
          simp only [Verifier.comp, Transcript.split_join, OptionT.run_bind, Option.elimM,
            simulateQ_bind]
          change ((simulateQ impl (v₁ stmtIn tr₁).run >>= fun x =>
              simulateQ impl (x.elim (pure none) fun x => (v₂ x tr₂).run)).run σs) =
            (do
              let us ← (simulateQ impl (v₁ stmtIn tr₁).run).run σs
              match us.1 with
              | none => pure (none, us.2)
              | some s => (simulateQ impl (v₂ s tr₂).run).run us.2)
          rw [StateT.run_bind]
          apply bind_congr
          intro us
          cases hmid : us.1 <;> simp [Option.elim]
        calc
          Pr[accept | (simulateQ impl
              ((Verifier.comp v₁ v₂ stmtIn (Transcript.join tr₁ tr₂)).run)).run' σs]
              = Pr[accept | Prod.fst <$> leftPair] := by
                  simp [leftPair, StateT.run']
          _ = Pr[accept ∘ Prod.fst | leftPair] := by
                simp
          _ = Pr[accept ∘ Prod.fst | pairStep] := by rw [hCompEq]
          _ = Pr[accept | Prod.fst <$> pairStep] := by
                simp
          _ = Pr[accept | mxv.run σs >>= fun us =>
                match us.1 with
                | none => pure none
                | some s => (v₂Run s tr₂).run us.2 >>= pure ∘ fun x => x.1] := by
                have hEqComp :
                    Prod.fst <$> pairStep =
                    (do
                      let us ← mxv.run σs
                      match us.1 with
                      | none => pure none
                      | some s => (v₂Run s tr₂).run us.2 >>= pure ∘ fun x => x.1) := by
                  unfold pairStep
                  simp only [map_eq_bind_pure_comp, bind_assoc]
                  apply bind_congr
                  intro us
                  cases hmid : us.1 <;> simp
                rw [hEqComp]
          _ = Pr[accept | mxv.run σs >>= A] := by
                rfl
      have hAB :
          Pr[accept | mxv.run σs >>= A] = Pr[accept | mxv.run σs >>= B] := by
        refine probEvent_bind_congr ?_
        intro us hus
        have husσ : us.2 = σs := (hState₁ stmtIn tr₁) σs us hus
        cases hmid : us.1 <;> simp [A, B, hmid, husσ]
      have hRightProb :
          Pr[accept | mxv.run σs >>= B] =
          Pr[accept | do
            let mid ← (v₁Run tr₁).run' σs
            match mid with
            | none => pure none
            | some s => (v₂Run s tr₂).run' σs] := by
        simp [mxv, B, v₁Run, v₂Run, StateT.run', StateT.run, bind_assoc, map_eq_bind_pure_comp]
      exact hLeftProb.trans (hAB.trans hRightProb)
    let pairComp : ProbComp (Option S × Output) := do
      let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
      (simulateQ impl (do
        let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
          (pSpec₁ ++ pSpec₂) prover challenges
        let verResult ← (Verifier.comp v₁ v₂ stmtIn tr).run
        return (verResult, out))).run' σ0
    change Pr[fun (verResult, _) => ∃ s ∈ lang, verResult = some s | pairComp] =
      Pr[accept | expSwap]
    calc
      Pr[fun (verResult, _) => ∃ s ∈ lang, verResult = some s | pairComp]
          = Pr[accept | Prod.fst <$> pairComp] := by
              change Pr[accept ∘ Prod.fst | pairComp] = Pr[accept | Prod.fst <$> pairComp]
              simpa [pairComp] using
                (probEvent_map (q := accept) (f := Prod.fst) (mx := pairComp)).symm
      _ = Pr[accept | do
            let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
            (simulateQ impl (do
              let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
                (pSpec₁ ++ pSpec₂) prover challenges
              let verResult ← (Verifier.comp v₁ v₂ stmtIn tr).run
              return verResult)).run' σ0] := by
            simp [pairComp, map_eq_bind_pure_comp, bind_assoc]
      _ = Pr[accept | do
            let ch₁ ← sampleChallenges pSpec₁
            let ch₂ ← sampleChallenges pSpec₂
            let z₁ ← (stage₁Run ch₁).run σ0
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            (simulateQ impl
              ((Verifier.comp v₁ v₂ stmtIn (Transcript.join z₁.1.1 z₂.1.1)).run)).run' z₂.2] := by
            simp [hsample, stage₁Run, stage₂Run, p₁, Prover.run_splitPrefix_join,
              simulateQ_bind, bind_assoc]
      _ = Pr[accept | do
            let ch₁ ← sampleChallenges pSpec₁
            let z₁ ← (stage₁Run ch₁).run σ0
            let ch₂ ← sampleChallenges pSpec₂
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            (simulateQ impl
              ((Verifier.comp v₁ v₂ stmtIn (Transcript.join z₁.1.1 z₂.1.1)).run)).run' z₂.2] := by
            refine probEvent_bind_congr ?_
            intro ch₁ _
            simpa [bind_assoc] using
              (probEvent_bind_bind_swap
                (mx := sampleChallenges pSpec₂)
                (my := (stage₁Run ch₁).run σ0)
                (f := fun ch₂ z₁ => do
                  let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
                  (simulateQ impl
                    ((Verifier.comp v₁ v₂ stmtIn (Transcript.join z₁.1.1 z₂.1.1)).run)).run' z₂.2)
                (q := accept))
      _ = Pr[accept | do
            let ch₁ ← sampleChallenges pSpec₁
            let z₁ ← (stage₁Run ch₁).run σ0
            let mid ← (v₁Run z₁.1.1).run' z₁.2
            let ch₂ ← sampleChallenges pSpec₂
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            match mid with
            | none => pure none
            | some s => (v₂Run s z₂.1.1).run' z₂.2] := by
            refine probEvent_bind_congr ?_
            intro ch₁ _
            refine probEvent_bind_congr ?_
            intro z₁ hz₁
            have hInvz₁ : Inv z₁.2 := by
              exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
                (oa := Prover.run pSpec₁ p₁ ch₁) σ0 hσ0 _ hz₁)
            let mx₂ : ProbComp ((Transcript pSpec₂ × Output) × σ) := do
              let ch₂ ← sampleChallenges pSpec₂
              (stage₂Run z₁.1.2 ch₂).run z₁.2
            let midComp : ProbComp (Option S) := (v₁Run z₁.1.1).run' z₁.2
            have hMidInside :
                Pr[accept | mx₂ >>= fun z₂ =>
                  (simulateQ impl
                    ((Verifier.comp v₁ v₂ stmtIn (Transcript.join z₁.1.1 z₂.1.1)).run)).run' z₂.2] =
                Pr[accept | mx₂ >>= fun z₂ =>
                  do
                    let mid ← (v₁Run z₁.1.1).run' z₁.2
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2] := by
              refine probEvent_bind_congr ?_
              intro z₂ hz₂
              have hInvz₂ : Inv z₂.2 := by
                simp only [mx₂, mem_support_bind_iff] at hz₂
                rcases hz₂ with ⟨ch₂, _, hz₂'⟩
                exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
                  (oa := Prover.run pSpec₂ z₁.1.2 ch₂) z₁.2 hInvz₁ _ hz₂')
              have hCompAtZ₂ :=
                hVerCompState z₁.1.1 z₂.1.1 z₂.2
              have hMidDist :
                  evalDist ((v₁Run z₁.1.1).run' z₂.2) =
                    evalDist ((v₁Run z₁.1.1).run' z₁.2) :=
                hOut₁ stmtIn z₁.1.1 z₂.2 z₁.2 hInvz₂ hInvz₁
              have hMidSwap :
                  Pr[accept | do
                    let mid ← (v₁Run z₁.1.1).run' z₂.2
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2] =
                  Pr[accept | do
                    let mid ← (v₁Run z₁.1.1).run' z₁.2
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2] := by
                exact probEvent_bind_of_evalDist_eq
                  ((v₁Run z₁.1.1).run' z₂.2)
                  ((v₁Run z₁.1.1).run' z₁.2)
                  (fun mid =>
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2)
                  accept
                  hMidDist
              exact hCompAtZ₂.trans hMidSwap
            have hSwapMid :
                Pr[accept | mx₂ >>= fun z₂ =>
                  do
                    let mid ← midComp
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2] =
                Pr[accept | midComp >>= fun mid =>
                  mx₂ >>= fun z₂ =>
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2] := by
              simpa [midComp] using
                (probEvent_bind_bind_swap
                  (mx := mx₂)
                  (my := midComp)
                  (f := fun z₂ mid =>
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2)
                  (q := accept))
            calc
              Pr[accept | do
                  let ch₂ ← sampleChallenges pSpec₂
                  let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
                  (simulateQ impl
                    ((Verifier.comp v₁ v₂ stmtIn (Transcript.join z₁.1.1 z₂.1.1)).run)).run' z₂.2]
                  = Pr[accept | mx₂ >>= fun z₂ =>
                      (simulateQ impl
                        ((Verifier.comp v₁ v₂ stmtIn (Transcript.join z₁.1.1 z₂.1.1)).run)).run'
                          z₂.2] := by
                      simp [mx₂, bind_assoc]
              _ = Pr[accept | mx₂ >>= fun z₂ =>
                    do
                      let mid ← (v₁Run z₁.1.1).run' z₁.2
                      match mid with
                      | none => pure none
                      | some s => (v₂Run s z₂.1.1).run' z₂.2] := hMidInside
              _ = Pr[accept | midComp >>= fun mid =>
                    mx₂ >>= fun z₂ =>
                      match mid with
                      | none => pure none
                      | some s => (v₂Run s z₂.1.1).run' z₂.2] := hSwapMid
              _ = Pr[accept | do
                    let mid ← (v₁Run z₁.1.1).run' z₁.2
                    let ch₂ ← sampleChallenges pSpec₂
                    let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
                    match mid with
                    | none => pure none
                    | some s => (v₂Run s z₂.1.1).run' z₂.2] := by
                      simp [mx₂, midComp, bind_assoc]
      _ = Pr[accept | expSwap] := by
            simp [expSwap]
  -- Step 2: Factor expSwap as mx >>= my for the union bound
  let mx : ProbComp
      ((Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ) := do
    let ch₁ ← sampleChallenges pSpec₁
    let z₁ ← (stage₁Run ch₁).run σ0
    let mid ← (v₁Run z₁.1.1).run' z₁.2
    return (z₁.1.2, mid, z₁.2)
  let my (z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ) :
      ProbComp (Option S) := do
    let ch₂ ← sampleChallenges pSpec₂
    let z₂ ← (stage₂Run z.1 ch₂).run z.2.2
    match z.2.1 with
    | none => pure none
    | some s => (v₂Run s z₂.1.1).run' z₂.2
  have hFactor : expSwap = mx >>= my := by
    simp [expSwap, mx, my, bind_assoc]
  -- Step 3: Bound Pr[¬p | mx] ≤ ε₁ (stage 1 soundness)
  let p := fun (z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ) =>
    z.2.1 = none ∨ ∃ s, z.2.1 = some s ∧ s ∉ lang
  have hBad₁ : Pr[fun z => ¬ p z | mx] ≤ (ε₁ : ℝ≥0∞) := by
    have h₁Bound :
        Pr[fun (verResult, _) => ∃ s ∈ lang, verResult = some s | do
          let challenges ← sampleChallenges pSpec₁
          (simulateQ impl (do
            let (tr, out) ← Prover.run (m := OracleComp oSpec)
              (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ challenges
            let verResult ← (v₁ stmtIn tr).run
            return (verResult, out))).run' σ0] ≤ (ε₁ : ℝ≥0∞) := by
      simpa [Verifier.soundnessFromState] using
        (h₁ (Output := Prover (OracleComp oSpec) Output pSpec₂)
          (prover := p₁) (stmtIn := stmtIn) hstmtIn σ0 hσ0)
    have hPred :
        (fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ => ¬ p z) =
          (fun z => ∃ s ∈ lang, z.2.1 = some s) := by
      funext z
      cases hmid : z.2.1 <;> simp [p, hmid]
    have hmxMap :
        (fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
          (z.2.1, z.1)) <$> mx =
        (do
          let ch₁ ← sampleChallenges pSpec₁
          let z₁ ← (stage₁Run ch₁).run σ0
          let mid ← (v₁Run z₁.1.1).run' z₁.2
          return (mid, z₁.1.2)) := by
      simp [mx]
    have hmxEq :
        (do
          let ch₁ ← sampleChallenges pSpec₁
          let z₁ ← (stage₁Run ch₁).run σ0
          let mid ← (v₁Run z₁.1.1).run' z₁.2
          return (mid, z₁.1.2)) =
        (do
          let challenges ← sampleChallenges pSpec₁
          (simulateQ impl (do
            let (tr, out) ← Prover.run (m := OracleComp oSpec)
              (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ challenges
            let verResult ← (v₁ stmtIn tr).run
            return (verResult, out))).run' σ0) := by
      simp [stage₁Run, v₁Run, p₁, simulateQ_bind]
    calc
      Pr[fun z => ¬ p z | mx]
          = Pr[(fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
              ∃ s ∈ lang, z.2.1 = some s) | mx] := by
              simp [hPred]
      _ = Pr[(fun z : Option S × Prover (OracleComp oSpec) Output pSpec₂ =>
            ∃ s ∈ lang, z.1 = some s) |
            (fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
              (z.2.1, z.1)) <$> mx] := by
              change Pr[(fun z : Option S × Prover (OracleComp oSpec) Output pSpec₂ =>
                ∃ s ∈ lang, z.1 = some s) ∘
                  (fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
                    (z.2.1, z.1)) | mx] =
                Pr[(fun z : Option S × Prover (OracleComp oSpec) Output pSpec₂ =>
                  ∃ s ∈ lang, z.1 = some s) |
                  (fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
                    (z.2.1, z.1)) <$> mx]
              simp
      _ = Pr[(fun z : Option S × Prover (OracleComp oSpec) Output pSpec₂ =>
            ∃ s ∈ lang, z.1 = some s) |
            (do
              let ch₁ ← sampleChallenges pSpec₁
              let z₁ ← (stage₁Run ch₁).run σ0
              let mid ← (v₁Run z₁.1.1).run' z₁.2
              return (mid, z₁.1.2))] := by
              simp [hmxMap]
      _ = Pr[fun (verResult, _) => ∃ s ∈ lang, verResult = some s | do
            let challenges ← sampleChallenges pSpec₁
            (simulateQ impl (do
              let (tr, out) ← Prover.run (m := OracleComp oSpec)
                (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ challenges
              let verResult ← (v₁ stmtIn tr).run
              return (verResult, out))).run' σ0] := by
              rw [hmxEq]
      _ ≤ (ε₁ : ℝ≥0∞) := h₁Bound
  -- Step 4: Bound Pr[accept | my z] ≤ ε₂ when p z holds
  have hBad₂ : ∀ z ∈ support mx, p z →
      Pr[fun o => ¬ (¬ accept o) | my z] ≤ (ε₂ : ℝ≥0∞) := by
    intro z hz hp
    rcases hp with hnone | ⟨s, hs, hsNotLang⟩
    · have hmyNone :
          my z = (do
            let ch₂ ← sampleChallenges pSpec₂
            let _ ← (stage₂Run z.1 ch₂).run z.2.2
            pure none) := by
          simp [my, hnone]
      rw [hmyNone]
      have : Pr[fun o : Option S => ¬ (¬ accept o) | do
        let ch₂ ← sampleChallenges pSpec₂
        let _ ← (stage₂Run z.1 ch₂).run z.2.2
        pure none] = 0 := by
        rw [probEvent_eq_zero_iff]
        intro x hx hxAcc
        simp only [mem_support_bind_iff] at hx
        rcases hx with ⟨ch₂, _, hx₁⟩
        rcases hx₁ with ⟨u, _, hx₂⟩
        have hxEq : x = none := by
          simpa [support_pure] using hx₂
        subst hxEq
        simp [accept] at hxAcc
      rw [this]
      simp
    · have hInvz : Inv z.2.2 := by
        simp only [mx, mem_support_bind_iff] at hz
        rcases hz with ⟨ch₁, _, hz₁⟩
        rcases hz₁ with ⟨z₁, hz₁, mid, _, hz₃⟩
        have hzEq : z = (z₁.1.2, mid, z₁.2) := by
          simpa [support_pure] using hz₃
        subst hzEq
        exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
          (oa := Prover.run pSpec₁ p₁ ch₁) σ0 hσ0 _ hz₁)
      have h₂Bound :
          Pr[fun (verResult, _) => ∃ s' ∈ lang, verResult = some s' | do
            let challenges ← sampleChallenges pSpec₂
            (simulateQ impl (do
              let (tr, out) ← Prover.run (m := OracleComp oSpec)
                (Output := Output) pSpec₂ z.1 challenges
              let verResult ← (v₂ s tr).run
              return (verResult, out))).run' z.2.2] ≤ (ε₂ : ℝ≥0∞) := by
        simpa [Verifier.soundnessFromState] using
          (h₂ (Output := Output) (prover := z.1) (stmtIn := s) hsNotLang z.2.2 hInvz)
      have hmySome :
          my z = (do
            let ch₂ ← sampleChallenges pSpec₂
            let z₂ ← (stage₂Run z.1 ch₂).run z.2.2
            (v₂Run s z₂.1.1).run' z₂.2) := by
        simp [my, hs]
      rw [hmySome]
      let pairStage₂ : ProbComp (Option S × Output) := do
        let challenges ← sampleChallenges pSpec₂
        (simulateQ impl (do
          let (tr, out) ← Prover.run (m := OracleComp oSpec)
            (Output := Output) pSpec₂ z.1 challenges
          let verResult ← (v₂ s tr).run
          return (verResult, out))).run' z.2.2
      have h₂BoundMap : Pr[accept | Prod.fst <$> pairStage₂] ≤ (ε₂ : ℝ≥0∞) := by
        have hPairEq :
            Pr[accept | Prod.fst <$> pairStage₂] =
            Pr[fun (verResult, _) => ∃ s' ∈ lang, verResult = some s' | pairStage₂] := by
          change Pr[accept | Prod.fst <$> pairStage₂] = Pr[accept ∘ Prod.fst | pairStage₂]
          simp
        exact hPairEq.trans_le h₂Bound
      have h₂BoundMid :
          Pr[accept | do
            let challenges ← sampleChallenges pSpec₂
            (simulateQ impl (do
              let (tr, out) ← Prover.run (m := OracleComp oSpec)
                (Output := Output) pSpec₂ z.1 challenges
              let verResult ← (v₂ s tr).run
              return verResult)).run' z.2.2] ≤ (ε₂ : ℝ≥0∞) := by
        have hMapComp :
            Prod.fst <$> pairStage₂ =
            (do
              let challenges ← sampleChallenges pSpec₂
              (simulateQ impl (do
                let (tr, out) ← Prover.run (m := OracleComp oSpec)
                  (Output := Output) pSpec₂ z.1 challenges
                let verResult ← (v₂ s tr).run
                return verResult)).run' z.2.2) := by
          simp [pairStage₂, map_eq_bind_pure_comp, bind_assoc]
        rw [← hMapComp]
        exact h₂BoundMap
      have hTarget :
          Pr[accept | do
            let ch₂ ← sampleChallenges pSpec₂
            let z₂ ← (stage₂Run z.1 ch₂).run z.2.2
            (v₂Run s z₂.1.1).run' z₂.2] ≤ (ε₂ : ℝ≥0∞) := by
        simpa [stage₂Run, v₂Run, simulateQ_bind, bind_assoc] using h₂BoundMid
      simpa [accept] using hTarget
  -- Step 5: Apply the union bound
  rw [hFactor]
  have h := probEvent_bind_le_add (mx := mx) (my := my) (p := p)
    (q := fun o => ¬ accept o) hBad₁ hBad₂
  simpa [accept] using h

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
    (hOut : Verifier.OutputIndependent impl Inv v)
    (hState : Verifier.StatePreserving impl v)
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrSoundness impl lang lang v Inv rbrError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).soundness init impl lang lang
      (n * Finset.sum Finset.univ rbrError) := by
  let ε : ℝ≥0 := Finset.sum Finset.univ rbrError
  have hSingle :
      Verifier.soundnessFromState impl Inv lang lang v ε :=
    soundnessFromState_of_rbr (impl := impl) (Inv := Inv) (hPres := hPres) h
  have hStateNth :
      ∀ n : Nat,
        letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
        Verifier.soundnessFromState impl Inv lang lang (v.compNth n) (n * ε) := by
    intro n
    induction n with
    | zero =>
        simpa [Nat.cast_zero, zero_mul, Verifier.compNth] using
          (Verifier.soundnessFromState_id (impl := impl) (lang := lang) (Inv := Inv))
    | succ n ih =>
        letI : ChallengesSampleable (pSpec.replicate n) :=
          ChallengesSampleable.ofReplicate (pSpec := pSpec) n
        letI : ChallengesSampleable (pSpec ++ pSpec.replicate n) :=
          ChallengesSampleable.ofAppend (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n)
        have ih' : Verifier.soundnessFromState impl Inv lang lang (v.compNth n) (n * ε) := ih
        have hComp :
            Verifier.soundnessFromState impl Inv lang lang
              (Verifier.comp v (v.compNth n)) (ε + n * ε) :=
          Verifier.soundnessFromState_comp (impl := impl) (Inv := Inv) (lang := lang)
            (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n)
            (v₁ := v) (v₂ := v.compNth n)
            hOut hState hPres hSingle ih'
        have hmul : ((n + 1 : ℝ≥0) * ε) = ε + n * ε := by
          ring
        simpa [Verifier.compNth, hmul] using hComp
  letI : ChallengesSampleable (pSpec.replicate n) :=
    ChallengesSampleable.ofReplicate (pSpec := pSpec) n
  exact soundness_of_soundnessFromState (init := init) (impl := impl)
    (hInit := hInit) (hσbound := hStateNth n)

end Soundness

end ProtocolSpec
