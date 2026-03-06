/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Composition.Util

set_option linter.style.longFile 2200

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

set_option maxHeartbeats 300000 in
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
      let flipTr : Transcript pSpec → Prop := fun tr =>
        ¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) ∧
          sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec tr)
      have hFlipMap : Pr[flip i | mx0] = Pr[flipTr | Prod.fst <$> mx0] := by
        rw [probEvent_map]
        rfl
      have hMx0 :
          Prod.fst <$> mx0 = (do
            let challenges ← sampleChallenges pSpec
            Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0) := by
        simp [mx0, map_eq_bind_pure_comp, bind_assoc]
      rw [hFlipMap, hMx0]
      simpa [flipTr] using hrbr stmtIn hstmtIn Output prover i σ0 hσ0
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

theorem oracleAwareRbrSoundness_implies_soundness
    {StmtIn StmtOut : Type}
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
  exact rbrSoundness_implies_soundness (init := init) (impl := impl) hInit hPres h

set_option maxHeartbeats 300000 in
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

set_option maxHeartbeats 300000 in
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

**Proof strategy**:
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

theorem Verifier.oracleAwareRbrSoundness_compNth
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
  exact Verifier.soundness_compNth (init := init) (impl := impl)
    hOut hState hInit hPres h n

/-! ## RBR Soundness Composition -/


private def rbrSoundness_comp_sf
    {StmtIn StmtMid StmtOut : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    {langIn : Set StmtIn} {langMid : Set StmtMid} {langOut : Set StmtOut}
    {v₁ : Verifier (OracleComp oSpec) StmtIn StmtMid pSpec₁}
    {v₂ : Verifier (OracleComp oSpec) StmtMid StmtOut pSpec₂}
    {Inv : σ → Prop}
    (sf₁ : StateFunction impl Inv langIn langMid v₁)
    (sf₂ : StateFunction impl Inv langMid langOut v₂)
    (g : StmtIn → Transcript pSpec₁ → Option StmtMid)
    (hv₁_pure : ∀ stmt tr, v₁ stmt tr = OptionT.mk (pure (g stmt tr)))
    (σw : σ) (hσw : Inv σw) :
    StateFunction impl Inv langIn langOut (Verifier.comp v₁ v₂) := by
  classical
  let toFunComp : (k : Nat) → StmtIn → PartialTranscript (pSpec₁ ++ pSpec₂) k → Prop :=
    fun k stmtIn ptr =>
      if stmtIn ∈ langIn then True
      else if hk : k < pSpec₁.length then
        sf₁.toFun k stmtIn (PartialTranscript.leftOfAppend (Nat.le_of_lt hk) ptr)
      else
        ∃ mid : StmtMid,
          g stmtIn (PartialTranscript.leftFullOfAppend (Nat.le_of_not_lt hk) ptr) = some mid ∧
          sf₂.toFun (k - pSpec₁.length) mid
            (PartialTranscript.rightOfAppend
              (show (k - pSpec₁.length) + pSpec₁.length = k by omega) ptr)
  exact {
    toFun := toFunComp
    toFun_empty := by
      intro stmt
      constructor
      · intro hStmt
        simp [toFunComp, hStmt]
      · intro hTo
        by_cases hStmt : stmt ∈ langIn
        · exact hStmt
        · simp only [toFunComp, hStmt, ite_false] at hTo
          by_cases hk : 0 < pSpec₁.length
          · have hTo0 : sf₁.toFun 0 stmt HVector.nil := by
              simpa [hk, PartialTranscript.leftOfAppend] using hTo
            exact False.elim (hStmt ((sf₁.toFun_empty stmt).mpr hTo0))
          · have hk0 : pSpec₁.length = 0 := Nat.eq_zero_of_not_pos hk
            rcases (show ∃ mid : StmtMid,
                  g stmt (PartialTranscript.leftFullOfAppend (pSpec₂ := pSpec₂)
                    (Nat.le_of_not_lt hk) HVector.nil) = some mid ∧
                    sf₂.toFun 0 mid HVector.nil from by
                  simp only [dif_neg hk] at hTo
                  rcases hTo with ⟨mid, hmid, hMid_raw⟩
                  exact ⟨mid, hmid, by
                    suffices ∀ (j : Nat) (pt : PartialTranscript pSpec₂ j),
                        j = 0 → sf₂.toFun j mid pt → sf₂.toFun 0 mid HVector.nil by
                      exact this _ _ (by omega) hMid_raw
                    intro j pt hj h; subst hj; exact h⟩) with
              ⟨mid, hmid, hMid0⟩
            have hMidLang : mid ∈ langMid := (sf₂.toFun_empty mid).mpr hMid0
            have hSf1False :
                ¬ sf₁.toFun pSpec₁.length stmt
                  (PartialTranscript.ofTranscript
                    (PartialTranscript.leftFullOfAppend
                      (pSpec₂ := pSpec₂) (Nat.le_of_not_lt hk) HVector.nil)) := by
              have hSf1False0 : ¬ sf₁.toFun 0 stmt HVector.nil := by
                intro hSf1
                exact hStmt ((sf₁.toFun_empty stmt).mpr hSf1)
              suffices ∀ (n : Nat) (hn : n = 0)
                  (pt : PartialTranscript pSpec₁ n),
                  ¬ sf₁.toFun 0 stmt HVector.nil → ¬ sf₁.toFun n stmt pt by
                exact this _ hk0 _ hSf1False0
              intro n hn pt h; subst hn; exact h
            have hZero :
                Pr[(· ∈ langMid) | OptionT.mk do
                  (simulateQ impl
                    (v₁ stmt
                      (PartialTranscript.leftFullOfAppend
                        (pSpec₂ := pSpec₂) (Nat.le_of_not_lt hk) HVector.nil))).run'
                      σw] = 0 :=
              sf₁.toFun_full stmt
                (tr := PartialTranscript.leftFullOfAppend
                  (pSpec₂ := pSpec₂) (Nat.le_of_not_lt hk) HVector.nil)
                σw hσw hSf1False
            have hMidSupport :
                mid ∈ support (OptionT.mk do
                  (simulateQ impl
                    (v₁ stmt
                      (PartialTranscript.leftFullOfAppend
                        (pSpec₂ := pSpec₂) (Nat.le_of_not_lt hk) HVector.nil))).run'
                      σw) := by
              rw [OptionT.mem_support_iff]
              simp only [OptionT.run, OptionT.mk, hv₁_pure, simulateQ_pure, StateT.run',
                support_map, Set.mem_image]
              exact ⟨(some mid, σw), (mem_support_pure_iff' _ _).mpr (by simp [hmid]), rfl⟩
            have hPos :
                Pr[(· ∈ langMid) | OptionT.mk do
                  (simulateQ impl
                    (v₁ stmt
                      (PartialTranscript.leftFullOfAppend
                        (pSpec₂ := pSpec₂) (Nat.le_of_not_lt hk) HVector.nil))).run'
                      σw] > 0 := by
              exact (probEvent_pos_iff).2 ⟨mid, hMidSupport, hMidLang⟩
            rw [hZero] at hPos
            simp at hPos
    toFun_next := by
      intro k hk hnon stmt tr hFalse msg
      by_cases hStmt : stmt ∈ langIn
      · intro hTrue
        exact hFalse (by simp [toFunComp, hStmt])
      · by_cases hk₁ : k < pSpec₁.length
        · let trL : PartialTranscript pSpec₁ k :=
            PartialTranscript.leftOfAppend (Nat.le_of_lt hk₁) tr
          let msgL : (pSpec₁.get ⟨k, hk₁⟩).type :=
            cast (congrArg Round.type
              (ChallengeIndex.get_eq_left (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (i := ⟨k, hk⟩) hk₁)) msg
          have hnon₁ : (pSpec₁.get ⟨k, hk₁⟩).isChallenge = false := by
            rw [← ChallengeIndex.get_eq_left (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
              (i := ⟨k, hk⟩) hk₁]
            exact hnon
          have hFalse₁ : ¬ sf₁.toFun k stmt trL := by
            simpa [toFunComp, hStmt, hk₁, trL] using hFalse
          by_cases hkSucc : k + 1 < pSpec₁.length
          · have hLeft :
              PartialTranscript.leftOfAppend (show k + 1 ≤ pSpec₁.length by omega)
                (PartialTranscript.concat (pSpec₁ ++ pSpec₂) hk tr msg) =
              PartialTranscript.concat pSpec₁ hk₁ trL msgL := by
              simpa [trL, msgL] using
                (PartialTranscript.leftOfAppend_concat (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                  (hk := hk₁) (hk₂ := hk) tr msg)
            intro hTrue
            have hTrue₁ :
                sf₁.toFun (k + 1) stmt (PartialTranscript.concat pSpec₁ hk₁ trL msgL) := by
              simpa [toFunComp, hStmt, hkSucc, hLeft, trL, msgL] using hTrue
            exact (sf₁.toFun_next k hk₁ hnon₁ stmt trL hFalse₁ msgL) hTrue₁
          · let trSucc : PartialTranscript (pSpec₁ ++ pSpec₂) (k + 1) :=
              PartialTranscript.concat (pSpec₁ ++ pSpec₂) hk tr msg
            let trFull : Transcript pSpec₁ :=
              PartialTranscript.leftFullOfAppend (show pSpec₁.length ≤ k + 1 by omega) trSucc
            let trRight0 : PartialTranscript pSpec₂ ((k + 1) - pSpec₁.length) :=
              PartialTranscript.rightOfAppend
                (show ((k + 1) - pSpec₁.length) + pSpec₁.length = k + 1 by omega) trSucc
            have hkEq : k + 1 = pSpec₁.length := by omega
            have hLeft :
              PartialTranscript.leftOfAppend (show k + 1 ≤ pSpec₁.length by omega) trSucc =
              PartialTranscript.concat pSpec₁ hk₁ trL msgL := by
              simpa [trSucc, trL, msgL] using
                (PartialTranscript.leftOfAppend_concat (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                  (hk := hk₁) (hk₂ := hk) tr msg)
            have hFalseFull :
                ¬ sf₁.toFun pSpec₁.length stmt (PartialTranscript.ofTranscript trFull) := by
              intro hFull
              have hNotSucc := sf₁.toFun_next k hk₁ hnon₁ stmt trL hFalse₁ msgL
              apply hNotSucc; rw [← hLeft]
              suffices ∀ (n : Nat) (hn : n = pSpec₁.length)
                  (tr' : PartialTranscript (pSpec₁ ++ pSpec₂) n),
                  sf₁.toFun pSpec₁.length stmt
                    (PartialTranscript.ofTranscript
                      (PartialTranscript.leftFullOfAppend (hn ▸ le_rfl) tr')) →
                  sf₁.toFun n stmt (PartialTranscript.leftOfAppend (hn ▸ le_rfl) tr') by
                exact this (k + 1) hkEq trSucc hFull
              intro n hn tr' h; subst hn
              rwa [PartialTranscript.leftOfAppend_eq_ofTranscript_leftFullOfAppend]
            intro hTrue
            rcases (by
              simpa [toFunComp, hStmt, hkSucc, hkEq, trSucc, trFull, trRight0] using hTrue :
                ∃ mid : StmtMid,
                  g stmt trFull = some mid ∧
                  sf₂.toFun ((k + 1) - pSpec₁.length) mid trRight0) with ⟨mid, hmid, hMid0⟩
            have hZeroIdx : ((k + 1) - pSpec₁.length : Nat) = 0 := by
              omega
            have hMid0' : sf₂.toFun 0 mid HVector.nil := by
              suffices ∀ (j : Nat) (pt : PartialTranscript pSpec₂ j),
                  j = 0 → sf₂.toFun j mid pt → sf₂.toFun 0 mid HVector.nil by
                exact this _ _ hZeroIdx hMid0
              intro j pt hj h; subst hj; exact h
            have hMidLang : mid ∈ langMid := (sf₂.toFun_empty mid).mpr hMid0'
            have hZero :
                Pr[(· ∈ langMid) | OptionT.mk do
                  (simulateQ impl (v₁ stmt trFull)).run' σw] = 0 :=
              sf₁.toFun_full stmt (tr := trFull) σw hσw hFalseFull
            have hMidSupport :
                mid ∈ support (OptionT.mk do
                  (simulateQ impl (v₁ stmt trFull)).run' σw) := by
              rw [OptionT.mem_support_iff]
              simp only [OptionT.run, OptionT.mk, hv₁_pure, simulateQ_pure, StateT.run',
                support_map, Set.mem_image]
              exact ⟨(some mid, σw), (mem_support_pure_iff' _ _).mpr (by simp [hmid]), rfl⟩
            have hPos :
                Pr[(· ∈ langMid) | OptionT.mk do
                  (simulateQ impl (v₁ stmt trFull)).run' σw] > 0 := by
              exact (probEvent_pos_iff).2 ⟨mid, hMidSupport, hMidLang⟩
            rw [hZero] at hPos
            simp at hPos
        · let j : Nat := k - pSpec₁.length
          let trR : PartialTranscript pSpec₂ j :=
            PartialTranscript.rightOfAppend (show j + pSpec₁.length = k by
              dsimp [j]
              omega) tr
          have hk₂ : j < pSpec₂.length := by
            dsimp [j]
            simpa [List.length_append] using
              (ChallengeIndex.rightIndexLt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (i := ⟨k, hk⟩) (Nat.le_of_not_lt hk₁))
          let msgR : (pSpec₂.get ⟨j, hk₂⟩).type :=
            cast (congrArg Round.type
              (ChallengeIndex.get_eq_right (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (i := ⟨k, hk⟩) (Nat.le_of_not_lt hk₁))) msg
          have hnon₂ : (pSpec₂.get ⟨j, hk₂⟩).isChallenge = false := by
            rw [← ChallengeIndex.get_eq_right (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
              (i := ⟨k, hk⟩) (Nat.le_of_not_lt hk₁)]
            exact hnon
          let trSucc : PartialTranscript (pSpec₁ ++ pSpec₂) (k + 1) :=
            PartialTranscript.concat (pSpec₁ ++ pSpec₂) hk tr msg
          have hLeftFull :
              PartialTranscript.leftFullOfAppend (show pSpec₁.length ≤ k + 1 by omega) trSucc =
                PartialTranscript.leftFullOfAppend (Nat.le_of_not_lt hk₁) tr := by
            simpa [trSucc] using
              (PartialTranscript.leftFullOfAppend_concat (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (hk₁ := Nat.le_of_not_lt hk₁) (hk₂ := hk) tr msg)
          have hRight :
              PartialTranscript.rightOfAppend
                  (show (j + 1) + pSpec₁.length = k + 1 by
                    simpa [j, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                      congrArg Nat.succ (Nat.sub_add_cancel (Nat.le_of_not_lt hk₁))) trSucc =
                PartialTranscript.concat pSpec₂ hk₂ trR msgR := by
            simpa [trSucc, trR, msgR, j] using
              (PartialTranscript.rightOfAppend_concat (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (h_eq := by
                  simpa [j, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                    (Nat.sub_add_cancel (Nat.le_of_not_lt hk₁))) (hk₂ := hk) tr msg)
          intro hTrue
          have hkSuccFalse : ¬ k + 1 < pSpec₁.length := by omega
          rcases (by
            simpa [toFunComp, hStmt, hk₁, hkSuccFalse, j, trSucc] using hTrue :
              ∃ mid : StmtMid,
                g stmt
                    (PartialTranscript.leftFullOfAppend
                      (Nat.le_of_not_lt hkSuccFalse) trSucc) = some mid ∧
                  sf₂.toFun ((k + 1) - pSpec₁.length) mid
                    (PartialTranscript.rightOfAppend
                      (Nat.sub_add_cancel (Nat.le_of_not_lt hkSuccFalse))
                        trSucc)) with
            ⟨mid, hmidSucc, hSf₂Succ⟩
          have hmid : g stmt
              (PartialTranscript.leftFullOfAppend (Nat.le_of_not_lt hk₁) tr) =
                some mid := by
            simpa [hLeftFull] using hmidSucc
          have hSf₂False : ¬ sf₂.toFun j mid trR := by
            intro hPrev
            exact hFalse (by
              simp [toFunComp, hStmt, hk₁, j, trR, hmid, hPrev])
          have hSuccIdx : j + 1 = (k + 1) - pSpec₁.length := by
            dsimp [j]
            omega
          have hSf₂SuccCast :
              sf₂.toFun (j + 1) mid
                (PartialTranscript.rightOfAppend (show (j + 1) + pSpec₁.length = k + 1 by omega)
                  trSucc) := by
            suffices ∀ (a : Nat) (ha : a = j + 1)
                (h_add : a + pSpec₁.length = k + 1),
                sf₂.toFun a mid (PartialTranscript.rightOfAppend h_add trSucc) →
                sf₂.toFun (j + 1) mid
                  (PartialTranscript.rightOfAppend
                    (show (j + 1) + pSpec₁.length = k + 1 by omega) trSucc) by
              exact this _ hSuccIdx.symm (by omega) hSf₂Succ
            intro a ha h_add h; subst ha; exact h
          have hSf₂Succ' :
              sf₂.toFun (j + 1) mid (PartialTranscript.concat pSpec₂ hk₂ trR msgR) := by
            simpa [hRight] using hSf₂SuccCast
          exact (sf₂.toFun_next j hk₂ hnon₂ mid trR hSf₂False msgR) hSf₂Succ'
    toFun_challenge_of_mem := by
      intro i stmt ptr hmem
      simp [toFunComp, hmem]
    toFun_full := by
      intro stmt tr σ0 hσ0 hFalse
      rw [probEvent_eq_zero_iff]
      intro stmtOut hStmtOut hLangOut
      by_cases hStmt : stmt ∈ langIn
      · exact hFalse (by simp [toFunComp, hStmt])
      · let tr₁ : Transcript pSpec₁ := (Transcript.split tr).1
        let tr₂ : Transcript pSpec₂ := (Transcript.split tr).2
        have hFalse' :
            ¬ ∃ mid : StmtMid,
              g stmt tr₁ = some mid ∧
                sf₂.toFun pSpec₂.length mid (PartialTranscript.ofTranscript tr₂) := by
          intro hExists
          rcases hExists with ⟨mid, hmid, hSf₂⟩
          have hEqIdx : (pSpec₁ ++ pSpec₂).length - pSpec₁.length = pSpec₂.length := by
            simp [List.length_append]
          have hNotLt : ¬ (pSpec₁ ++ pSpec₂).length < pSpec₁.length := by
            simp [List.length_append]
          have hLeftFull :
              PartialTranscript.leftFullOfAppend
                (show pSpec₁.length ≤ (pSpec₁ ++ pSpec₂).length by
                  simp [List.length_append])
                (PartialTranscript.ofTranscript tr) = tr₁ := by
            simpa [tr₁] using
              (PartialTranscript.leftFullOfAppend_ofTranscript_eq_split_fst
                (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) tr)
          have hLen :
              ((pSpec₁ ++ pSpec₂).length - pSpec₁.length) + pSpec₁.length =
                (pSpec₁ ++ pSpec₂).length := by
            simp [List.length_append]; omega
          have hLen₂ :
              pSpec₂.length + pSpec₁.length = (pSpec₁ ++ pSpec₂).length := by
            simp [List.length_append]; omega
          have hRightTake :
              PartialTranscript.rightOfAppend hLen (PartialTranscript.ofTranscript tr) =
              HVector.take ((pSpec₁ ++ pSpec₂).length - pSpec₁.length) pSpec₂
                (Transcript.split tr).2 := by
            simpa [hvector_take_length_eq] using
              (PartialTranscript.rightOfAppend_hvector_take (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (k := (pSpec₁ ++ pSpec₂).length)
                (hk := by simp [List.length_append])
                (hk₂ := le_rfl) tr)
          have hSf₂Full :
              sf₂.toFun ((pSpec₁ ++ pSpec₂).length - pSpec₁.length) mid
                (PartialTranscript.rightOfAppend hLen (PartialTranscript.ofTranscript tr)) := by
            suffices ∀ (j : Nat) (hj : j + pSpec₁.length = (pSpec₁ ++ pSpec₂).length),
                sf₂.toFun j mid
                  (PartialTranscript.rightOfAppend hj
                    (PartialTranscript.ofTranscript tr)) by
              exact this _ hLen
            intro j hj
            have hEq : j = pSpec₂.length := by omega
            subst hEq
            rw [show hj = (show pSpec₂.length + pSpec₁.length = (pSpec₁ ++ pSpec₂).length
              from hLen₂) from Subsingleton.elim _ _,
              PartialTranscript.rightOfAppend_ofTranscript_eq_split_snd]
            simpa [tr₂] using hSf₂
          apply hFalse
          simp only [if_true_left, hStmt, not_false_eq_true, nonempty_prop, forall_const,
            List.length_append, add_lt_iff_neg_left, not_lt_zero, ↓reduceDIte, hLeftFull,
            toFunComp]
          exact ⟨mid, hmid, hSf₂Full⟩
        cases hmid : g stmt tr₁ with
        | none =>
            have hRunNone :
                (simulateQ impl ((Verifier.comp v₁ v₂) stmt tr)).run σ0 = pure (none, σ0) := by
              simp [Verifier.comp, hv₁_pure, tr₁, hmid, simulateQ_pure,
                OptionT.instMonad, OptionT.bind, OptionT.mk, pure_bind]
            have hs' :
                ∃ x, (some stmtOut, x) ∈ support
                  ((simulateQ impl ((Verifier.comp v₁ v₂) stmt tr)).run σ0) := by
              simpa [OptionT.mem_support_iff, OptionT.mk, OptionT.run, StateT.run'] using hStmtOut
            have : False := by
              rcases hs' with ⟨x, hx⟩
              simp [hRunNone] at hx
            exact this.elim
        | some mid =>
            have hStmtOut₂ : stmtOut ∈ support (OptionT.mk do
                (simulateQ impl (v₂ mid tr₂)).run' σ0) := by
              simpa [Verifier.comp, hv₁_pure, tr₁, tr₂, hmid, simulateQ_pure] using hStmtOut
            have hSf₂False :
                ¬ sf₂.toFun pSpec₂.length mid
                  (PartialTranscript.ofTranscript tr₂) := by
              intro hSf₂
              exact hFalse' ⟨mid, hmid, hSf₂⟩
            have hZero :
                Pr[(· ∈ langOut) | OptionT.mk do
                  (simulateQ impl (v₂ mid tr₂)).run' σ0] = 0 :=
              sf₂.toFun_full mid tr₂ σ0 hσ0 hSf₂False
            have hPos :
                Pr[(· ∈ langOut) | OptionT.mk do
                  (simulateQ impl (v₂ mid tr₂)).run' σ0] > 0 := by
              exact (probEvent_pos_iff).2 ⟨stmtOut, hStmtOut₂, hLangOut⟩
            rw [hZero] at hPos
            simp at hPos
    }

set_option maxHeartbeats 300000 in
/-- Generic RBR soundness composition: given RBR soundness for `v₁` and `v₂`, with
`v₁` oracle-free and the query implementation preserving the state invariant,
`Verifier.comp v₁ v₂` is RBR sound with the appended error map. -/
theorem rbrSoundness_comp
    {StmtIn StmtMid StmtOut : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂]
    {langIn : Set StmtIn} {langMid : Set StmtMid} {langOut : Set StmtOut}
    {v₁ : Verifier (OracleComp oSpec) StmtIn StmtMid pSpec₁}
    {v₂ : Verifier (OracleComp oSpec) StmtMid StmtOut pSpec₂}
    {Inv : σ → Prop}
    (hV₁ : Verifier.OracleFree v₁)
    (hPres : QueryImpl.PreservesInv impl Inv)
    {e₁ : ChallengeIndex pSpec₁ → ℝ≥0}
    {e₂ : ChallengeIndex pSpec₂ → ℝ≥0}
    (h₁ : rbrSoundness impl langIn langMid v₁ Inv e₁)
    (h₂ : rbrSoundness impl langMid langOut v₂ Inv e₂) :
    letI := ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    rbrSoundness impl langIn langOut
      (Verifier.comp v₁ v₂) Inv (ChallengeIndex.errorAppend e₁ e₂) := by
  classical
  letI : ChallengesSampleable (pSpec₁ ++ pSpec₂) :=
    ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
  rcases h₁ with ⟨sf₁, hBound₁⟩
  rcases h₂ with ⟨sf₂, hBound₂⟩
  obtain ⟨g, hg⟩ := hV₁
  have hv₁_pure : ∀ stmt tr, v₁ stmt tr = OptionT.mk (pure (g stmt tr)) := by
    intro stmt tr; ext; simpa using hg stmt tr
  by_cases hInv : Nonempty {σ // Inv σ}
  · rcases hInv with ⟨⟨σw, hσw⟩⟩
    let toFunComp : (k : Nat) → StmtIn → PartialTranscript (pSpec₁ ++ pSpec₂) k → Prop :=
      fun k stmtIn ptr =>
        if stmtIn ∈ langIn then True
        else if hk : k < pSpec₁.length then
          sf₁.toFun k stmtIn (PartialTranscript.leftOfAppend (Nat.le_of_lt hk) ptr)
        else
          ∃ mid : StmtMid,
            g stmtIn (PartialTranscript.leftFullOfAppend (Nat.le_of_not_lt hk) ptr) = some mid ∧
            sf₂.toFun (k - pSpec₁.length) mid
              (PartialTranscript.rightOfAppend
                (show (k - pSpec₁.length) + pSpec₁.length = k by omega) ptr)
    refine ⟨rbrSoundness_comp_sf sf₁ sf₂ g hv₁_pure σw hσw (impl := impl), ?flipBound⟩
    case flipBound =>
      intro stmtIn hNotLang Output prover i σ0 hσ0
      let flipComp : Transcript (pSpec₁ ++ pSpec₂) → Prop := fun tr =>
        ¬ toFunComp i.1 stmtIn (HVector.take i.1 (pSpec₁ ++ pSpec₂) tr) ∧
          toFunComp (i.1 + 1) stmtIn (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂) tr)
      let p₁ :
          Prover (OracleComp oSpec) (Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ :=
        Prover.splitPrefix (m := OracleComp oSpec) (Output := Output) pSpec₁ prover
      let stage₁Run (ch₁ : Challenges pSpec₁) :=
        simulateQ impl (Prover.run (m := OracleComp oSpec)
          (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ ch₁)
      let stage₂Run (p₂ : Prover (OracleComp oSpec) Output pSpec₂) (ch₂ : Challenges pSpec₂) :=
        simulateQ impl (Prover.run (m := OracleComp oSpec) (Output := Output) pSpec₂ p₂ ch₂)
      let fullMx : ProbComp (Transcript (pSpec₁ ++ pSpec₂)) := do
        let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
        Prod.fst <$> (simulateQ impl
          (Prover.run (m := OracleComp oSpec) (Output := Output)
            (pSpec₁ ++ pSpec₂) prover challenges)).run' σ0
      change Pr[flipComp | fullMx] ≤ (ChallengeIndex.errorAppend e₁ e₂ i : ℝ≥0∞)
      have hsample : sampleChallenges (pSpec₁ ++ pSpec₂) = do
          let ch₁ ← sampleChallenges pSpec₁
          let ch₂ ← sampleChallenges pSpec₂
          return Challenges.join pSpec₁ pSpec₂ ch₁ ch₂ := rfl
      by_cases hiLt : i.1 < pSpec₁.length
      · let i₁ : ChallengeIndex pSpec₁ :=
          ChallengeIndex.toLeft (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i hiLt
        let leftMx : ProbComp (Transcript pSpec₁) := do
          let ch₁ ← sampleChallenges pSpec₁
          Prod.fst <$> (stage₁Run ch₁).run' σ0
        let flip₁ : Transcript pSpec₁ → Prop := fun tr₁ =>
          ¬ sf₁.toFun i₁.1 stmtIn (HVector.take i₁.1 pSpec₁ tr₁) ∧
            sf₁.toFun (i₁.1 + 1) stmtIn (HVector.take (i₁.1 + 1) pSpec₁ tr₁)
        have hFlip₁ : Pr[flip₁ | leftMx] ≤ (e₁ i₁ : ℝ≥0∞) := by
          simpa [flip₁, leftMx, stage₁Run, i₁] using
            (hBound₁ stmtIn hNotLang
              (Output := Prover (OracleComp oSpec) Output pSpec₂)
              (prover := p₁) i₁ σ0 hσ0)
        have hPointwise : ∀ tr : Transcript (pSpec₁ ++ pSpec₂),
            flipComp tr → flip₁ (Transcript.split tr).1 := by
          intro tr htr
          rcases htr with ⟨hPrev, hNext⟩
          have hPrevTake :
              PartialTranscript.leftOfAppend (Nat.le_of_lt hiLt)
                (HVector.take i.1 (pSpec₁ ++ pSpec₂) tr) =
                HVector.take i.1 pSpec₁ (Transcript.split tr).1 := by
            simpa using
              (PartialTranscript.leftOfAppend_hvector_take (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                (k := i.1) (hk := Nat.le_of_lt hiLt) tr)
          by_cases hiSuccLt : i.1 + 1 < pSpec₁.length
          · have hNextTake :
                PartialTranscript.leftOfAppend (Nat.le_of_lt hiSuccLt)
                  (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂) tr) =
                  HVector.take (i.1 + 1) pSpec₁ (Transcript.split tr).1 := by
              simpa using
                (PartialTranscript.leftOfAppend_hvector_take (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                  (k := i.1 + 1) (hk := Nat.le_of_lt hiSuccLt) tr)
            have hPrev₁ :
                ¬ sf₁.toFun i₁.1 stmtIn (HVector.take i₁.1 pSpec₁ (Transcript.split tr).1) := by
              simpa [flipComp, toFunComp, hNotLang, hiLt, i₁, ChallengeIndex.toLeft, hPrevTake]
                using hPrev
            have hNext₁ :
                sf₁.toFun (i₁.1 + 1) stmtIn
                  (HVector.take (i₁.1 + 1) pSpec₁ (Transcript.split tr).1) := by
              simpa [flipComp, toFunComp, hNotLang, hiLt, hiSuccLt, i₁, ChallengeIndex.toLeft,
                hNextTake] using hNext
            exact ⟨hPrev₁, hNext₁⟩
          · have hiEq : i.1 + 1 = pSpec₁.length := by
              omega
            have hPrev₁ :
                ¬ sf₁.toFun i₁.1 stmtIn (HVector.take i₁.1 pSpec₁ (Transcript.split tr).1) := by
              simpa [flipComp, toFunComp, hNotLang, hiLt, i₁, ChallengeIndex.toLeft, hPrevTake]
                using hPrev
            have hLeftSucc :
                PartialTranscript.leftFullOfAppend (Nat.le_of_not_lt hiSuccLt)
                  (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂) tr) =
                  (Transcript.split tr).1 := by
              simpa [hiEq] using
                (PartialTranscript.leftFullOfAppend_hvector_take
                  (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                  (k := i.1 + 1) (hk := Nat.le_of_not_lt hiSuccLt)
                  (hk₂ := Nat.succ_le_of_lt i.1.isLt) tr)
            have hRightSucc :
                PartialTranscript.rightOfAppend
                    (show ((i.1 + 1) - pSpec₁.length) + pSpec₁.length = i.1 + 1 by omega)
                    (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂) tr) =
                  HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ (Transcript.split tr).2 := by
              simpa using
                (PartialTranscript.rightOfAppend_hvector_take (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                  (k := i.1 + 1) (hk := Nat.le_of_not_lt hiSuccLt)
                  (hk₂ := Nat.succ_le_of_lt i.1.isLt) tr)
            rcases (by
              simpa [toFunComp, hNotLang, hiLt, hiSuccLt, hiEq, hLeftSucc, hRightSucc] using hNext :
                ∃ mid : StmtMid,
                  g stmtIn (Transcript.split tr).1 = some mid ∧
                    sf₂.toFun ((i.1 + 1) - pSpec₁.length) mid
                      (HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ (Transcript.split tr).2))
              with ⟨mid, hmid, hSf₂0⟩
            have hZeroIdx : ((i.1 + 1) - pSpec₁.length : Nat) = 0 := by
              omega
            have hMid0' : sf₂.toFun 0 mid HVector.nil := by
              rw [hZeroIdx] at hSf₂0
              simpa using hSf₂0
            have hMidLang : mid ∈ langMid := (sf₂.toFun_empty mid).mpr hMid0'
            have hTrueFull :
                sf₁.toFun pSpec₁.length stmtIn
                  (PartialTranscript.ofTranscript (Transcript.split tr).1) := by
              by_contra hFalseFull
              have hZero :
                  Pr[(· ∈ langMid) | OptionT.mk do
                    (simulateQ impl (v₁ stmtIn (Transcript.split tr).1)).run' σ0] = 0 :=
                sf₁.toFun_full stmtIn (tr := (Transcript.split tr).1) σ0 hσ0 hFalseFull
              have hMidSupport :
                  mid ∈ support (OptionT.mk do
                    (simulateQ impl (v₁ stmtIn (Transcript.split tr).1)).run' σ0) := by
                rw [OptionT.mem_support_iff]
                simp only [OptionT.run, OptionT.mk, hv₁_pure, simulateQ_pure, StateT.run',
                  support_map, Set.mem_image]
                exact ⟨(some mid, σ0), (mem_support_pure_iff' _ _).mpr (by simp [hmid]), rfl⟩
              have hPos :
                  Pr[(· ∈ langMid) | OptionT.mk do
                    (simulateQ impl (v₁ stmtIn (Transcript.split tr).1)).run' σ0] > 0 := by
                exact (probEvent_pos_iff).2 ⟨mid, hMidSupport, hMidLang⟩
              rw [hZero] at hPos
              simp at hPos
            have hi₁Eq : (i₁.1 : Nat) + 1 = pSpec₁.length := by
              simpa [i₁, ChallengeIndex.toLeft] using hiEq
            have hNext₁ :
                sf₁.toFun (i₁.1 + 1) stmtIn
                  (HVector.take (i₁.1 + 1) pSpec₁ (Transcript.split tr).1) := by
              rw [hi₁Eq]
              simpa [hvector_take_length_eq] using hTrueFull
            exact ⟨hPrev₁, hNext₁⟩
        let mx : ProbComp ((Transcript pSpec₁ × Prover (OracleComp oSpec) Output pSpec₂) × σ) := do
          let ch₁ ← sampleChallenges pSpec₁
          (stage₁Run ch₁).run σ0
        let my (z : (Transcript pSpec₁ × Prover (OracleComp oSpec) Output pSpec₂) × σ) :
            ProbComp (Transcript pSpec₂) := do
          let ch₂ ← sampleChallenges pSpec₂
          Prod.fst <$> (stage₂Run z.1.2 ch₂).run' z.2
        let leftEvent : Transcript (pSpec₁ ++ pSpec₂) → Prop := fun tr =>
          flip₁ (Transcript.split tr).1
        let swapped : ProbComp (Transcript (pSpec₁ ++ pSpec₂)) := do
          let ch₁ ← sampleChallenges pSpec₁
          let z ← (stage₁Run ch₁).run σ0
          let ch₂ ← sampleChallenges pSpec₂
          let a ← (stage₂Run z.1.2 ch₂).run' z.2
          pure (Transcript.join z.1.1 a.1)
        let unswapped : ProbComp (Transcript (pSpec₁ ++ pSpec₂)) := do
          let ch₁ ← sampleChallenges pSpec₁
          let ch₂ ← sampleChallenges pSpec₂
          let a ← (simulateQ impl
            (Prover.run (m := OracleComp oSpec) (Output := Output)
              (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run' σ0
          pure a.1
        have hFullMx : fullMx = unswapped := by
          unfold fullMx unswapped
          rw [hsample]
          simp [map_eq_bind_pure_comp, bind_assoc]
        have hFactor :
            Pr[leftEvent | fullMx] = Pr[leftEvent | swapped] := by
          rw [hFullMx]
          unfold swapped
          refine probEvent_bind_congr ?_
          intro ch₁ _
          have hDecomp :
              Pr[leftEvent | do
                let ch₂ ← sampleChallenges pSpec₂
                let a ← (simulateQ impl
                  (Prover.run (m := OracleComp oSpec) (Output := Output)
                    (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run' σ0
                pure a.1] =
              Pr[leftEvent | do
                let ch₂ ← sampleChallenges pSpec₂
                let z ← (stage₁Run ch₁).run σ0
                let a ← (stage₂Run z.1.2 ch₂).run' z.2
                pure (Transcript.join z.1.1 a.1)] := by
            refine probEvent_bind_congr ?_
            intro ch₂ _
            rw [Prover.run_splitPrefix_join (prover := prover) (ch₁ := ch₁) (ch₂ := ch₂)]
            simp [p₁, stage₁Run, stage₂Run, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc]
          calc
            Pr[leftEvent | do
              let ch₂ ← sampleChallenges pSpec₂
              let a ← (simulateQ impl
                (Prover.run (m := OracleComp oSpec) (Output := Output)
                  (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run' σ0
              pure a.1]
                = Pr[leftEvent | do
                    let ch₂ ← sampleChallenges pSpec₂
                    let z ← (stage₁Run ch₁).run σ0
                    let a ← (stage₂Run z.1.2 ch₂).run' z.2
                    pure (Transcript.join z.1.1 a.1)] := hDecomp
            _ = Pr[leftEvent | do
                    let z ← (stage₁Run ch₁).run σ0
                    let ch₂ ← sampleChallenges pSpec₂
                    let a ← (stage₂Run z.1.2 ch₂).run' z.2
                    pure (Transcript.join z.1.1 a.1)] := by
                  simpa [bind_assoc] using
                    (probEvent_bind_bind_swap
                      (mx := sampleChallenges pSpec₂)
                      (my := (stage₁Run ch₁).run σ0)
                      (f := fun ch₂ z => do
                        let a ← (stage₂Run z.1.2 ch₂).run' z.2
                        pure (Transcript.join z.1.1 a.1))
                      (q := leftEvent))
        have hSwapped : swapped = mx >>= fun z => Transcript.join z.1.1 <$> my z := by
          simp [swapped, mx, my, map_eq_bind_pure_comp, bind_assoc]
        have hMapMx :
            (fun z : ((Transcript pSpec₁ ×
                Prover (OracleComp oSpec) Output pSpec₂) × σ) =>
              z.1.1) <$> mx = leftMx := by
          simp [mx, leftMx, map_eq_bind_pure_comp, bind_assoc]
        have hInnerLeft :
            ∀ z ∈ support mx,
              Pr[leftEvent | Transcript.join z.1.1 <$> my z] ≤
                Pr[flip₁ | (pure z.1.1 : ProbComp _)] := by
          intro z hz
          rw [probEvent_map]
          by_cases hflip : flip₁ z.1.1
          · have hLe : Pr[(fun _ : Transcript pSpec₂ => True) | my z] ≤ 1 :=
              probEvent_le_one
            simp [leftEvent, hflip]
          · simp [leftEvent, Function.comp, Transcript.split_join, hflip]
        have hLeftBound :
            Pr[leftEvent | mx >>= fun z => Transcript.join z.1.1 <$> my z] ≤
              Pr[flip₁ | leftMx] := by
          calc
            Pr[leftEvent | mx >>= fun z => Transcript.join z.1.1 <$> my z]
                = ∑' z, Pr[= z | mx] * Pr[leftEvent | Transcript.join z.1.1 <$> my z] := by
                    rw [probEvent_bind_eq_tsum]
            _ ≤ ∑' z, Pr[= z | mx] * Pr[flip₁ | pure z.1.1] := by
                  refine ENNReal.tsum_le_tsum fun z => ?_
                  by_cases hz : z ∈ support mx
                  · exact mul_le_mul' le_rfl (hInnerLeft z hz)
                  · have hProb : Pr[= z | mx] = 0 := probOutput_eq_zero_of_not_mem_support hz
                    simp [hProb]
            _ = Pr[flip₁ |
                (fun z : ((Transcript pSpec₁ ×
                    Prover (OracleComp oSpec) Output pSpec₂) × σ) =>
                  z.1.1) <$> mx] := by
                  rw [map_eq_bind_pure_comp, probEvent_bind_eq_tsum]; rfl
            _ = Pr[flip₁ | leftMx] := by
                  rw [hMapMx]
        calc
          Pr[flipComp | fullMx]
              ≤ Pr[leftEvent | fullMx] := by
                exact probEvent_mono (fun tr _ h => hPointwise tr h)
          _ = Pr[leftEvent | swapped] := hFactor
          _ = Pr[leftEvent | mx >>= fun z => Transcript.join z.1.1 <$> my z] := by
                rw [hSwapped]
          _ ≤ Pr[flip₁ | leftMx] := hLeftBound
          _ ≤ (e₁ i₁ : ℝ≥0∞) := hFlip₁
          _ = ChallengeIndex.errorAppend e₁ e₂ i := by
                simp [ChallengeIndex.errorAppend, ChallengeIndex.split, i₁, hiLt]
      · let j : ChallengeIndex pSpec₂ :=
          ChallengeIndex.toRight (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i (Nat.le_of_not_lt hiLt)
        let mx : ProbComp ((Transcript pSpec₁ × Prover (OracleComp oSpec) Output pSpec₂) × σ) := do
          let ch₁ ← sampleChallenges pSpec₁
          (stage₁Run ch₁).run σ0
        let my (z : (Transcript pSpec₁ × Prover (OracleComp oSpec) Output pSpec₂) × σ) :
            ProbComp (Transcript pSpec₂) := do
          let ch₂ ← sampleChallenges pSpec₂
          Prod.fst <$> (stage₂Run z.1.2 ch₂).run' z.2
        let flip₂ (mid : StmtMid) : Transcript pSpec₂ → Prop := fun tr₂ =>
          ¬ sf₂.toFun j.1 mid (HVector.take j.1 pSpec₂ tr₂) ∧
            sf₂.toFun (j.1 + 1) mid (HVector.take (j.1 + 1) pSpec₂ tr₂)
        let swapped : ProbComp (Transcript (pSpec₁ ++ pSpec₂)) := do
          let ch₁ ← sampleChallenges pSpec₁
          let z ← (stage₁Run ch₁).run σ0
          let ch₂ ← sampleChallenges pSpec₂
          let a ← (stage₂Run z.1.2 ch₂).run' z.2
          pure (Transcript.join z.1.1 a.1)
        let unswapped : ProbComp (Transcript (pSpec₁ ++ pSpec₂)) := do
          let ch₁ ← sampleChallenges pSpec₁
          let ch₂ ← sampleChallenges pSpec₂
          let a ← (simulateQ impl
            (Prover.run (m := OracleComp oSpec) (Output := Output)
              (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run' σ0
          pure a.1
        have hFullMx : fullMx = unswapped := by
          unfold fullMx unswapped
          rw [hsample]
          simp [map_eq_bind_pure_comp, bind_assoc]
        have hFactor :
            Pr[flipComp | fullMx] = Pr[flipComp | swapped] := by
          rw [hFullMx]
          unfold swapped
          refine probEvent_bind_congr ?_
          intro ch₁ _
          have hDecomp :
              Pr[flipComp | do
                let ch₂ ← sampleChallenges pSpec₂
                let a ← (simulateQ impl
                  (Prover.run (m := OracleComp oSpec) (Output := Output)
                    (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run' σ0
                pure a.1] =
              Pr[flipComp | do
                let ch₂ ← sampleChallenges pSpec₂
                let z ← (stage₁Run ch₁).run σ0
                let a ← (stage₂Run z.1.2 ch₂).run' z.2
                pure (Transcript.join z.1.1 a.1)] := by
            refine probEvent_bind_congr ?_
            intro ch₂ _
            rw [Prover.run_splitPrefix_join (prover := prover) (ch₁ := ch₁) (ch₂ := ch₂)]
            simp [p₁, stage₁Run, stage₂Run, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc]
          calc
            Pr[flipComp | do
              let ch₂ ← sampleChallenges pSpec₂
              let a ← (simulateQ impl
                (Prover.run (m := OracleComp oSpec) (Output := Output)
                  (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂))).run' σ0
              pure a.1]
                = Pr[flipComp | do
                    let ch₂ ← sampleChallenges pSpec₂
                    let z ← (stage₁Run ch₁).run σ0
                    let a ← (stage₂Run z.1.2 ch₂).run' z.2
                    pure (Transcript.join z.1.1 a.1)] := hDecomp
            _ = Pr[flipComp | do
                    let z ← (stage₁Run ch₁).run σ0
                    let ch₂ ← sampleChallenges pSpec₂
                    let a ← (stage₂Run z.1.2 ch₂).run' z.2
                    pure (Transcript.join z.1.1 a.1)] := by
                  simpa [bind_assoc] using
                    (probEvent_bind_bind_swap
                      (mx := sampleChallenges pSpec₂)
                      (my := (stage₁Run ch₁).run σ0)
                      (f := fun ch₂ z => do
                        let a ← (stage₂Run z.1.2 ch₂).run' z.2
                        pure (Transcript.join z.1.1 a.1))
                      (q := flipComp))
        have hSwapped : swapped = mx >>= fun z => Transcript.join z.1.1 <$> my z := by
          simp [swapped, mx, my, map_eq_bind_pure_comp, bind_assoc]
        have hInner : ∀ z ∈ support mx,
            Pr[flipComp | Transcript.join z.1.1 <$> my z] ≤ (e₂ j : ℝ≥0∞) := by
          intro z hz
          have hInvz : Inv z.2 := by
            simp only [mx, mem_support_bind_iff] at hz
            rcases hz with ⟨ch₁, _, hz₁⟩
            exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
              (oa := Prover.run pSpec₁ p₁ ch₁) σ0 hσ0 _ hz₁)
          rw [probEvent_map]
          have hiSuccFalse : ¬ i.1 + 1 < pSpec₁.length := by
            omega
          cases hmid : g stmtIn z.1.1 with
          | none =>
              have hFlipNone :
                  (fun tr₂ => flipComp (Transcript.join z.1.1 tr₂)) = fun _ => False := by
                funext tr₂
                have hLeftSucc :
                    PartialTranscript.leftFullOfAppend (Nat.le_of_not_lt hiSuccFalse)
                      (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂) (Transcript.join z.1.1 tr₂)) =
                      z.1.1 := by
                  simpa [Transcript.split_join] using
                    (PartialTranscript.leftFullOfAppend_hvector_take
                      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                      (k := i.1 + 1) (hk := Nat.le_of_not_lt hiSuccFalse)
                      (hk₂ := Nat.succ_le_of_lt i.1.isLt)
                      (Transcript.join z.1.1 tr₂))
                have hRightSucc :
                    PartialTranscript.rightOfAppend
                        (show ((i.1 + 1) - pSpec₁.length) +
                          pSpec₁.length = i.1 + 1 by omega)
                        (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂)
                          (Transcript.join z.1.1 tr₂)) =
                      HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ tr₂ := by
                  simpa [Transcript.split_join] using
                    (PartialTranscript.rightOfAppend_hvector_take
                      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                      (k := i.1 + 1) (hk := Nat.le_of_not_lt hiSuccFalse)
                      (hk₂ := Nat.succ_le_of_lt i.1.isLt)
                      (Transcript.join z.1.1 tr₂))
                simp [flipComp, toFunComp, hNotLang, hiLt, hiSuccFalse,
                  hmid, hLeftSucc, hRightSucc]
              have hFlipNoneComp : flipComp ∘ Transcript.join z.1.1 = fun _ => False := by
                simpa [Function.comp] using hFlipNone
              rw [hFlipNoneComp]
              simp
          | some mid =>
              by_cases hMidNotLang : mid ∉ langMid
              · have hFlipEq :
                    (fun tr₂ => flipComp (Transcript.join z.1.1 tr₂)) = flip₂ mid := by
                  funext tr₂
                  have hiGe : pSpec₁.length ≤ i.1 := Nat.le_of_not_lt hiLt
                  have hLeftPrev :
                      PartialTranscript.leftFullOfAppend hiGe
                        (HVector.take i.1 (pSpec₁ ++ pSpec₂)
                          (Transcript.join z.1.1 tr₂)) =
                        z.1.1 := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.leftFullOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1) (hk := hiGe)
                        (hk₂ := Nat.le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hRightPrev :
                      PartialTranscript.rightOfAppend
                          (show (i.1 - pSpec₁.length) +
                            pSpec₁.length = i.1 by omega)
                          (HVector.take i.1 (pSpec₁ ++ pSpec₂)
                            (Transcript.join z.1.1 tr₂)) =
                        HVector.take (i.1 - pSpec₁.length)
                          pSpec₂ tr₂ := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.rightOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1) (hk := hiGe)
                        (hk₂ := Nat.le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hLeftSucc :
                      PartialTranscript.leftFullOfAppend
                          (Nat.le_of_not_lt hiSuccFalse)
                        (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂)
                          (Transcript.join z.1.1 tr₂)) =
                        z.1.1 := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.leftFullOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1 + 1)
                        (hk := Nat.le_of_not_lt hiSuccFalse)
                        (hk₂ := Nat.succ_le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hRightSucc :
                      PartialTranscript.rightOfAppend
                          (show ((i.1 + 1) - pSpec₁.length) +
                            pSpec₁.length = i.1 + 1 by omega)
                          (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂)
                            (Transcript.join z.1.1 tr₂)) =
                        HVector.take ((i.1 + 1) - pSpec₁.length)
                          pSpec₂ tr₂ := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.rightOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1 + 1)
                        (hk := Nat.le_of_not_lt hiSuccFalse)
                        (hk₂ := Nat.succ_le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hjEq : (j.1 : Nat) = i.1 - pSpec₁.length := by
                    rfl
                  have hjSuccEq : (j.1 : Nat) + 1 = (i.1 + 1) - pSpec₁.length := by
                    dsimp [j, ChallengeIndex.toRight]
                    omega
                  have hFlipEqBase :
                      flipComp (Transcript.join z.1.1 tr₂) ↔
                        (¬ sf₂.toFun (i.1 - pSpec₁.length) mid
                            (HVector.take (i.1 - pSpec₁.length) pSpec₂ tr₂) ∧
                          sf₂.toFun ((i.1 + 1) - pSpec₁.length) mid
                            (HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ tr₂)) := by
                    simp [flipComp, toFunComp, hNotLang, hiLt, hiSuccFalse, hmid,
                      hLeftPrev, hRightPrev, hLeftSucc, hRightSucc]
                  apply propext
                  constructor
                  · intro h
                    rcases hFlipEqBase.mp h with ⟨hPrev, hSucc⟩
                    have hSucc' :
                        sf₂.toFun (j.1 + 1) mid
                          (HVector.take (j.1 + 1) pSpec₂ tr₂) := by
                      rw [hjSuccEq]
                      exact hSucc
                    exact ⟨by simpa [hjEq] using hPrev, hSucc'⟩
                  · intro h
                    have hPrev :
                        ¬ sf₂.toFun (i.1 - pSpec₁.length) mid
                            (HVector.take (i.1 - pSpec₁.length) pSpec₂ tr₂) := by
                      simpa [hjEq] using h.1
                    have hSucc :
                        sf₂.toFun ((i.1 + 1) - pSpec₁.length) mid
                          (HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ tr₂) := by
                      rw [← hjSuccEq]
                      exact h.2
                    exact hFlipEqBase.mpr ⟨hPrev, hSucc⟩
                have hFlipEqComp : flipComp ∘ Transcript.join z.1.1 = flip₂ mid := by
                  simpa [Function.comp] using hFlipEq
                rw [hFlipEqComp]
                simpa [flip₂, my] using
                  (hBound₂ mid hMidNotLang (Output := Output) (prover := z.1.2) j z.2 hInvz)
              · have hMidLang : mid ∈ langMid := by
                  exact not_not.mp hMidNotLang
                have hFlipEq :
                    (fun tr₂ => flipComp (Transcript.join z.1.1 tr₂)) = flip₂ mid := by
                  funext tr₂
                  have hiGe : pSpec₁.length ≤ i.1 := Nat.le_of_not_lt hiLt
                  have hLeftPrev :
                      PartialTranscript.leftFullOfAppend hiGe
                        (HVector.take i.1 (pSpec₁ ++ pSpec₂)
                          (Transcript.join z.1.1 tr₂)) =
                        z.1.1 := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.leftFullOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1) (hk := hiGe)
                        (hk₂ := Nat.le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hRightPrev :
                      PartialTranscript.rightOfAppend
                          (show (i.1 - pSpec₁.length) +
                            pSpec₁.length = i.1 by omega)
                          (HVector.take i.1 (pSpec₁ ++ pSpec₂)
                            (Transcript.join z.1.1 tr₂)) =
                        HVector.take (i.1 - pSpec₁.length)
                          pSpec₂ tr₂ := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.rightOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1) (hk := hiGe)
                        (hk₂ := Nat.le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hLeftSucc :
                      PartialTranscript.leftFullOfAppend
                          (Nat.le_of_not_lt hiSuccFalse)
                        (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂)
                          (Transcript.join z.1.1 tr₂)) =
                        z.1.1 := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.leftFullOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1 + 1)
                        (hk := Nat.le_of_not_lt hiSuccFalse)
                        (hk₂ := Nat.succ_le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hRightSucc :
                      PartialTranscript.rightOfAppend
                          (show ((i.1 + 1) - pSpec₁.length) +
                            pSpec₁.length = i.1 + 1 by omega)
                          (HVector.take (i.1 + 1) (pSpec₁ ++ pSpec₂)
                            (Transcript.join z.1.1 tr₂)) =
                        HVector.take ((i.1 + 1) - pSpec₁.length)
                          pSpec₂ tr₂ := by
                    simpa [Transcript.split_join] using
                      (PartialTranscript.rightOfAppend_hvector_take
                        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                        (k := i.1 + 1)
                        (hk := Nat.le_of_not_lt hiSuccFalse)
                        (hk₂ := Nat.succ_le_of_lt i.1.isLt)
                        (Transcript.join z.1.1 tr₂))
                  have hjEq : (j.1 : Nat) = i.1 - pSpec₁.length := by
                    rfl
                  have hjSuccEq : (j.1 : Nat) + 1 = (i.1 + 1) - pSpec₁.length := by
                    dsimp [j, ChallengeIndex.toRight]
                    omega
                  have hFlipEqBase :
                      flipComp (Transcript.join z.1.1 tr₂) ↔
                        (¬ sf₂.toFun (i.1 - pSpec₁.length) mid
                            (HVector.take (i.1 - pSpec₁.length) pSpec₂ tr₂) ∧
                          sf₂.toFun ((i.1 + 1) - pSpec₁.length) mid
                            (HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ tr₂)) := by
                    simp [flipComp, toFunComp, hNotLang, hiLt, hiSuccFalse, hmid,
                      hLeftPrev, hRightPrev, hLeftSucc, hRightSucc]
                  apply propext
                  constructor
                  · intro h
                    rcases hFlipEqBase.mp h with ⟨hPrev, hSucc⟩
                    have hSucc' :
                        sf₂.toFun (j.1 + 1) mid
                          (HVector.take (j.1 + 1) pSpec₂ tr₂) := by
                      rw [hjSuccEq]
                      exact hSucc
                    exact ⟨by simpa [hjEq] using hPrev, hSucc'⟩
                  · intro h
                    have hPrev :
                        ¬ sf₂.toFun (i.1 - pSpec₁.length) mid
                            (HVector.take (i.1 - pSpec₁.length) pSpec₂ tr₂) := by
                      simpa [hjEq] using h.1
                    have hSucc :
                        sf₂.toFun ((i.1 + 1) - pSpec₁.length) mid
                          (HVector.take ((i.1 + 1) - pSpec₁.length) pSpec₂ tr₂) := by
                      rw [← hjSuccEq]
                      exact h.2
                    exact hFlipEqBase.mpr ⟨hPrev, hSucc⟩
                have hFlipEqComp : flipComp ∘ Transcript.join z.1.1 = flip₂ mid := by
                  simpa [Function.comp] using hFlipEq
                rw [hFlipEqComp]
                have hZero : Pr[flip₂ mid | my z] = 0 := by
                  rw [probEvent_eq_zero_iff]
                  intro tr₂ htr₂ hflip
                  exact hflip.1
                    (sf₂.toFun_challenge_of_mem j mid
                      (HVector.take j.1 pSpec₂ tr₂) hMidLang)
                rw [hZero]
                simp
        rw [hFactor, hSwapped, probEvent_bind_eq_tsum]
        calc
          ∑' z, Pr[= z | mx] * Pr[flipComp | Transcript.join z.1.1 <$> my z]
              ≤ ∑' z, Pr[= z | mx] * (e₂ j : ℝ≥0∞) := by
                refine ENNReal.tsum_le_tsum fun z => ?_
                by_cases hz : z ∈ support mx
                · exact mul_le_mul' le_rfl (hInner z hz)
                · have hProb : Pr[= z | mx] = 0 := probOutput_eq_zero_of_not_mem_support hz
                  simp [hProb]
          _ = (∑' z, Pr[= z | mx]) * (e₂ j : ℝ≥0∞) := by
                rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * (e₂ j : ℝ≥0∞) := by
                exact mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = (e₂ j : ℝ≥0∞) := by
                simp
          _ = ChallengeIndex.errorAppend e₁ e₂ i := by
                simp [ChallengeIndex.errorAppend, ChallengeIndex.split, hiLt, j]
  · have hNoInv : ∀ σ0, Inv σ0 → False := by
      intro σ0 hσ0
      exact hInv ⟨⟨σ0, hσ0⟩⟩
    refine ⟨{
      toFun := fun _ stmt _ => stmt ∈ langIn
      toFun_empty := by
        intro stmt
        rfl
      toFun_next := by
        intro k hk hnon stmt tr hFalse msg hTrue
        exact hFalse hTrue
      toFun_challenge_of_mem := by
        intro i stmt ptr hmem
        exact hmem
      toFun_full := by
        intro stmt tr σ0 hσ0 hFalse
        exact False.elim (hNoInv σ0 hσ0)
    }, ?_⟩
    intro stmtIn hNotLang Output prover i σ0 hσ0
    exact False.elim (hNoInv σ0 hσ0)

/-- Any zero-round protocol (i.e. `pSpec.replicate 0`) is trivially RBR sound: the state function
is membership in the language, and there are no challenge rounds to bound. -/
theorem rbrSoundness_replicate_zero
    {S : Type}
    {pSpec : ProtocolSpec}
    [ChallengesSampleable pSpec]
    {lang : Set S}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    {e : ChallengeIndex pSpec → ℝ≥0} :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) 0
    rbrSoundness impl lang lang
      (v.compNth 0) Inv (ChallengeIndex.errorReplicate e 0) := by
  refine ⟨{
    toFun := fun _ stmt _ => stmt ∈ lang
    toFun_empty := fun _ => Iff.rfl
    toFun_next := fun k hk => absurd hk (by simp [ProtocolSpec.replicate])
    toFun_challenge_of_mem := fun i => absurd i.1.isLt (by simp [ProtocolSpec.replicate])
    toFun_full := by
      intro stmt tr σ0 _ hNot
      rw [probEvent_eq_zero_iff]
      intro s hs hsLang
      apply hNot
      have : s = stmt := by
        simp only [Verifier.compNth, OptionT.mk, OptionT.run,
          StateT.run', OptionT.mem_support_iff] at hs
        rcases hs with ⟨u, hu⟩
        exact (Option.some.inj rfl).symm
      subst this; exact hsLang
  }, fun _ _ _ _ i => absurd i.1.isLt (by simp [ProtocolSpec.replicate])⟩

/-- `n`-fold RBR soundness composition using `OracleFree` and `PreservesInv`. -/
theorem rbrSoundness_compNth
    {S : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {lang : Set S}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    (hV : Verifier.OracleFree v)
    (hPres : QueryImpl.PreservesInv impl Inv)
    {e : ChallengeIndex pSpec → ℝ≥0}
    (h : rbrSoundness impl lang lang v Inv e) :
    (n : Nat) →
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    rbrSoundness impl lang lang
      (v.compNth n) Inv (ChallengeIndex.errorReplicate e n)
  | 0 => rbrSoundness_replicate_zero impl
  | n + 1 => by
      letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
      have h_comp := rbrSoundness_comp (impl := impl) hV hPres h
        (rbrSoundness_compNth hV hPres h n)
      rcases h_comp with ⟨sf, hBound⟩
      refine ⟨sf, fun stmtIn hNotLang Output prover i σ0 hσ0 => ?_⟩
      rw [ChallengeIndex.errorReplicate_succ_eq_errorAppend]
      exact hBound stmtIn hNotLang Output prover i σ0 hσ0

end Soundness

end ProtocolSpec
