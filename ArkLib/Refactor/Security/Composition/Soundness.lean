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
  sorry /- WIP proof:
  intro Output prover stmtIn hstmtIn σ0 hσ0
  have hexp :
      (do
        let challenges ← sampleChallenges ([] : ProtocolSpec)
        (simulateQ impl (do
          let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
            ([] : ProtocolSpec) prover challenges
          let verResult ← ((fun stmt _ => (pure stmt : OptionT (OracleComp oSpec) S)) stmtIn tr).run
          return (verResult, out))).run' σ0)
        = (pure (some stmtIn, prover) : ProbComp (Option S × Output)) := by
    simp [sampleChallenges, ChallengesSampleable.sampleChallenges, Prover.run, simulateQ_pure]
  have hnone : ¬ (∃ s ∈ lang, (some stmtIn : Option S) = some s) := by
    intro hs
    rcases hs with ⟨s, hsLang, hsEq⟩
    have hEq : stmtIn = s := by
      simpa using Option.some.inj hsEq
    exact hstmtIn (hEq ▸ hsLang)
  let accept : (Option S × Output) → Prop := fun z => ∃ s ∈ lang, z.1 = some s
  have hbound' :
      Pr[accept | do
        let challenges ← sampleChallenges ([] : ProtocolSpec)
        (simulateQ impl (do
          let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
            ([] : ProtocolSpec) prover challenges
          let verResult ← ((fun stmt _ => (pure stmt : OptionT (OracleComp oSpec) S)) stmtIn tr).run
          return (verResult, out))).run' σ0] ≤ (0 : ℝ≥0∞) := by
    calc
      Pr[accept | do
        let challenges ← sampleChallenges ([] : ProtocolSpec)
        (simulateQ impl (do
          let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
            ([] : ProtocolSpec) prover challenges
          let verResult ← ((fun stmt _ => (pure stmt : OptionT (OracleComp oSpec) S)) stmtIn tr).run
          return (verResult, out))).run' σ0]
          = Pr[accept | (pure (some stmtIn, prover) : ProbComp (Option S × Output))] := by
              rw [hexp]
      _ = 0 := by
            rw [probEvent_eq_zero_iff]
            intro x hx
            simp only [support_pure, Set.mem_singleton_iff] at hx
            rcases hx with rfl
            simpa [accept] using hnone
      _ ≤ 0 := le_rfl
  have hbound :
      Pr[(fun (verResult, _) => ∃ s ∈ lang, verResult = some s) | do
        let challenges ← sampleChallenges ([] : ProtocolSpec)
        (simulateQ impl (do
          let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
            ([] : ProtocolSpec) prover challenges
          let verResult ← ((fun stmt _ => (pure stmt : OptionT (OracleComp oSpec) S)) stmtIn tr).run
          return (verResult, out))).run' σ0] ≤ (0 : ℝ≥0∞) := by
    change Pr[accept | do
      let challenges ← sampleChallenges ([] : ProtocolSpec)
      (simulateQ impl (do
        let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
          ([] : ProtocolSpec) prover challenges
        let verResult ← ((fun stmt _ => (pure stmt : OptionT (OracleComp oSpec) S)) stmtIn tr).run
        return (verResult, out))).run' σ0] ≤ (0 : ℝ≥0∞)
    exact hbound'
  -/

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
  sorry /- WIP proof (references undefined `expJoined`):
  classical
  intro Output prover stmtIn hstmtIn σ0 hσ0
  letI : ChallengesSampleable (pSpec₁ ++ pSpec₂) :=
    ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
  let accept : Option S → Prop := fun o => ∃ s ∈ lang, o = some s
  let p₁ : Prover (OracleComp oSpec) (Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ :=
    Prover.splitPrefix (m := OracleComp oSpec) (Output := Output) pSpec₁ prover
  let stage₁Run (ch₁ : Challenges pSpec₁) :
      StateT σ ProbComp (Transcript pSpec₁ × Prover (OracleComp oSpec) Output pSpec₂) :=
    simulateQ impl (Prover.run (m := OracleComp oSpec)
      (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ ch₁)
  let stage₂Run (p₂ : Prover (OracleComp oSpec) Output pSpec₂)
      (ch₂ : Challenges pSpec₂) :
      StateT σ ProbComp (Transcript pSpec₂ × Output) :=
    simulateQ impl (Prover.run (m := OracleComp oSpec)
      (Output := Output) pSpec₂ p₂ ch₂)
  let v₁Run (tr₁ : Transcript pSpec₁) : StateT σ ProbComp (Option S) :=
    simulateQ impl ((v₁ stmtIn tr₁).run)
  let v₂Run (mid : S) (tr₂ : Transcript pSpec₂) : StateT σ ProbComp (Option S) :=
    simulateQ impl ((v₂ mid tr₂).run)
  let expOrig : ProbComp (Option S) := do
    let ch₁ ← sampleChallenges pSpec₁
    let ch₂ ← sampleChallenges pSpec₂
    let z₁ ← (stage₁Run ch₁).run σ0
    let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
    let zmid ← (v₁Run z₁.1.1).run z₂.2
    match zmid.1 with
    | none => pure none
    | some mid => (v₂Run mid z₂.1.1).run' zmid.2
  have hExpOrig :
      Pr[accept | expOrig] =
      Pr[accept | do
        let ch ← sampleChallenges (pSpec₁ ++ pSpec₂)
        (simulateQ impl (do
          let (tr, _out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
            (pSpec₁ ++ pSpec₂) prover ch
          (Verifier.comp v₁ v₂ stmtIn tr).run)).run' σ0] := by
    have hsample : sampleChallenges (pSpec₁ ++ pSpec₂) = do
        let ch₁ ← sampleChallenges pSpec₁
        let ch₂ ← sampleChallenges pSpec₂
        return Challenges.join pSpec₁ pSpec₂ ch₁ ch₂ := rfl
    rw [hsample]
    have hExpEq : expOrig = expJoined := by
      simp [expOrig, expJoined, stage₁Run, stage₂Run, v₁Run, v₂Run, p₁,
        Prover.run_splitPrefix_join, Verifier.comp, Transcript.split_join,
        simulateQ_bind, OptionT.bind, OptionT.run, StateT.run',
        map_eq_bind_pure_comp, bind_assoc]
    rw [hExpEq]
    have hRHS :
        (pSpec₁.sampleChallenges >>= fun x =>
          pSpec₂.sampleChallenges >>= fun x_1 => do
            let a ← (simulateQ impl (Prover.run (m := OracleComp oSpec) (Output := Output)
              (pSpec₁ ++ pSpec₂) prover (Challenges.join pSpec₁ pSpec₂ x x_1))).run σ0
            (fun x => x.1) <$> (simulateQ impl (Verifier.comp v₁ v₂ stmtIn a.1.1).run).run a.2)
          = expJoined := by
      simp [expJoined, Prover.run_splitPrefix_join, Verifier.comp, Transcript.split_join,
        simulateQ_bind, OptionT.bind, OptionT.run, StateT.run',
        map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr (x := sampleChallenges pSpec₁) (fun x => ?_)
      refine bind_congr (x := sampleChallenges pSpec₂) (fun x_1 => ?_)
      refine bind_congr
        (x := (simulateQ impl (Prover.run (m := OracleComp oSpec)
          (Output := Prover (OracleComp oSpec) Output pSpec₂)
          pSpec₁ (Prover.splitPrefix (m := OracleComp oSpec)
            (Output := Output) pSpec₁ prover) x)).run σ0)
        (fun x => ?_)
      refine bind_congr
        (x := (simulateQ impl (Prover.run (m := OracleComp oSpec)
          (Output := Output) pSpec₂ x.1.2 x_1)).run x.2)
        (fun x_2 => ?_)
      change ((simulateQ impl ((liftM (v₁ stmtIn x.1.1)) >>= fun ox =>
        (OptionT.mk (match ox with
          | none => pure none
          | some a => v₂ a x_2.1.1)).run)).run x_2.2 >>= pure ∘ fun x => x.1) = _
      rw [simulateQ_bind]
      simp [liftM, OptionT.run, StateT.run', bind_assoc, map_eq_bind_pure_comp]
    simpa [hRHS]
  have hStateNorm :
      Pr[accept | expOrig] =
      Pr[accept | do
        let ch₁ ← sampleChallenges pSpec₁
        let ch₂ ← sampleChallenges pSpec₂
        let z₁ ← (stage₁Run ch₁).run σ0
        let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
        let mid ← (v₁Run z₁.1.1).run' z₂.2
        match mid with
        | none => pure none
        | some s => (v₂Run s z₂.1.1).run' z₂.2] := by
    unfold expOrig
    refine probEvent_bind_congr ?_
    intro ch₁ hch₁
    refine probEvent_bind_congr ?_
    intro ch₂ hch₂
    refine probEvent_bind_congr ?_
    intro z₁ hz₁
    refine probEvent_bind_congr ?_
    intro z₂ hz₂
    have hzmidState :
        ∀ zmid ∈ support ((v₁Run z₁.1.1).run z₂.2), zmid.2 = z₂.2 :=
      hState₁ stmtIn z₁.1.1 z₂.2
    have hbranch :
        Pr[accept | do
          let zmid ← (v₁Run z₁.1.1).run z₂.2
          match zmid.1 with
          | none => pure none
          | some mid => (v₂Run mid z₂.1.1).run' zmid.2] =
        Pr[accept | do
          let zmid ← (v₁Run z₁.1.1).run z₂.2
          match zmid.1 with
          | none => pure none
          | some mid => (v₂Run mid z₂.1.1).run' z₂.2] := by
      refine probEvent_bind_congr ?_
      intro zmid hsup
      have hzσ : zmid.2 = z₂.2 := hzmidState zmid hsup
      cases zmid with
      | mk m σm =>
          simp at hzσ
          subst hzσ
          cases m <;> simp
    have hrun' :
        Pr[accept | do
          let zmid ← (v₁Run z₁.1.1).run z₂.2
          match zmid.1 with
          | none => pure none
          | some mid => (v₂Run mid z₂.1.1).run' z₂.2] =
        Pr[accept | do
          let mid ← (v₁Run z₁.1.1).run' z₂.2
          match mid with
          | none => pure none
          | some mid => (v₂Run mid z₂.1.1).run' z₂.2] := by
      change Pr[accept | do
        let zmid ← (v₁Run z₁.1.1).run z₂.2
        let mid := zmid.1
        match mid with
        | none => pure none
        | some mid => (v₂Run mid z₂.1.1).run' z₂.2] =
        Pr[accept | do
          let mid ← (v₁Run z₁.1.1).run z₂.2 >>= fun zmid => pure zmid.1
          match mid with
          | none => pure none
          | some mid => (v₂Run mid z₂.1.1).run' z₂.2]
      simp [StateT.run', map_eq_bind_pure_comp, bind_assoc]
    exact hbranch.trans hrun'
  let expSwap : ProbComp (Option S) := do
    let ch₁ ← sampleChallenges pSpec₁
    let z₁ ← (stage₁Run ch₁).run σ0
    let mid ← (v₁Run z₁.1.1).run' z₁.2
    let ch₂ ← sampleChallenges pSpec₂
    let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
    match mid with
    | none => pure none
    | some s => (v₂Run s z₂.1.1).run' z₂.2
  have hSwap :
      Pr[accept | do
        let ch₁ ← sampleChallenges pSpec₁
        let ch₂ ← sampleChallenges pSpec₂
        let z₁ ← (stage₁Run ch₁).run σ0
        let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
        let mid ← (v₁Run z₁.1.1).run' z₂.2
        match mid with
        | none => pure none
        | some s => (v₂Run s z₂.1.1).run' z₂.2] =
      Pr[accept | expSwap] := by
    refine probEvent_bind_congr ?_
    intro ch₁ hch₁
    refine probEvent_bind_congr ?_
    intro ch₂ hch₂
    refine probEvent_bind_congr ?_
    intro z₁ hz₁
    refine probEvent_bind_congr ?_
    intro z₂ hz₂
    have hInv_z₁ : Inv z₁.2 := by
      have hz₁' : z₁ ∈ support ((stage₁Run ch₁).run σ0) := hz₁
      exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
        (oa := Prover.run (m := OracleComp oSpec)
          (Output := Prover (OracleComp oSpec) Output pSpec₂) pSpec₁ p₁ ch₁)
        σ0 hσ0 _ hz₁')
    have hInv_z₂ : Inv z₂.2 := by
      exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
        (oa := Prover.run (m := OracleComp oSpec) (Output := Output) pSpec₂ z₁.1.2 ch₂)
        z₁.2 hInv_z₁ _ hz₂)
    let cont : Option S → ProbComp (Option S) := fun mid =>
      match mid with
      | none => pure none
      | some s => (v₂Run s z₂.1.1).run' z₂.2
    have hcombine :
        Pr[accept | do
          let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
          let mid ← (v₁Run z₁.1.1).run' z₂.2
          cont mid] =
        Pr[accept | do
          let mid ← (v₁Run z₁.1.1).run' z₁.2
          let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
          cont mid] := by
      -- first replace state in `v₁Run` by output-independence, then swap independent draws
      have hfirst :
          Pr[accept | do
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            let mid ← (v₁Run z₁.1.1).run' z₂.2
            cont mid] =
          Pr[accept | do
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            let mid ← (v₁Run z₁.1.1).run' z₁.2
            cont mid] := by
        refine probEvent_bind_congr ?_
        intro z₂' hz₂'
        have hInv_z₂' : Inv z₂'.2 := by
          exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
            (oa := Prover.run (m := OracleComp oSpec) (Output := Output) pSpec₂ z₁.1.2 ch₂)
            z₁.2 hInv_z₁ _ hz₂')
        have hdist' :
            evalDist ((v₁Run z₁.1.1).run' z₂'.2) = evalDist ((v₁Run z₁.1.1).run' z₁.2) :=
          hOut₁ stmtIn z₁.1.1 _ _ hInv_z₂' hInv_z₁
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        refine tsum_congr fun mid => ?_
        have hprob :
            Pr[= mid | (v₁Run z₁.1.1).run' z₂'.2] =
              Pr[= mid | (v₁Run z₁.1.1).run' z₁.2] := by
          simpa [probOutput_def] using congrArg (fun d => d mid) hdist'
        simp [cont, hprob]
      have hsecond :
          Pr[accept | do
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            let mid ← (v₁Run z₁.1.1).run' z₁.2
            cont mid] =
          Pr[accept | do
            let mid ← (v₁Run z₁.1.1).run' z₁.2
            let z₂ ← (stage₂Run z₁.1.2 ch₂).run z₁.2
            cont mid] := by
        simpa [bind_assoc, cont] using
          (probEvent_bind_bind_swap
            (mx := (stage₂Run z₁.1.2 ch₂).run z₁.2)
            (my := (v₁Run z₁.1.1).run' z₁.2)
            (f := fun z₂' mid => cont mid)
            (q := accept))
      exact hfirst.trans hsecond
    simpa [accept, cont, bind_assoc] using hcombine
  have hMainEq : Pr[accept | expOrig] = Pr[accept | expSwap] := hStateNorm.trans hSwap
  let mx : ProbComp ((Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ) := do
    let ch₁ ← sampleChallenges pSpec₁
    let z₁ ← (stage₁Run ch₁).run σ0
    let mid ← (v₁Run z₁.1.1).run' z₁.2
    return (z₁.1.2, mid, z₁.2)
  let my : ((Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ) → ProbComp (Option S) :=
    fun z => do
      let ch₂ ← sampleChallenges pSpec₂
      let z₂ ← (stage₂Run z.1.1 ch₂).run z.2.2
      match z.1.2 with
      | none => pure none
      | some s => (v₂Run s z₂.1.1).run' z₂.2
  have hExpSwapBind : expSwap = mx >>= my := by
    simp [expSwap, mx, my, bind_assoc]
  have hBad₁ :
      Pr[fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
          ¬ (z.1.2 = none ∨ ∃ s, z.1.2 = some s ∧ s ∉ lang) | mx] ≤ (ε₁ : ℝ≥0∞) := by
    let mx₁ : ProbComp (Option S × Prover (OracleComp oSpec) Output pSpec₂) := do
      let ch₁ ← sampleChallenges pSpec₁
      let z₁ ← (stage₁Run ch₁).run σ0
      let mid ← (v₁Run z₁.1.1).run' z₁.2
      return (mid, z₁.1.2)
    have h₁bound :
        Pr[(fun z : Option S × Prover (OracleComp oSpec) Output pSpec₂ => ∃ s ∈ lang, z.1 = some s)
          | mx₁] ≤ (ε₁ : ℝ≥0∞) := by
      have h₁' := h₁ (Output := Prover (OracleComp oSpec) Output pSpec₂) (prover := p₁)
        (stmtIn := stmtIn) hstmtIn σ0 hσ0
      simpa [Verifier.soundnessFromState, mx₁, stage₁Run, v₁Run, p₁, bind_assoc]
        using h₁'
    have hmxMap : mx₁ = (fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
        (z.1.2, z.1.1)) <$> mx := by
      simp [mx₁, mx, bind_assoc, map_eq_bind_pure_comp]
    have hEventEq :
        Pr[(fun z : Option S × Prover (OracleComp oSpec) Output pSpec₂ => ∃ s ∈ lang, z.1 = some s)
          | mx₁] =
        Pr[(fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
          ¬ (z.1.2 = none ∨ ∃ s, z.1.2 = some s ∧ s ∉ lang)) | mx] := by
      rw [hmxMap, probEvent_map]
      rfl
    simpa [hEventEq] using h₁bound
  have hBad₂ :
      ∀ z ∈ support mx,
        (z.1.2 = none ∨ ∃ s, z.1.2 = some s ∧ s ∉ lang) →
        Pr[fun o => ¬ accept o | my z] ≤ (ε₂ : ℝ≥0∞) := by
    intro z hz hp
    rcases hp with hnone | ⟨s, hs, hsNot⟩
    · subst hnone
      simp [my, accept]
    · subst hs
      have hInv_z : Inv z.2.2 := by
        simp only [mx, mem_support_bind_iff] at hz
        rcases hz with ⟨ch₁, hch₁, hz₁⟩
        simp only [mem_support_bind_iff] at hz₁
        rcases hz₁ with ⟨z₁, hz₁, hzmid⟩
        simp only [support_map, Set.mem_image, Prod.exists] at hzmid
        rcases hzmid with ⟨mid, hmid, hzEq⟩
        subst hzEq
        exact (OracleComp.simulateQ_run_preservesInv (impl := impl) (Inv := Inv) hPres
          (oa := Prover.run (m := OracleComp oSpec)
            (Output := Prover (OracleComp oSpec) Output pSpec₂)
            pSpec₁ p₁ ch₁) σ0 hσ0 _ hz₁)
      have h₂' := h₂ (Output := Output) (prover := z.1.1) (stmtIn := s) hsNot z.2.2 hInv_z
      have hmy :
          Pr[accept | my z] ≤ (ε₂ : ℝ≥0∞) := by
        simpa [Verifier.soundnessFromState, my, v₂Run, stage₂Run, bind_assoc, accept]
          using h₂'
      simpa using hmy
  have hBoundSwap :
      Pr[accept | expSwap] ≤ (ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞) := by
    rw [hExpSwapBind]
    have h := probEvent_bind_le_add (mx := mx) (my := my)
      (p := fun z : (Prover (OracleComp oSpec) Output pSpec₂) × Option S × σ =>
        z.1.2 = none ∨ ∃ s, z.1.2 = some s ∧ s ∉ lang)
      (q := fun o => ¬ accept o)
      hBad₁ hBad₂
    simpa [accept] using h
  have hBoundOrig :
      Pr[accept | expOrig] ≤ (ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞) := by
    simpa [hMainEq] using hBoundSwap
  have hTarget :
      Pr[fun (verResult, _) => ∃ s ∈ lang, verResult = some s | do
        let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
        (simulateQ impl (do
          let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
            (pSpec₁ ++ pSpec₂) prover challenges
          let verResult ← (Verifier.comp v₁ v₂ stmtIn tr).run
          return (verResult, out))).run' σ0] ≤ (ε₁ : ℝ≥0∞) + (ε₂ : ℝ≥0∞) := by
    have hmap :
        Pr[(fun z : Option S × Output => ∃ s ∈ lang, z.1 = some s) | do
          let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
          (simulateQ impl (do
            let (tr, out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
              (pSpec₁ ++ pSpec₂) prover challenges
            let verResult ← (Verifier.comp v₁ v₂ stmtIn tr).run
            return (verResult, out))).run' σ0] =
        Pr[accept | do
          let challenges ← sampleChallenges (pSpec₁ ++ pSpec₂)
          (simulateQ impl (do
            let (tr, _out) ← Prover.run (m := OracleComp oSpec) (Output := Output)
              (pSpec₁ ++ pSpec₂) prover challenges
            (Verifier.comp v₁ v₂ stmtIn tr).run)).run' σ0] := by
      simp [accept, probEvent_map, map_eq_bind_pure_comp, bind_assoc]
    exact (hmap.trans_le (by simpa [hExpOrig] using hBoundOrig))
  simpa using hTarget
  -/

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
