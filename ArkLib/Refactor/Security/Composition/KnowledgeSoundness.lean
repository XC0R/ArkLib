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

/-! ## RBR Knowledge Soundness → Knowledge Soundness -/

section KnowledgeSoundness

variable {StmtIn WitIn StmtOut WitOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- RBR knowledge soundness implies overall knowledge soundness. The total knowledge
error is bounded by the sum of per-round RBR knowledge errors.

**Proof strategy**: analogous to `rbrSoundness_implies_soundness`
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
  by_cases hStmtIn : ∃ w : WitIn, (stmtIn, w) ∈ relIn
  · have hChoose : (stmtIn, Classical.choose hStmtIn) ∈ relIn :=
      Classical.choose_spec hStmtIn
    let badExp : ProbComp (Option StmtOut × (StmtOut × WitOut) × Option WitIn) := do
      let challenges ← sampleChallenges pSpec
      let σ0 ← init
      let a ← (simulateQ impl (Prover.run pSpec prover challenges)).run σ0
      (fun a_1 => (a_1.1, a.1.2, some (Classical.choose hStmtIn))) <$>
        (simulateQ impl (verifier stmtIn a.1.1)).run a.2
    let badPred : (Option StmtOut × (StmtOut × WitOut) × Option WitIn) → Prop := fun x =>
      (x.1 = some x.2.1.1 ∧ x.2.1 ∈ relOut) ∧
        (x.2.2 = none ∨ ∃ w, x.2.2 = some w ∧ (stmtIn, w) ∉ relIn)
    have hChooseAll : ∀ x : WitIn,
        (some (Classical.choose hStmtIn) : Option WitIn) = some x → (stmtIn, x) ∈ relIn := by
      intro x hx
      injection hx with hEq
      subst hEq
      simpa using hChoose
    have hzero : Pr[badPred | badExp] = 0 := by
      simp only [probEvent_eq_zero_iff, support_bind, support_map, Set.mem_iUnion, Set.mem_image,
        Prod.exists, exists_and_right, exists_prop, not_and, not_or, not_exists, Decidable.not_not,
        and_imp, forall_exists_index, Prod.forall, Prod.mk.injEq, badExp, badPred]
      intro a a1 b b1 ch hch σ0 hσ0 tr stmtOut witOut σ1 hs1 verRes σ2 hs2
        hEqA hEqS hEqW hEqB hEqR hRel
      constructor
      · intro hnone
        cases hEqB.trans hnone
      · intro x hx
        exact hChooseAll x (hEqB.trans hx)
    have hnonneg :
        (0 : ℝ≥0∞) ≤ (Finset.sum Finset.univ rbrKnowledgeError : ℝ≥0) := by
      simp
    simpa [Verifier.knowledgeSoundness, slExtractor, hStmtIn, badPred, badExp] using
      (le_trans (le_of_eq hzero) hnonneg)
  · let ε : ℝ≥0∞ := (Finset.sum Finset.univ rbrKnowledgeError : ℝ≥0)
    let accept : (Option StmtOut × (StmtOut × WitOut)) → Prop :=
      fun z => z.1 = some z.2.1 ∧ z.2 ∈ relOut
    let expPair : σ → ProbComp (Option StmtOut × (StmtOut × WitOut)) := fun σ0 => do
      let z ← (do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (Prover.run pSpec prover challenges)).run σ0)
      let verResult ← (simulateQ impl (verifier stmtIn z.1.1)).run' z.2
      return (verResult, z.1.2)
    have probEvent_exists_rel_eq_optionT :
        ∀ (mxo : ProbComp (Option StmtOut)) (witOut : WitOut),
          Pr[(fun o => ∃ s, o = some s ∧ (s, witOut) ∈ relOut) | mxo] =
            Pr[(fun s => (s, witOut) ∈ relOut) |
              (OptionT.mk mxo : OptionT ProbComp StmtOut)] := by
      intro mxo witOut
      rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
      rw [tsum_option (f := fun o : Option StmtOut =>
        if (∃ s, o = some s ∧ (s, witOut) ∈ relOut) then Pr[= o | mxo] else 0) ENNReal.summable]
      simp [OptionT.probOutput_eq]
    have hσbound : ∀ σ0, Inv σ0 → Pr[accept | expPair σ0] ≤ ε := by
      intro σ0 hσ0
      let mxRun : ProbComp ((Transcript pSpec × (StmtOut × WitOut)) × σ) := do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (Prover.run pSpec prover challenges)).run σ0
      let mx0 : ProbComp (Transcript pSpec × (StmtOut × WitOut)) := do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
      let my : ((Transcript pSpec × (StmtOut × WitOut)) × σ) →
          ProbComp (Option StmtOut × (StmtOut × WitOut)) := fun z => do
        let verResult ← (simulateQ impl (verifier stmtIn z.1.1)).run' z.2
        return (verResult, z.1.2)
      let finalRun : ((Transcript pSpec × (StmtOut × WitOut)) × σ) → Prop := fun z =>
        ∃ witMid,
          ksf.toFun (.last pSpec.length) stmtIn
            (PartialTranscript.ofTranscript z.1.1) witMid
      let final0 : (Transcript pSpec × (StmtOut × WitOut)) → Prop := fun z =>
        ∃ witMid,
          ksf.toFun (.last pSpec.length) stmtIn
            (PartialTranscript.ofTranscript z.1) witMid
      let flip : ChallengeIndex pSpec → (Transcript pSpec × (StmtOut × WitOut)) → Prop := fun i z =>
        ∃ witMid,
          ¬ ksf.toFun i.1.castSucc stmtIn
              (HVector.take i.1.castSucc pSpec z.1)
              (extractor.extractMid i.1 stmtIn
                (HVector.take (i.1 + 1) pSpec z.1) witMid) ∧
            ksf.toFun i.1.succ stmtIn
              (HVector.take (i.1 + 1) pSpec z.1) witMid
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
          · have hNoExtract :
              ¬ ksf.toFun (.last pSpec.length) stmtIn
                (PartialTranscript.ofTranscript z.1.1)
                (extractor.extractOut stmtIn z.1.1 z.1.2.2) := by
              intro hLast
              exact hft ⟨_, hLast⟩
            let verDist : ProbComp (Option StmtOut) :=
              (simulateQ impl (verifier stmtIn z.1.1)).run' z.2
            have hrel_not_gt :
                ¬ (0 <
                  Pr[(fun s => (s, z.1.2.2) ∈ relOut) |
                    (OptionT.mk verDist : OptionT ProbComp StmtOut)]) := by
              intro hgt
              exact hNoExtract (ksf.toFun_full stmtIn z.1.1 z.1.2.2 z.2 hInvz hgt)
            have hrel0 :
                Pr[(fun s => (s, z.1.2.2) ∈ relOut) |
                  (OptionT.mk verDist : OptionT ProbComp StmtOut)] = 0 := by
              exact le_antisymm (le_of_not_gt hrel_not_gt) bot_le
            have hExist0 :
                Pr[(fun verResult =>
                    ∃ s, verResult = some s ∧ (s, z.1.2.2) ∈ relOut) | verDist] = 0 := by
              simpa [probEvent_exists_rel_eq_optionT] using hrel0
            have hacc_le_exist :
                Pr[(fun verResult => verResult = some z.1.2.1 ∧ z.1.2 ∈ relOut) | verDist] ≤
                  Pr[(fun verResult =>
                    ∃ s, verResult = some s ∧ (s, z.1.2.2) ∈ relOut) | verDist] := by
              refine probEvent_mono ?_
              intro verResult _ hacc
              exact ⟨z.1.2.1, hacc.1, by simpa using hacc.2⟩
            have hleft0 :
                Pr[(fun verResult => verResult = some z.1.2.1 ∧ z.1.2 ∈ relOut) | verDist] = 0 := by
              refine le_antisymm ?_ bot_le
              exact le_trans hacc_le_exist (by simp [hExist0])
            have hmy_map :
                Pr[accept | my z] =
                  Pr[(fun verResult => verResult = some z.1.2.1 ∧ z.1.2 ∈ relOut) | verDist] := by
              unfold my accept verDist
              have hp :
                  ((fun z0 : Option StmtOut × (StmtOut × WitOut) =>
                      z0.1 = some z0.2.1 ∧ z0.2 ∈ relOut) ∘
                    (fun a : Option StmtOut × σ => (a.1, z.1.2))) =
                    ((fun verResult : Option StmtOut =>
                        verResult = some z.1.2.1 ∧ z.1.2 ∈ relOut) ∘
                      (fun x : Option StmtOut × σ => x.1)) := by
                funext t
                cases t
                rfl
              simp [hp]
            have hinner0 : Pr[accept | my z] = 0 := by
              rw [hmy_map]
              exact hleft0
            simp [hft, hinner0]
        · have hz0 : Pr[= z | mxRun] = 0 := probOutput_eq_zero_of_not_mem_support hz
          by_cases hft : finalRun z <;> simp [hft, hz0]
      have h_final0_eq_finalRun : Pr[final0 | mx0] = Pr[finalRun | mxRun] := by
        rw [hmx0_eq_mapfst]
        rw [probEvent_map]
        rfl
      have h_final_false_of_noFlip :
          ∀ x : Transcript pSpec × (StmtOut × WitOut),
            (∀ i : ChallengeIndex pSpec, ¬ flip i x) →
            ¬ final0 x := by
        intro x hNoFlip
        let goodAt : (k : Nat) → (hk : k ≤ pSpec.length) → Prop :=
          fun k hk =>
            ∃ witMid : WitMid ⟨k, Nat.lt_succ_of_le hk⟩,
              ksf.toFun ⟨k, Nat.lt_succ_of_le hk⟩ stmtIn
                (HVector.take k pSpec x.1) witMid
        have hfalse_prefix : ∀ k (hk : k ≤ pSpec.length), ¬ goodAt k hk := by
          intro k hkLe
          induction k with
          | zero =>
              intro hgood0
              rcases hgood0 with ⟨wit0, hwit0⟩
              have hRel0 : (stmtIn, cast extractor.eqIn wit0) ∈ relIn :=
                (ksf.toFun_empty stmtIn wit0).mpr hwit0
              exact hStmtIn ⟨cast extractor.eqIn wit0, hRel0⟩
          | succ k ih =>
              have hkLt : k < pSpec.length := Nat.lt_of_succ_le hkLe
              have hkPrev : k ≤ pSpec.length := Nat.le_of_lt hkLt
              have hNoPrev : ¬ goodAt k hkPrev := ih hkPrev
              intro hgoodSucc
              rcases hgoodSucc with ⟨witSucc, hsuccRaw⟩
              let kFin : Fin pSpec.length := ⟨k, hkLt⟩
              have hidxSucc :
                  (⟨k + 1, Nat.lt_succ_of_le hkLe⟩ : Fin (pSpec.length + 1)) = kFin.succ := by
                ext
                simp [kFin]
              let witSucc' : WitMid kFin.succ := cast (congrArg WitMid hidxSucc) witSucc
              have hsucc :
                  ksf.toFun kFin.succ stmtIn
                    (HVector.take (k + 1) pSpec x.1) witSucc' := by
                simpa [witSucc', hidxSucc] using hsuccRaw
              have hidxPrev :
                  (⟨k, Nat.lt_succ_of_le hkPrev⟩ : Fin (pSpec.length + 1)) = kFin.castSucc := by
                ext
                simp [kFin]
              have hNoPrevExtract :
                  ¬ ksf.toFun kFin.castSucc stmtIn
                      (HVector.take k pSpec x.1)
                      (extractor.extractMid kFin stmtIn
                        (HVector.take (k + 1) pSpec x.1) witSucc') := by
                intro hprev
                apply hNoPrev
                refine ⟨cast (congrArg WitMid hidxPrev.symm)
                    (extractor.extractMid kFin stmtIn
                      (HVector.take (k + 1) pSpec x.1) witSucc'), ?_⟩
                simpa [hidxPrev] using hprev
              by_cases hchal : (pSpec.get ⟨k, hkLt⟩).isChallenge = true
              · have hNoFlipK :
                  ¬ (∃ witMid : WitMid kFin.succ,
                      ¬ ksf.toFun kFin.castSucc stmtIn
                          (HVector.take k pSpec x.1)
                          (extractor.extractMid kFin stmtIn
                            (HVector.take (k + 1) pSpec x.1) witMid) ∧
                        ksf.toFun kFin.succ stmtIn
                          (HVector.take (k + 1) pSpec x.1) witMid) := by
                    simpa [flip, kFin] using hNoFlip ⟨kFin, hchal⟩
                exact hNoFlipK ⟨witSucc', hNoPrevExtract, hsucc⟩
              · have hnon : (pSpec.get ⟨k, hkLt⟩).isChallenge = false :=
                  Bool.eq_false_iff.mpr hchal
                have htake := hvector_take_succ_eq_concat (k := k) (hk := hkLt) (tr := x.1)
                have hprev :
                    ksf.toFun kFin.castSucc stmtIn
                      (HVector.take k pSpec x.1)
                      (extractor.extractMid kFin stmtIn
                        (HVector.take (k + 1) pSpec x.1) witSucc') := by
                  have hstep :=
                    ksf.toFun_next kFin hnon stmtIn
                      (HVector.take k pSpec x.1)
                      (HVector.get pSpec x.1 ⟨k, hkLt⟩) witSucc'
                      (by simpa [htake.symm] using hsucc)
                  simpa [htake.symm] using hstep
                exact hNoPrevExtract hprev
        have hlenFalse : ¬ goodAt pSpec.length le_rfl :=
          hfalse_prefix pSpec.length le_rfl
        intro hFinal
        rcases hFinal with ⟨witLast, hLast⟩
        apply hlenFalse
        refine ⟨?_, ?_⟩
        · simpa using witLast
        · have htake_full :
              HVector.take pSpec.length pSpec x.1 =
                PartialTranscript.ofTranscript x.1 :=
            hvector_take_length_eq (tr := x.1)
          simpa [htake_full] using hLast
      have h_final_implies_exists :
          ∀ x : Transcript pSpec × (StmtOut × WitOut),
            final0 x → ∃ i : ChallengeIndex pSpec, flip i x := by
        intro x hxFinal
        by_contra hNone
        push_neg at hNone
        exact (h_final_false_of_noFlip x hNone) hxFinal
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
      have h_each : ∀ i : ChallengeIndex pSpec, Pr[flip i | mx0] ≤ rbrKnowledgeError i := by
        intro i
        simpa [mx0, flip] using h stmtIn prover i σ0 hσ0
      have h_final0_le_sum : Pr[final0 | mx0] ≤ ε := by
        calc
          Pr[final0 | mx0]
              ≤ Pr[(fun x => ∃ i ∈ (Finset.univ :
                Finset (ChallengeIndex pSpec)), flip i x) | mx0] :=
                h_final_le_exists
          _ ≤ Finset.sum Finset.univ (fun i => Pr[flip i | mx0]) :=
                h_union
          _ ≤ Finset.sum Finset.univ (fun i => (rbrKnowledgeError i : ℝ≥0∞)) := by
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
    let f : Challenges pSpec → σ → ProbComp (Option StmtOut × (StmtOut × WitOut)) :=
      fun challenges σ0 => do
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
      have hEq1 :
          Pr[accept | do
            let challenges ← sampleChallenges pSpec
            (f challenges (← init))] =
          Pr[accept | do
            let challenges ← sampleChallenges pSpec
            let σ0 ← init
            f challenges σ0] := by
        simp
      have hEq2 :
          Pr[accept | do
            let challenges ← sampleChallenges pSpec
            let σ0 ← init
            f challenges σ0] =
          Pr[accept | do
            let σ0 ← init
            let challenges ← sampleChallenges pSpec
            f challenges σ0] := by
        simpa using hswap
      have hEq3 :
          Pr[accept | do
            let σ0 ← init
            let challenges ← sampleChallenges pSpec
            f challenges σ0] =
          Pr[accept | do
            let σ0 ← init
            expPair σ0] := by
        simp [expPair, f]
      exact (hEq1.trans (hEq2.trans hEq3)).trans_le hInitBound
    let pairExp : ProbComp (Option StmtOut × (StmtOut × WitOut)) := do
      let challenges ← sampleChallenges pSpec
      (f challenges (← init))
    have hmainTrip :
        Pr[fun z : Option StmtOut × (StmtOut × WitOut) × Option WitIn =>
            (z.1 = some z.2.1.1 ∧ z.2.1 ∈ relOut) ∧
            (z.2.2 = none ∨ ∃ w, z.2.2 = some w ∧ (stmtIn, w) ∉ relIn)
          | (fun z => (z.1, z.2, (none : Option WitIn))) <$> pairExp] ≤ ε := by
      rw [probEvent_map]
      have hp :
          ((fun z : Option StmtOut × (StmtOut × WitOut) × Option WitIn =>
              (z.1 = some z.2.1.1 ∧ z.2.1 ∈ relOut) ∧
              (z.2.2 = none ∨ ∃ w, z.2.2 = some w ∧ (stmtIn, w) ∉ relIn)) ∘
            fun z : Option StmtOut × (StmtOut × WitOut) => (z.1, z.2, (none : Option WitIn)))
            = accept := by
        funext z
        simp [accept]
      rw [hp]
      simpa [pairExp] using hmain
    simpa [slExtractor, hStmtIn, ε, f, pairExp]
      using hmainTrip

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
    (hOut : Verifier.OutputIndependent impl Inv v)
    (hState : Verifier.StatePreserving impl v)
    (hInit : InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).knowledgeSoundness init impl rel rel
      (n * Finset.sum Finset.univ rbrKnowledgeError) := by
  classical
  letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
  let lang : Set S := {s | ∃ w, (s, w) ∈ rel}
  have hRbrSound : rbrSoundness impl lang lang v Inv rbrKnowledgeError :=
    rbrKnowledgeSoundness_implies_rbrSoundness impl h
  have hSound :
      letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
      (v.compNth n).soundness init impl lang lang
        (n * Finset.sum Finset.univ rbrKnowledgeError) :=
    Verifier.soundness_compNth init impl hOut hState hInit hPres hRbrSound n
  let slExtractor : Extractor.Straightline oSpec S W W (pSpec.replicate n) :=
    fun stmtIn _ _ =>
      OptionT.mk <| pure <|
        if hRel : ∃ w : W, (stmtIn, w) ∈ rel then
          some (Classical.choose hRel)
        else
          none
  refine ⟨slExtractor, ?_⟩
  intro stmtIn prover
  let extResult : Option W :=
    if hRel : ∃ w : W, (stmtIn, w) ∈ rel then some (Classical.choose hRel) else none
  let baseComp : ProbComp (Option S × (S × W)) := do
    let challenges ← sampleChallenges (pSpec.replicate n)
    (simulateQ impl (do
      let (tr, out) ← Prover.run (pSpec.replicate n) prover challenges
      let verResult ← ((v.compNth n) stmtIn tr).run
      return (verResult, out))).run' (← init)
  have hOcEq : ∀ challenges,
      (do
        let (tr, proverOut) ← Prover.run (pSpec.replicate n) prover challenges
        let verResult ← ((v.compNth n) stmtIn tr).run
        let extractedWit ← (slExtractor stmtIn proverOut.2 tr).run
        return (verResult, proverOut, extractedWit)
        : OracleComp oSpec _) =
      (fun z => (z.1, z.2, extResult)) <$> (do
        let (tr, out) ← Prover.run (pSpec.replicate n) prover challenges
        let verResult ← ((v.compNth n) stmtIn tr).run
        return (verResult, out)) := by
    intro challenges
    simp only [slExtractor, extResult]
    dsimp only [OptionT.run, OptionT.mk]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  by_cases hStmtIn : ∃ w : W, (stmtIn, w) ∈ rel
  · have hChoose : (stmtIn, Classical.choose hStmtIn) ∈ rel :=
      Classical.choose_spec hStmtIn
    suffices hzero : Pr[fun (verResult, (stmtOut, witOut), extractedWit) =>
        (verResult = some stmtOut ∧ (stmtOut, witOut) ∈ rel) ∧
          (extractedWit.isNone ∨ ∃ w, extractedWit = some w ∧ (stmtIn, w) ∉ rel)
      | do
        let challenges ← sampleChallenges (pSpec.replicate n)
        (simulateQ impl (do
          let (tr, proverOut) ← Prover.run (pSpec.replicate n) prover challenges
          let verResult ← ((v.compNth n) stmtIn tr).run
          let extractedWit ← (slExtractor stmtIn proverOut.2 tr).run
          return (verResult, proverOut, extractedWit))).run' (← init)] = 0 by
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
      subst this; exact hnotRel hChoose
  · have hstmtIn_not_lang : stmtIn ∉ lang := by
      simp only [lang, Set.mem_setOf_eq]; exact hStmtIn
    sorry

end KnowledgeSoundness

end ProtocolSpec
