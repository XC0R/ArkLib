/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.OracleReduction.Completeness
import ArkLib.OracleReduction.Basic
import VCVio.OracleComp.Coercions.Append
import ArkLib.Data.Misc.Basic

set_option maxHeartbeats 400000  -- Increase if needed
set_option profiler true
set_option profiler.threshold 20  -- Show anything taking over 10ms

namespace Binius.BinaryBasefold.QueryPhase

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/
noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR



/-!
### Oracle-Aware Reduction Logic for Query Phase

The query phase uses `OracleAwareReductionLogicStep` because its verifier check involves
oracle queries (querying committed codewords at fiber points).
-/

/-- The oracle-aware reduction logic step for the query phase.

This encapsulates the pure logic of the query phase:
- `verifierCheck`: Runs `verifyQueryPhase` which queries oracles for fiber evaluations
- `verifierOut`: Returns `true` (acceptance) or `false` (rejection)
- `honestProverTranscript`: The honest transcript just receives the challenges
- `proverOut`: The honest prover always outputs `(true, ())` -/
noncomputable def queryPhaseLogicStep :
    OracleAwareReductionLogicStep
      -- oSpec is the base/shared oracle (empty for query phase - no random oracles)
      -- The structure internally uses oSpec ++ₒ ([OracleIn]ₒ ++ₒ [pSpec.Message]ₒ)
      (oSpec := []ₒ)
      (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      (WitIn := Unit)
      (OracleIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleOut := fun _ : Empty => Unit)
      (StmtOut := Bool)
      (WitOut := Unit)
      (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where

  -- Relations
  completeness_relIn := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  completeness_relOut := acceptRejectOracleRel

  -- Verifier (Oracle-Aware): verifierCheck queries oracles and returns StmtOut
  -- Iterates through all γ_repetitions and checks each one
  verifierCheck := fun stmtIn transcript => do
    let challenges := transcript.challenges
    let fold_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0 :=
      challenges ⟨0, by rfl⟩

    for rep in (List.finRange γ_repetitions) do
      let v := fold_challenges rep
      let _ ← checkSingleRepetition 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        v stmtIn stmtIn.final_constant

    return true  -- StmtOut = Bool for QueryPhase

  -- Pure output computation (deterministic)
  verifierOut := fun _stmtIn _transcript => true

  -- Oracle embedding (no output oracles for query phase)
  embed := ⟨Empty.elim, fun a _ => Empty.elim a⟩
  hEq := fun i => Empty.elim i

  -- Honest prover transcript: just receives the challenges
  honestProverTranscript := fun stmtIn _witIn _oStmtIn challenges =>
    FullTranscript.mk1 (challenges ⟨0, by rfl⟩)

  -- Prover output: always outputs (true, ())
  proverOut := fun _stmtIn _witIn _oStmtIn _transcript =>
    ((true, fun i => Empty.elim i), ())

def queryPhaseProverState : Fin (1 + 1) → Type := fun
  | 0 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit
  | 1 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit ×
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩

/-- The oracle prover for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification. -/
noncomputable def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Prover state: tracks (stmtIn, oStmtIn, witIn) and optionally the challenges
  PrvState := queryPhaseProverState 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩  => do
    -- V sends all γ challenges v₁, ..., v_γ
    pure (fun challenges => (stmtIn, oStmtIn, witIn, challenges))

  output := fun ⟨stmtIn, oStmtIn, witIn, challenges⟩ => do
    -- Build the transcript using the logic step's honestProverTranscript
    let transcript := FullTranscript.mk1 (pSpec :=
      pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges)
    -- Delegate to proverOut from the logic step
    pure ((queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).proverOut stmtIn witIn oStmtIn transcript)

/-- The oracle verifier for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification:
- `verifierCheck`: monadic check via `verifyQueryPhase`
- `verifierOut`: pure output computation
- `embed` and `hEq`: oracle embedding from the logic step -/
noncomputable def queryOracleVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where

  verify := fun stmtIn challenges => do
    -- ⊢ OracleComp ([]ₒ ++ₒ ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ ++ₒ [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ)) Bool
    let transcript := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges ⟨0, by rfl⟩)
    let logic := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    let _ ← (logic.verifierCheck stmtIn transcript)
    pure (logic.verifierOut stmtIn transcript)

  -- Use embed and hEq from the logic step
  embed := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed
  hEq := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq

/-- The oracle reduction for the final query phase. -/
noncomputable def queryOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := queryOracleProver 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- The final query round as an `OracleProof` (since it outputs Bool and no oracle statements). -/
noncomputable def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

omit [CharP L 2] [SelectableType L] in
lemma mem_support_queryFiberPoints
    -- The number of oracles in query phase is toCodewordsCount(ℓ) = ℓ/ϑ
    {oraclePositionIdx : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
      f_i_on_fiber ∈
      (simulateQ so ((queryFiberPoints 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oraclePositionIdx v).liftComp
        ([]ₒ ++ₒ ([OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ ++ₒ
          [fun (i : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).MessageIdx) ↦ (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Type ↑i]ₒ)))).support):
    let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨oraclePositionIdx, by simp only [toOutCodewordsCount, Fin.val_last,
        lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩

    ∀ (fiberIndex : Fin (2 ^ ϑ)), f_i_on_fiber.get fiberIndex =
      (oStmtIn k_th_oracleIdx (getFiberPoint 𝔽q β oraclePositionIdx v fiberIndex)) := by

  simp only at h_fiber_mem
  simp only [MessageIdx, simulateQ_liftComp] at h_fiber_mem
  unfold queryFiberPoints at h_fiber_mem
  simp only [bind_pure, simulateQ_vector_mapM] at h_fiber_mem
  unfold queryCodeword at h_fiber_mem

  -- Simplify the simulation through liftComp/liftM
  simp_rw [← simulateQ_liftComp] at h_fiber_mem
  simp only [←liftM_eq_liftComp] at h_fiber_mem

  -- Step 1: Unpack Vector.mapM membership
  rw [mem_support_vector_mapM] at h_fiber_mem
  simp only [←liftM_query_eq_liftM_liftM] at h_fiber_mem
  -- simp only [liftM_eq_liftComp] at h_fiber_honest
  simp only [liftM, monadLift, MonadLift.monadLift] at h_fiber_mem
  conv_rhs at h_fiber_mem =>
    -- Somehow we can't rw if we don't conv_rhs
    rw [simulateQ_simOracle2_lift_liftComp_query_T1]
    dsimp only [instOracleStatementBinaryBasefold]

  simp only [Fin.getElem_fin, Vector.getElem_mk, Array.getElem_finRange, Fin.cast_mk, Fin.eta,
    support_pure, Set.mem_singleton_iff] at h_fiber_mem

  exact h_fiber_mem

/--
Lemma 1 (Safety):
Proves that if `c_k` is the result of `iterated_fold` up to step `k`,
it must match the oracle evaluation at that step (provided by `h_relIn`).
This closes the first `sorry` regarding the safety of the guard in `checkSingleFoldingStep`.
-/
lemma query_phase_consistency_guard_safe
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: c_k is the correct iterated fold value up to this point
    (h_c_k_correct :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ (k := k)
      c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
        (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];)
    )
    -- Hypothesis: We are at a step > 0 where a check actually happens
    (h_k_pos : k.val * ϑ > 0)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
      f_i_on_fiber ∈
      (simulateQ so ((queryFiberPoints 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v).liftComp
        ([]ₒ ++ₒ ([OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ ++ₒ
          [fun (i : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).MessageIdx) ↦ (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Type ↑i]ₒ)))).support) :
  let := k_mul_ϑ_lt_ℓ (k := k)
  c_k = f_i_on_fiber.get (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by

  have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v f_i_on_fiber stmtIn
    oStmtIn () challenges h_fiber_mem
  simp only at h_fiber_val

  rw [h_c_k_correct]
  simp only
  have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
  set destIdx : Fin r := ⟨k.val * ϑ, by omega⟩ with h_destIdx_eq
  conv_rhs => rw [h_fiber_val]

  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency

  -- Now extract the oStmtIn equality at position k
  have h_oStmtIn_k_eq := h_strictOracleFoldingConsistency ⟨k.val, by simp only [toOutCodewordsCount_last,
    Fin.is_lt]⟩

  conv_rhs => rw [h_oStmtIn_k_eq]
  simp only

  have h_point_eq : extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ, by omega⟩ (by simp only; omega) =
      getFiberPoint 𝔽q β k v (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, by omega⟩ ϑ) := by
    -- The key insight: getFiberPoint reconstructs a point in S^i by:
    -- 1. Taking the suffix at i+ϑ
    -- 2. Joining it with the fiber index u (the middle ϑ bits)
    -- 3. Converting back to sDomain
    -- When u = extractMiddleFinMask v i ϑ, this reconstructs exactly the suffix at i

    -- Unfold definitions
    dsimp only [getFiberPoint, getChallengeSuffix, challengeSuffixToFin, extractSuffixFromChallenge]

    -- Both sides use iteratedQuotientMap, so we need to show they're applied to the same element
    -- This requires showing that finToSDomain (joinBits u suffix_fin) = iteratedQuotientMap v
    -- where u = extractMiddleFinMask and suffix_fin comes from the suffix at i+ϑ

    -- For now, we leave this as sorry since it requires deep reasoning about
    -- the relationship between joinBits, sDomainToFin, finToSDomain, and iteratedQuotientMap
    sorry

  rw [h_point_eq]

  rw [polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
        (challenges := stmtIn.challenges) (oStmt := oStmtIn)
        (h_consistency := h_strictOracleFoldingConsistency)]

/--
Lemma 2 (Preservation):
Proves that `checkSingleFoldingStep` computes the correct `iterated_fold` value at step `k+1`.

**Key insight**: This lemma does NOT require `c_k` to be the correct fold value as a hypothesis.
Why? Because `checkSingleFoldingStep` performs a **direct computation** from oracle queries:
  `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`

The output `s'` is computed via `single_point_localized_fold_matrix_form` using:
- Fresh oracle queries to `f^(i)` (the fiber evaluations)
- The folding challenges from position `i` to `i+ϑ`
- The suffix of the challenge `v` starting at `i+ϑ`

The input `c_k` is only used for the guard check (validating consistency when `i > 0`),
but it does NOT affect the computation of the output value `s'`.
-/
lemma query_phase_step_preserves_fold
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L) (s' : L) -- The next state (c_next)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), ()))
    -- Hypothesis: s' is a valid output of the simulated step function
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (h_s'_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let witIn : Unit := ()
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
      s' ∈
      (simulateQ so ((checkSingleFoldingStep 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c_k v stmtIn).liftComp
        ([]ₒ ++ₒ ([OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ ++ₒ
          [fun (i : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).MessageIdx) ↦ (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Type ↑i]ₒ)))).support) :
    let := k_succ_mul_ϑ_le_ℓ (k := k)
    s' = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (k.val + 1) * ϑ)
        (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)) (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];) := by
  -- This is basically due to definition of s'
  -- First, convert h_s'_mem to equality form
  dsimp only [checkSingleFoldingStep] at h_s'_mem
  -- 2. Handle the conditional guard (k > 0 vs k = 0)
  --    In both cases, the core computation (query + fold) is the same.
  have h₁ := k_succ_mul_ϑ_le_ℓ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val + 1) * ϑ, by omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by omega⟩

  split_ifs at h_s'_mem with h_k_pos
  · -- Case k > 0: The guard is present.
    -- **Simplify the monadic structure**
    -- fiber_vec is the vector of fiber evaluations at domain Sˆ{k * ϑ} of (y ∈ Sˆ{(k+1) * ϑ})
    -- Goal s'= fold (f^0)(r_0, ..., r_{(k+1)*ϑ-1})(y)
    simp only
    simp only [guard_eq, bind_pure_comp, liftComp_bind, liftComp_map,
      simulateQ_bind, simulateQ_liftComp, support_bind, Function.comp_apply, simulateQ_map,
      simulateQ_ite, simulateQ_pure, simulateQ_failure, support_map, support_ite, support_pure,
      support_failure, Set.mem_iUnion, Set.mem_image, Set.mem_ite_empty_right,
      Set.mem_singleton_iff, and_true, exists_const, exists_and_left, exists_prop] at h_s'_mem

    rcases h_s'_mem with ⟨fiber_vec, c_k_guard, h_fiber_vec_mem_support, h_s'_eq⟩
    -- h_s'_eq : s' = the evaluation at y of the folded function from fiber_vec
    rw [← simulateQ_liftComp] at h_fiber_vec_mem_support

    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges h_fiber_vec_mem_support

    -- Step 1: Use symmetry of h_s'_eq
    rw [←h_s'_eq]
    dsimp only [getChallengeSuffix] -- extractSuffixFromChallenge  arise here

    have h_destIdx_eq : destIdx.val = k.val * ϑ + ϑ := by
      dsimp only [destIdx]; rw [Nat.add_mul, Nat.one_mul]

  --  iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) (extractSuffixFromChallenge 𝔽q β v ⟨(↑k + 1) * ϑ, ⋯⟩ ⋯)

    set challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val + 1) * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (k := 0)
      (h := by simp only [zero_add, Fin.val_last, k_succ_mul_ϑ_le_ℓ]) with h_challenges_full_defs

    set challenges_mid := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k.val * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (k := 0)
      (h := by simp only [zero_add, Fin.val_last]; omega) with h_challenges_mid_defs

    set challenges_last : Fin ϑ → L := (fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, by simp only [Fin.val_last]; omega⟩) with h_challenges_last_defs

    set y_left := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_left_defs
    set y_right := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_right_defs
    -- -- Step 2: Transform the RHS
    -- Define f_mid directly from oStmtIn k, which is simpler and aligns with fiber_vec.get
    let k_oracle_idx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
    -- Prove that oraclePositionToDomainIndex matches midIdx
    have h_domain_idx_eq : (oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ) (positionIdx := k_oracle_idx)).val = midIdx.val := by
      dsimp only [oraclePositionToDomainIndex, midIdx]
    have h_sDomain_midIdx_eq : sDomain 𝔽q β h_ℓ_add_R_rate midIdx = sDomain 𝔽q β h_ℓ_add_R_rate ⟨(oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ) (positionIdx := k_oracle_idx)).val, by omega⟩ := by
      apply sDomain_eq_of_eq; apply Fin.eq_of_val_eq; rw [h_domain_idx_eq]
    let f_mid : ↥(sDomain 𝔽q β h_ℓ_add_R_rate midIdx) → L :=
      fun x => oStmtIn k_oracle_idx (cast (by rw [h_sDomain_midIdx_eq]) x)

    set fiber_vec_actual_def := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := ϑ) (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by simp only [Nat.add_right_cancel_iff]; rfl)
      (h_destIdx_le := by omega) (f := f_mid)
      (y := y_left) with h_fiber_vec_actual_def

    have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
      dsimp only [fiber_vec_actual_def]; unfold fiberEvaluations
      funext x
      conv_lhs =>
        rw [h_fiber_val x]; dsimp only [getFiberPoint]
        dsimp only [getChallengeSuffix]
      conv_rhs =>
        dsimp only [getFirstOracle]
      dsimp only [f_mid]
      apply OracleStatement.oracle_eval_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oStmtIn := oStmtIn) (j' := k_oracle_idx) (j := ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩) (h_j := by rfl)
      -- ⊢ finToSDomain 𝔽q β h_ℓ_add_R_rate ⟨↑k * ϑ, ⋯⟩ ⋯
      --     ⟨↑(Nat.joinBits x (challengeSuffixToFin 𝔽q β k (extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ + ϑ, ⋯⟩ ⋯))), ⋯⟩ =
      --   cast ⋯ (cast ⋯ (qMap_total_fiber 𝔽q β midIdx ϑ h_destIdx_eq h₁ y x))
      sorry
    rw [h_fiber_vec_get]; dsimp only [fiber_vec_actual_def]

    --   single_point_localized_fold_matrix_form 𝔽q β ⟨↑k * ϑ, ⋯⟩ ϑ ⋯ ⋯ (fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, ⋯⟩)
    --   (extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ + ϑ, ⋯⟩ ⋯) (fiberEvaluations 𝔽q β midIdx ϑ h_destIdx_eq h₁ f_mid y) =
    -- iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
    --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) y
    have h_eq := single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := ϑ) (destIdx := ⟨k * ϑ + ϑ, by omega⟩)
      (h_destIdx := by simp only [Nat.add_right_cancel_iff]; rfl) (h_destIdx_le := by omega) (f := f_mid) (r_challenges := fun j => stmtIn.challenges ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩) (y := y_left)
    conv_lhs => rw [h_eq]

    dsimp only [f_mid]
    -- Now rw the oStmtIn k_oracle_idx into the iterated_fold of f⁽⁰⁾ form
    -- Extract t and strictOracleFoldingConsistencyProp from h_relIn
    dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
      strictfinalSumcheckStepFoldingStateProp] at h_relIn
    simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
    rcases h_relIn with ⟨exists_t_MLP, _⟩
    rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
    dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency

    -- Get the equality for k_oracle_idx: oStmtIn k_oracle_idx = iterated_fold from 0 to k.val * ϑ
    have h_f_mid_eq_iterated_fold := h_strictOracleFoldingConsistency k_oracle_idx
    conv_lhs => rw [h_f_mid_eq_iterated_fold]

    let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    conv_lhs => dsimp only [midIdx]
    conv_lhs => simp only [cast_eq, Fin.val_last]; rw [←fun_eta_expansion]

    conv_lhs =>
      rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
          mul_eq_mul_right_iff]; left; rfl
      )]
    dsimp only [k_oracle_idx]

    -- Step 1: Align steps (k * ϑ + ϑ = (k + 1) * ϑ)
    have h_steps_eq : k.val * ϑ + ϑ = (k.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    conv_lhs =>
      rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
        (steps := k.val * ϑ + ϑ) (steps' := (k.val + 1) * ϑ)
        (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]) (h_destIdx_le := by omega)
        (h_steps_eq_steps' := h_steps_eq)
        (f := f₀) (r_challenges := Fin.append challenges_mid challenges_last)
        (y := y_left)]

    -- Step 2: Align destIdx (⟨k * ϑ + ϑ, ...⟩ = ⟨(k + 1) * ϑ, ...⟩)
    conv_lhs =>
      rw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
        (steps := (k.val + 1) * ϑ)
        (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (destIdx' := ⟨(k.val + 1) * ϑ, by omega⟩)
        (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
        (h_destIdx_le := by omega) (h_destIdx_eq_destIdx' := by apply Fin.eq_of_val_eq; omega)
        (f := f₀)]

    -- Step 3: Align function (f₀ = getFirstOracle)
    have h_f₀_eq_getFirstOracle : f₀ = getFirstOracle 𝔽q β oStmtIn := by
      exact polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
        (challenges := stmtIn.challenges) (oStmt := oStmtIn)
        (h_consistency := h_strictOracleFoldingConsistency)
    conv_lhs => rw [h_f₀_eq_getFirstOracle]

    -- Step 4: Align challenges
    have h_challenges_eq : (fun (cIdx : Fin ((↑k + 1) * ϑ)) => Fin.append challenges_mid challenges_last ⟨cIdx.val, by omega⟩) = challenges_full := by
      funext j
      dsimp only [Fin.append, Fin.addCases, challenges_full, challenges_mid, challenges_last]
      -- dsimp only [chalLeft, chalRight]
      by_cases h : j.val < k.val * ϑ
      · -- Case 1: cId < k_steps, so it's from the first part
        simp only [h, ↓reduceDIte, Fin.castLT_mk]; rfl
      · -- Case 2: cId >= k_steps, so it's from the second part
        dsimp only [getFoldingChallenges]
        simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, Fin.val_last,
          eq_rec_constant]
        congr 1; simp only [Fin.val_last, zero_add, Fin.mk.injEq]; omega
    conv_lhs => rw [h_challenges_eq]
    have h_sDomain_eq : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by omega⟩ = sDomain 𝔽q β h_ℓ_add_R_rate ⟨(↑k + 1) * ϑ, by omega⟩ := by
      apply sDomain_eq_of_eq; apply Fin.eq_of_val_eq; simp only; omega
    -- Step 5: Align points
    have h_y_eq : cast (by rw [h_sDomain_eq]) y_left = y_right := by
      dsimp only [y_left, y_right]
      rw [←extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_idx_eq := by apply Fin.eq_of_val_eq; omega)]
    conv_lhs => rw [h_y_eq]
  · -- Case k = 0: No guard.
    ---------------------------------------------------------------------
    -- First establish that k = 0
    have h_mul_eq_0 : ↑k * ϑ = 0 := by omega
    have h_k_eq_0 : k.val = 0 := by
      by_contra h_ne
      have : k.val > 0 := Nat.pos_of_ne_zero h_ne
      have : k.val * ϑ > 0 := Nat.mul_pos this (Nat.pos_of_neZero ϑ)
      omega
    simp only [h_k_eq_0, zero_mul, zero_add] at h_s'_mem ⊢

    -- **Simplify the monadic structure**
    simp only [bind_pure_comp, map_pure, liftComp_map, simulateQ_map,
      simulateQ_liftComp, support_map, Set.mem_image] at h_s'_mem

    rcases h_s'_mem with ⟨fiber_vec, h_fiber_vec_mem_support, h_s'_eq⟩
    rw [← simulateQ_liftComp] at h_fiber_vec_mem_support

    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges h_fiber_vec_mem_support

    -- Step 1: Use symmetry of h_s'_eq
    rw [←h_s'_eq]

    have h_destIdx_eq : destIdx.val = ϑ := by
      dsimp only [destIdx]; rw [h_k_eq_0, zero_add, one_mul]

  --  iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) (extractSuffixFromChallenge 𝔽q β v ⟨(↑k + 1) * ϑ, ⋯⟩ ⋯)

    let challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val + 1) * ϑ) (i := Fin.last ℓ) stmtIn.challenges
      (k := 0) (h := by simp only [zero_add, Fin.val_last]; omega)
    set y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_def

    -- Step 2: Transform the RHS
    let rhs_to_mat_mul_form := iterated_fold_eq_matrix_form 𝔽q β (i := 0)
      (steps := (k.val + 1) * ϑ) (destIdx := destIdx) (h_destIdx := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by omega) (f := getFirstOracle 𝔽q β oStmtIn) (r_challenges := challenges_full)
    conv_rhs =>
      rw [rhs_to_mat_mul_form]
      dsimp only [localized_fold_matrix_form]

    -- Step 3: Unfold localized form
    conv_rhs => unfold localized_fold_matrix_form

  -- 1. Simplify the index arithmetic for k=0
    --    (k+1)*ϑ becomes ϑ
    simp only [Fin.mk_zero', Fin.val_last]
    -- 2. Unfold your helper definition
    --    This reveals that LHS suffix is exactly the RHS suffix
    dsimp only [getChallengeSuffix]

    set fiber_vec_actual_def := fiberEvaluations 𝔽q β (i := 0) (steps := ϑ) (destIdx := destIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega) (f := getFirstOracle 𝔽q β oStmtIn) (y := y) with hright_def

    have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
      dsimp only [fiber_vec_actual_def]; unfold fiberEvaluations
      funext x
      conv_lhs =>
        rw [h_fiber_val x]; dsimp only [getFiberPoint]
        dsimp only [getChallengeSuffix]
      conv_rhs =>
        dsimp only [getFirstOracle]
      simp only [Fin.mk_zero']
      apply OracleStatement.oracle_eval_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oStmtIn := oStmtIn) (j := ⟨k, by
          simp only [toOutCodewordsCount_last, Fin.is_lt]⟩) (j' := 0) (h_j := by
          simp only [h_k_eq_0, Fin.mk_zero'];)
      sorry

    rw [h_fiber_vec_get]
    -- Step 4: Apply the congruence lemma of single_point_localized_fold_matrix_form

      -- 1. Establish that the step counts are equal
    have h_steps_eq : ϑ = (↑k + 1) * ϑ := by
      simp only [h_k_eq_0, zero_add, one_mul]

    -- 2. Apply the Step Congruence Lemma to the RHS
    --    We rewrite the RHS to use 'ϑ' instead of '(k+1)*ϑ'
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_steps_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := ϑ) (h_steps_eq_steps' := h_steps_eq.symm)]
    have h_challenges_eq :
      (fun (j : Fin ϑ) => stmtIn.challenges ⟨j.val, by simp only [Fin.val_last]; omega⟩)
      = fun (j : Fin ϑ) => challenges_full ⟨j.val, by omega⟩ := by
        funext j
        dsimp only [challenges_full, getFoldingChallenges]
        simp only [Fin.val_last, zero_add]
    conv_lhs => rw [h_challenges_eq]
    have h_sDomain_eq : (sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑k * ϑ + ϑ, by omega⟩)
      = (sDomain 𝔽q β h_ℓ_add_R_rate ⟨(↑k + 1) * ϑ, by omega⟩) := by
      apply sDomain_eq_of_eq; simp only [Fin.mk.injEq]; omega

    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
      dsimp only [destIdx]; simp only [Nat.add_mul, Nat.one_mul])]
    have h_y_eq : y = cast (by rw [h_sDomain_eq]) (extractSuffixFromChallenge 𝔽q β (v := v) (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by simp only [k_succ_mul_ϑ_le_ℓ_₂])) := by
      rw [hy_def]
      rw [extractSuffixFromChallenge_congr_destIdx]
      simp only [Nat.add_mul, Nat.one_mul]
    rw [←h_y_eq]
    dsimp only [fiber_vec_actual_def, fiberEvaluations]
    rw [qMap_total_fiber_congr_steps 𝔽q β (i := 0) (steps := ϑ) (steps' := (↑k + 1) * ϑ)
      (h_steps_eq := h_steps_eq) (y := y)]

/-- Lemma 3 (Completeness):
Proves that the fully folded value (result of `iterated_fold` at `ℓ`)
equals the `final_constant` expected by the statement.
-/
lemma query_phase_final_fold_eq_constant
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (x : L)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: x is the result of folding all the way to ℓ
    (h_x_correct :
      have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
      x = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (ℓ / ϑ) * ϑ)
        (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];)
    ) :
    x = stmtIn.final_constant := by
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn

  -- 2. Extract the existential witnesses
  --    We pull out the polynomial 'a' (let's call it 'poly') and the two proofs (consistency & fold).

  rw [h_x_correct]

  rcases h_relIn with ⟨exists_t_MLP, h_final_oracle_fold_to_constant⟩
  simp only at h_final_oracle_fold_to_constant
  -- h_final_oracle_fold_to_constant : (iterated_fold 𝔽q β ⟨↑(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ, ⋯⟩ ϑ ⋯ ⋯ (getLastOracle 𝔽q β ⋯ oStmtIn)
  --     fun cId ↦ stmtIn.challenges ⟨↑(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ + ↑cId, ⋯⟩) =
  --   fun x ↦ stmtIn.final_constant

  have h_final_oracle_fold_to_const_at_0 := congr_fun h_final_oracle_fold_to_constant 0
  simp only at h_final_oracle_fold_to_const_at_0
  rw [h_final_oracle_fold_to_const_at_0.symm]

  -- ⊢ x =
  --   iterated_fold 𝔽q β ⟨↑(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ, ⋯⟩ ϑ ⋯ ⋯ (getLastOracle 𝔽q β ⋯ oStmtIn)
  --     (fun cId ↦ stmtIn.challenges ⟨↑(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ + ↑cId, ⋯⟩) 0

  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency

  let lastOraclePositionIndex := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  have h_last_oracle_eq_t_evals_folded := h_strictOracleFoldingConsistency lastOraclePositionIndex
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add : (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]

  have h_first_oracle_eq_t_evals_folded := h_strictOracleFoldingConsistency ⟨0, by
    simp only [toOutCodewordsCount_last, Nat.div_pos_iff]; omega⟩

  dsimp only [getFirstOracle]

  have h_getLastOracle_eq : oStmtIn lastOraclePositionIndex =
    getLastOracle (h_destIdx := by rfl) (oracleFrontierIdx := Fin.last ℓ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) := by rfl
  rw [←h_getLastOracle_eq]
  rw [h_last_oracle_eq_t_evals_folded, h_first_oracle_eq_t_evals_folded]
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod]

  have h_zero_mod : 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ = 0 := by
    rw [toOutCodewordsCount_last];
    simp only [Nat.zero_mod, zero_mul]

  rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
    mul_eq_mul_right_iff];
    rw [getLastOraclePositionIndex_last];
    dsimp only [lastOraclePositionIndex]
    rw [getLastOraclePositionIndex_last];
    simp only [true_or]
  )]

  set chalLeft := (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)  (challenges := stmtIn.challenges) (k := 0) (ϑ := ℓ/ϑ * ϑ) (by
    simp only [zero_add, Fin.val_last]; omega)) with h_chalLeft
  -- have h_concat_challenges_eq :
  set chalRight := Fin.append (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)  (challenges := stmtIn.challenges) (k := 0) (ϑ := lastOraclePositionIndex.val * ϑ) (by simp only [zero_add, Fin.val_last, oracle_index_le_ℓ]))
      (fun (cId : Fin ϑ) ↦
      stmtIn.challenges ⟨(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ + cId.val, by simp only [Fin.val_last, getLastOraclePositionIndex_last]; simp only [lastBlockIdx_mul_ϑ_add_fin_lt_ℓ]⟩) with h_chalLeft

  have h_chalLeft_eq_chalRight_cast : chalLeft = fun cIdx : Fin (ℓ / ϑ * ϑ) => chalRight ⟨cIdx, by
    dsimp only [lastOraclePositionIndex]
    simp only [getLastOraclePositionIndex_last];
    rw [Nat.sub_mul, Nat.one_mul]; omega
  ⟩ := by
    funext cIdx
    dsimp only [chalLeft, chalRight]
    by_cases h : cIdx.val < lastOraclePositionIndex.val * ϑ
    · -- Case 1: cId < k_steps, so it's from the first part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.coe_castLT, zero_add]
    · -- Case 2: cId >= k_steps, so it's from the second part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      dsimp only [getFoldingChallenges]
      congr 1
      simp only [Fin.val_last, zero_add, Fin.mk.injEq]
      rw [add_comm];
      dsimp only [lastOraclePositionIndex, lastOraclePositionIndex] at ⊢ h
      rw [Nat.sub_add_cancel]
      rw [getLastOraclePositionIndex_last] at ⊢ h
      simp only [Nat.sub_mul, one_mul, not_lt, tsub_le_iff_right] at ⊢ h
      exact h
  rw [h_chalLeft_eq_chalRight_cast]

  conv_lhs =>
    -- 1. Locate the specific sub-term corresponding to the folding function
    --    This finds the lambda "fun y ↦ ..."
    pattern (fun y ↦ iterated_fold _ _ _ _ _ _ _ _ _)
    enter [y]
    rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ) (steps' := 0) (h_destIdx := by simp only [toOutCodewordsCount_last,
      Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod, add_zero]) (h_destIdx_le := by simp only [toOutCodewordsCount_last,
        Nat.zero_mod, zero_mul, zero_le]) (h_steps_eq_steps' := by omega)]
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (h_destIdx := by simp only [toOutCodewordsCount_last,
      Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod])]
  conv_lhs => simp only [cast_cast, cast_eq]; simp only [←fun_eta_expansion]
  conv_lhs =>
    rw [←iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := (ℓ / ϑ * ϑ)) (h_destIdx := by dsimp only [lastOraclePositionIndex]; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega) (h_destIdx_le := by simp only; omega) (h_steps_eq_steps' := by dsimp only [lastOraclePositionIndex]; omega)]

  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) (fun ω => t.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)

  set destIdx' : Fin r := ⟨(getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val + ϑ, by
    rw [getLastOracleDomainIndex]; simp only; omega⟩ with h_destIdx'

  let point := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)

  conv_lhs =>
    rw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩) (destIdx' := destIdx') (h_destIdx := by dsimp only [lastOraclePositionIndex]; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega) (h_destIdx_le := by simp only; omega) (h_destIdx_eq_destIdx' := by dsimp only [destIdx']; simp only [Fin.mk.injEq]; omega) (f := f₀) (r_challenges := chalRight) (y := point)]

  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
    dsimp only [destIdx'];
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff, mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ]) (h_steps_eq_steps' := by omega)]

  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
    dsimp only [destIdx'];
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff, mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ]) (h_steps_eq_steps' := by omega)]

  have h_sDomain_eq : (sDomain 𝔽q β h_ℓ_add_R_rate ⟨ℓ/ϑ * ϑ, by omega⟩)
    = (sDomain 𝔽q β h_ℓ_add_R_rate destIdx') := by
    apply sDomain_eq_of_eq; dsimp only [destIdx']; simp only [Fin.mk.injEq]; omega

  let res := iterated_fold_to_level_ℓ_is_constant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := ⟨t, h_t_mem_support⟩) (destIdx := destIdx') (h_destIdx := by omega) (challenges := fun (cIdx : Fin ℓ) => chalRight ⟨cIdx, by dsimp only [lastOraclePositionIndex]; omega⟩) (x := cast (by rw [h_sDomain_eq]) point) (y := 0)
  rw [res]

/-- Relation used in the forIn loop of `checkSingleRepetition`: at index 0 the folded value is 0;
  at index `oraclePositionIdx > 0` it equals `iterated_fold` up to that position with challenges from
  `stmtIn` and suffix from `v`. -/
@[reducible]
def checkSingleRepetition_foldRel
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  fun oraclePositionIdx val_folded_point =>
    if hk : oraclePositionIdx = 0 then
      val_folded_point = 0  -- Base case: initial value is 0
    else
      have h_toCodewordCount : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ := toOutCodewordsCount_last ℓ ϑ
      have h_le : oraclePositionIdx ≤ ℓ/ϑ := by
        have h := oraclePositionIdx.isLt
        simp only [List.length_finRange] at h
        exact Nat.le_of_lt_succ h
      have h_mul : (ℓ/ϑ) * ϑ = ℓ := by rw [Nat.div_mul_cancel (hdiv.out)]
      have h_mul_le : oraclePositionIdx * ϑ ≤ ℓ := by
        conv_rhs => rw [←h_mul]
        apply Nat.mul_le_mul_right; exact h_le
      let destIdx : Fin r := ⟨oraclePositionIdx * ϑ, by omega⟩
      let suffix_point_from_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v:=v) (destIdx:=destIdx) (h_destIdx_le:=by omega)
      val_folded_point = iterated_fold
        (i := 0) (steps := oraclePositionIdx * ϑ) (destIdx := destIdx) (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
        (h_destIdx_le := by
          rw [←h_mul]
          dsimp only [destIdx];
          apply Nat.mul_le_mul_right; exact h_le
        ) (f := f₀)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega)) (y := suffix_point_from_v)

/--
Safety and Correctness of `checkSingleRepetition` under Honest Simulation.

This lemma proves that for any repetition `rep`, the check:
1. Never fails (safety).
2. Only returns if the accumulated value equals `final_constant`.
-/
lemma checkSingleRepetition_probFailure_eq_zero
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      [⊥ | simulateQ so (checkSingleRepetition 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmtIn stmtIn.final_constant)] = 0 := by

  intro step transcript so v
  let Rel := checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)

  -- 1. Expand definition to expose the `forIn` and `guard`
  dsimp only [checkSingleRepetition]

  -- 2. Distribute simulateQ and liftM over the Bind (>>=)
  --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
  simp only [bind_pure_comp]
  dsimp only [liftM, monadLift, MonadLift.monadLift]
  simp only [Fin.eta, map_pure, bind_pure_comp, liftComp_bind, simulateQ_bind]
  dsimp only [Function.comp_def]
  conv => -- Somehow we have to use this block to replace `probFailure_bind_eq_zero_iff`
      -- since it's not working
    simp only [probFailure_eq_zero_iff, neverFails_bind_iff]
    simp only [←probFailure_eq_zero_iff]

  constructor
  · -- First part: the forIn loop is safe
    -- For this proof, we define a trivial relation since the real invariant
    -- is complex and involves the correctness of folding operations
    -- a. Push liftComp inside the forIn loop (twice, for the two layers)
    --    Goal: simulateQ so (liftComp (liftComp (forIn ...)))
    --    Becomes: simulateQ so (forIn ... (fun x s => liftComp ...))

    rw [liftComp_forIn] -- **Note**: This one actually requires NestedMonadLiftLemmas internally (specifially instMonadLift_left_right in this case)

    -- b. Push simulateQ inside the forIn loop
    --    Goal: simulateQ so (forIn ...)
    --    Becomes: forIn ... (fun x s => simulateQ ...)
    rw [simulateQ_forIn]

    -- **Applying indutive relation inference**
    apply probFailure_forIn_of_relations_simplified (rel := Rel) (h_start := by rfl) (h_step := by
      -- Inductive step: any INNER repetition never fails
      intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c
      -- simp only [List.get_eq_getElem, List.getElem_finRange] at *

      -- Simplify k.succ ≠ 0 (always true)
      have h_succ_ne_zero : k.succ ≠ 0 := Fin.succ_ne_zero k

      constructor
      · -- Part 1: checkSingleFoldingStep is safe (never fails)

        -- where the forInStep.yield has spec `OracleComp [OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ (ForInStep L)`
        -- [⊥|simulateQ so
        --     ((ForInStep.yield <$> checkSingleFoldingStep 𝔽q β ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).liftComp
        --       ([]ₒ ++ₒ
        --         ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ ++ₒ
        --           [fun i ↦ ![Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)] ↑i]ₒ)))] =
        -- 0
        rw [simulateQ_liftComp]
        simp only [map_eq_bind_pure_comp]
        rw [simulateQ_bind, probFailure_bind_eq_zero_iff]
        constructor
        · -- ⊢ [⊥|simulateQ (QueryImpl.lift so) (checkSingleFoldingStep 𝔽q β ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn)] = 0
          dsimp only [checkSingleFoldingStep]
          rw [simulateQ_bind]
          simp only [probFailure_bind_eq_zero_iff]

          constructor
          · -- queryFiberPoints never fails (oracle queries)
            -- ⊢ [⊥|simulateQ (QueryImpl.lift so) (queryFiberPoints 𝔽q β ((List.finRange (ℓ / ϑ)).get k) v)] = 0
            dsimp only [queryFiberPoints, queryCodeword]
            rw [simulateQ_bind]
            simp only [probFailure_eq_zero_iff,
              neverFails_bind_iff, Function.comp_apply, simulateQ_pure, neverFails_pure,
              implies_true, and_true]

            -- 2. Distribute simulateQ over Vector.mapM
            rw [simulateQ_vector_mapM]
            -- rw [probFailure_eq_zero_iff]
            apply neverFails_vector_mapM
            intro u _
            rw [←probFailure_eq_zero_iff]
            simp only [←simulateQ_liftComp]
            -- 1. Unfold 'so' to expose 'simOracle2' so the lemma matches
            dsimp only [so]

            -- 2. Apply the safety preservation lemma
            --    This reduces the goal from "Simulated query is safe"
            --    to "Original query is safe".
            apply probFailure_simulateQ_simOracle2_eq_zero
            -- 3. Prove the original query is safe
            --    A raw 'query' has failure probability 0.
            --    Lifting (lift/liftComp) preserves safety.
            rw [probFailure_liftComp]
            -- ⊢ `[⊥|lift (query ...)] = 0`
            exact probFailure_liftM _
          · -- The guard and pure computation
            intro (f_i_on_fiber : Vector L (2 ^ ϑ)) h_fiber_support
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta] at h_fiber_support

            rw [←simulateQ_liftComp] at h_fiber_support

            split_ifs with h_i_pos
            · -- Case k > 0: guard (c_k = f_i_val)
              -- 1. Simplify failure probability to just the guard condition
              simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
                Fin.coe_cast, guard_eq, Fin.val_last, bind_pure_comp, Function.comp_apply,
                simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure, probFailure_map,
                probFailure_ite, probFailure_pure, probFailure_failure, ite_eq_left_iff,
                one_ne_zero, imp_false, Decidable.not_not]

              -- ⊢ c_k = f_i_on_fiber.get (extractMiddleFinMask ...)
              -- This follows from h_rel_k_c and h_relIn (oracle consistency)
              simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.coe_cast,
                gt_iff_lt, CanonicallyOrderedAdd.mul_pos] at h_i_pos
              -- 1. Construct the correct index type for the lemma
              let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
                have h := k.isLt
                simp only [List.length_finRange] at h
                exact h⟩

              -- 3. Unfold Rel to get the equality
              unfold Rel checkSingleRepetition_foldRel at h_rel_k_c
              have h_k_castSucc_ne_0 : ¬(k.castSucc = 0) := by
                by_contra h_eq
                have h_val_eq := Fin.val_eq_of_eq h_eq
                simp only [Fin.coe_castSucc, Fin.coe_ofNat_eq_mod, List.length_finRange,
                  Nat.zero_mod] at h_val_eq
                have h_k_ne_0 : k.val ≠ 0 := by omega -- from h_i_pos.1
                -- h_val_eq : ↑k = 0
                -- h_k_ne_0 : ↑k ≠ 0
                exact h_k_ne_0 h_val_eq
              rw [dif_neg h_k_castSucc_ne_0] at h_rel_k_c
              simp only [Fin.coe_castSucc] at h_rel_k_c
              -- simp only [Fin.isValue, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
              --   Fin.coe_cast]

              have h_mul_gt_0 : k.val * ϑ > 0 := by
                simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
                exact h_i_pos

              -- 4. Apply the lemma
              exact query_phase_consistency_guard_safe 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k) (f_i_on_fiber := f_i_on_fiber) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := h_rel_k_c) (h_k_pos := h_mul_gt_0) (h_fiber_mem := h_fiber_support)
            · -- Case k = 0: no guard
              simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
                Fin.coe_cast, Fin.val_last, bind_pure_comp, map_pure, Function.comp_apply,
                simulateQ_pure, probFailure_pure]
        · intro x h_x_support_checkSingleFoldingStep
          simp only [MessageIdx, Function.comp_apply, simulateQ_pure, probFailure_pure]

      · -- Part 2: Results in support satisfy the next relation
        intro s' h_s'_support
        simp only [Rel, Fin.succ_ne_zero, ↓reduceDIte, Fin.val_succ]

        simp only [liftComp_map,
          simulateQ_map, support_map, Set.mem_image] at h_s'_support

        -- Extract the actual value from ForInStep.yield
        rcases h_s'_support with ⟨x, h_x_support, h_s'_eq⟩
        rw [←h_s'_eq]
        dsimp only [ForInStep.state]
        -- Handle the index casting issue
        let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
          have h := k.isLt
          simp only [List.length_finRange] at h
          exact h
        ⟩
        -- Apply the preservation lemma
        let res := query_phase_step_preserves_fold 𝔽q β (k := k_idx) (v := v) (c_k := c_k) (s' := x) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn) (challenges := challenges) (h_s'_mem := by
          have h_eq : (List.finRange (ℓ / ϑ)).get k = k_idx := by
            apply Fin.eq_of_val_eq
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.coe_cast]; rfl
          rw [h_eq] at h_x_support
          dsimp only [so] at h_x_support
          dsimp only [pSpecQuery]
          exact h_x_support
        )
        exact res
    )
  · -- Second part: for all x in support, guard (x = final_constant) is safe
    intro x h_x_support
    -- From h_relIn (strictFinalSumcheckRelOut), after all ℓ/ϑ iterations,
    -- the accumulated value equals final_constant
    -- For guard to be safe, we need x = final_constant
    rw [liftComp_forIn, simulateQ_forIn] at h_x_support
    simp only [MessageIdx, map_eq_bind_pure_comp, liftComp_bind, Function.comp_apply, liftComp_pure,
      bind_pure_comp, simulateQ_bind, simulateQ_liftComp, simulateQ_comp_pure_comp] at h_x_support
    simp only [MessageIdx, guard_eq, simulateQ_liftComp, simulateQ_ite, simulateQ_pure,
      simulateQ_failure, probFailure_ite, probFailure_pure, probFailure_failure, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not]

    -- ⊢ x = stmtIn.final_constant
    -- We reuse the SAME relation `Rel` and the SAME logic we used for safety!
    exact query_phase_final_fold_eq_constant 𝔽q β (v := v) (x := x)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (witIn := witIn)
      (h_relIn := h_relIn) (h_x_correct := by
        -- 1. Apply the helper lemma to transport the invariant to the end
      -- h_x_support : x ∈
      --   (forIn (List.finRange (ℓ / ϑ)) 0 fun a b ↦
      --       simulateQ (QueryImpl.lift so) (checkSingleFoldingStep 𝔽q β a b v stmtIn) >>= pure ∘ ForInStep.yield).support

      have h_rel_final : Rel ⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ x := by
        -- Apply the yield-only helper
        let relation_correct_of_mem_support := support_forIn_subset_rel_yield_only (spec := []ₒ) (l := List.finRange (ℓ/ϑ)) (rel := Rel)
          (f := fun k_val r_1 ↦
            simulateQ (QueryImpl.lift so) (checkSingleFoldingStep 𝔽q β k_val r_1 v stmtIn) >>= pure ∘ ForInStep.yield
          )
          (init := 0) (h_start := by rfl) (h_step := by
          simp only [←simulateQ_liftComp]
          intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c iteration_output h_iteration_output_iteration
          -- 1. Unpack support (extract c_next)
          -- simp only [bind_pure_comp, map_pure, support_map, Set.mem_image] at h_iteration_output_iteration
          -- 1. Distribute simulateQ over >>= and pure
          --    This transforms: simulateQ (action >>= pure) -> (simulateQ action) >>= pure
          simp only [Function.comp_apply, support_bind, support_pure, Set.mem_iUnion,
            Set.mem_singleton_iff, exists_prop] at h_iteration_output_iteration

          -- 2. Now the hypothesis is exactly: ∃ c_next, c_next ∈ support ∧ output = yield c_next
          --    Extract it just like before!
          rcases h_iteration_output_iteration with ⟨c_next, h_c_next_mem, h_iteration_output_eq⟩
          rw [h_iteration_output_eq]

          -- simp only [h_iteration_output_eq]
          constructor
          · rfl
          · -- Construct index (Same logic as Part 2)
            let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
              have h := k.isLt
              simp only [List.length_finRange] at h
              exact h
            ⟩
            -- Apply preservation lemma (Exact same syntax as Part 2)
            let res := query_phase_step_preserves_fold 𝔽q β (k := k_idx) (v := v) (c_k := c_k) (s' := c_next) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn) (challenges := challenges) (h_s'_mem := by
              have h_eq : (List.finRange (ℓ / ϑ)).get k = k_idx := by
                apply Fin.eq_of_val_eq
                simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.coe_cast]; rfl
              rw [h_eq] at h_c_next_mem
              -- exact h_c_next_mem
              dsimp only [pSpecQuery]
              exact h_c_next_mem
            )
            exact res
        )
        let res := relation_correct_of_mem_support x h_x_support
        simp only [List.length_finRange] at res
        exact res
      -- 2. Unpack the relation at the final index (ℓ/ϑ)
      unfold Rel checkSingleRepetition_foldRel at h_rel_final
      -- Prove that the final index is not 0
      have h_nonzero : (⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ : Fin (List.length (List.finRange (ℓ / ϑ)) + 1)) ≠ 0 := by
        simp only [ne_eq, Fin.mk_eq_zero, Nat.div_eq_zero_iff, not_or, not_lt]
        constructor
        · have h := Nat.pos_of_neZero (ϑ); omega
        · exact Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
      -- Resolve the "if" statement to the "else" branch
      rw [dif_neg h_nonzero] at h_rel_final
      -- Matches the goal exactly
      exact h_rel_final
    )

/-- **Per-repetition support → logical** (extracted for reuse from completeness-style reasoning).
**Counterpart** of `checkSingleRepetition_probFailure_eq_zero` for the `OracleComp.support` case.

  If `(ForInStep.yield PUnit.unit, state_post)` lies in the support of one iteration of the
  verifier's forIn body (for a given `rep`), then the logical proximity check holds for that
  repetition: `logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.final_constant`.

  **Proof plan:** Same block as in the completeness proof for a single repetition:
  - Unfold `forIn_body` to `simulateQ impl (simulateQ so (liftM (checkSingleRepetition ...) >>= pure (ForInStep.yield ...)))`.
  - Relate support under `impl` to support under `so` (bridge lemma if needed).
  - Use `Rel := checkSingleRepetition_foldRel`, `support_forIn_subset_rel_yield_only` on the inner
    forIn (List.finRange (ℓ/ϑ)), then `query_phase_consistency_guard_safe`, `query_phase_step_preserves_fold`,
    and `query_phase_final_fold_eq_constant` to obtain `logical_checkSingleRepetition`.
  See `mem_support_verify_iff_logical_analysis.md` and `checkSingleRepetition_probFailure_eq_zero`.
-/
lemma logical_checkSingleRepetition_of_mem_support_forIn_body {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmtIn : FinalSumcheckStatementOut)
    (rep : Fin γ_repetitions)
    (state_pre : σ)
    (forIn_body : Fin γ_repetitions → PUnit → StateT σ ProbComp (ForInStep PUnit))
    (h_forIn_body_eq : forIn_body = fun a b =>
      simulateQ impl (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages) do
        liftM (checkSingleRepetition 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a) stmtIn stmtIn.final_constant)
        pure (ForInStep.yield PUnit.unit)))
    (h_mem : ∃ res, res ∈
      OracleComp.support ((forIn_body rep PUnit.unit).run state_pre)) :
    logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.final_constant := by
-- 1. Extract the witness res = (control_flow, state_post)
  rcases h_mem with ⟨⟨res_flow, state_post_single_outer_repetition⟩, h_support⟩
  -- 2. Unfold the body definition
  rw [h_forIn_body_eq] at h_support
  set v := tr.challenges ⟨0, rfl⟩ rep with h_v

  let Rel := checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)

  dsimp only [logical_checkSingleRepetition]

  conv at h_support =>
    -- 1. Expand definition to expose the `forIn` and `guard`
    dsimp only [checkSingleRepetition]
    -- 2. Distribute simulateQ and liftM over the Bind (>>=)
    --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
    simp only [bind_pure_comp]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    simp only [Fin.eta, map_pure, bind_pure_comp, liftComp_bind, simulateQ_bind]
    dsimp only [Function.comp_def]
    simp only [Fin.isValue, id_map',
      guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure, StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]

  obtain ⟨exists_c_last, yield_value_eq⟩ := h_support
  rcases exists_c_last with ⟨c_last, state_post_inner_repetition,
    h_c_last_mem, h_exists_mem_support_guard⟩

  rcases h_exists_mem_support_guard with ⟨_unit_val, mem_support_guard_c_last⟩
  rw [mem_support_stateful_guard_iff] at mem_support_guard_c_last
  rw [simulateQ_forIn] at h_c_last_mem
  rw [simulateQ_forIn_stateful_comp (impl := impl) (l := List.finRange (ℓ / ϑ)) (init := 0)] at h_c_last_mem

  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_ϑ_ge_1 : ℓ/ϑ ≥ 1 := by exact (Nat.one_le_div_iff h_ϑ_pos).mpr h_ϑ_le_ℓ
  have h_0_lt : 0 < (ℓ / ϑ) := by omega
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add : (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]

  -- **Applying indutive relation inference** for the inner `forIn` only
  let Rel' := fun (i : Fin ((List.finRange (ℓ / ϑ)).length + 1)) (c_next : L) (_s : σ) =>
    -- state i => at the end of the inner repetition `i-1`
    -- which means at `i = 0`, value = True since nothing meaningful to check
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) (k := ⟨i - 1, by
      have hi := i.isLt;
      simp only [List.length_finRange] at hi; omega
    ⟩) (v := v) (stmt := stmtIn) (final_constant := stmtIn.final_constant)
    ∧ (
      if hi : i > 0 then
        have hi_lt := i.isLt;
        have hi_lt₂ : i - 1 < ℓ / ϑ := by
          simp only [List.length_finRange] at hi_lt; omega
        let k : Fin (ℓ / ϑ) := ⟨i - 1, by omega⟩
        -- **NOTE**: At the end of repetition `k = i-1`, the value c_next which is the evaluation on `S^{(k+1)*ϑ}` of the folded oracle function must be computed
        -- let point := getChallengeSuffix 𝔽q β (List.finRange (ℓ / ϑ))[↑k] v; fiber_vec.get
        let point := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (k := k)
        let fiber_vec : Fin (2 ^ ϑ) → L := logical_queryFiberPoints 𝔽q β oStmtIn k v

        let output_of_iteration_k : L :=
          (single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k.val * ϑ, by sorry⟩) (steps := ϑ) (destIdx := ⟨k.val * ϑ + ϑ, by sorry⟩) (h_destIdx := by sorry)
          (h_destIdx_le := by sorry)
          (r_challenges := fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, by simp only [Fin.val_last]; sorry⟩)
          (y := point) (fiber_eval_mapping := fiber_vec))
        output_of_iteration_k = c_next
      else True)

  -- inductive relation inference for the intermediate folding steps
  have h_inductive_relations := exists_rel_path_of_mem_support_forIn_stateful.{0} (spec := []ₒ) (l := List.finRange (ℓ / ϑ)) (init := 0) (σ := σ)
    (s := state_pre) (h_mem := h_c_last_mem) (rel := Rel') (h_start := by
      simp only [logical_stepCondition, logical_checkSingleFoldingStep, gt_iff_lt,
        CanonicallyOrderedAdd.mul_pos, tsub_pos_iff_lt, dite_else_true, Fin.val_last,
        Fin.coe_ofNat_eq_mod, List.length_finRange, Nat.zero_mod, zero_tsub, h_0_lt, ↓reduceDIte,
        not_lt_zero', false_and, zero_mul, Fin.mk_zero', IsEmpty.forall_iff, lt_self_iff_false,
        zero_add, and_self, Rel'];
    )
    (h_step := by
      intro k (c_cur : L) (s_curr : σ) h_rel_k
      -- c_cur is the yielded folded value from the previous inner iteration (i.e. k-1)
      intro res_step h_res_step_mem
      have h_k := k.isLt
      simp only [List.length_finRange] at h_k
      have h_k_succ_sub_1_lt : k.succ.val - 1 < ℓ / ϑ := by
        simp only [Fin.val_succ, add_tsub_cancel_right]; omega
      have h_k_sub_1_lt : k.val - 1 < ℓ / ϑ := by sorry
      have h_k_succ_gt_0 : k.succ > 0 := by simp only [gt_iff_lt, Fin.succ_pos]
      dsimp only [Rel', logical_stepCondition] at h_rel_k
      simp only [Fin.coe_castSucc, h_k_sub_1_lt, ↓reduceDIte] at h_rel_k
      -- **Nested simulateQ structure** (do not simp the outer impl):
      -- • Outer: `simulateQ impl (...)` comes from RoundByRound's toFun_full: the reduction runs
      --   the verifier with a stateful oracle impl (black box). We do NOT unfold impl; we only
      --   use that its support equals the spec (support_simulateQ_run'_eq).
      -- • Inner: `simulateQ (QueryImpl.lift (simOracle2 []ₒ oStmtIn tr.messages)) (...)` comes
      --   from OracleVerifier.toVerifier (Basic.lean): the verifier's verify is run with
      --   simOracle2 so oStmtIn and transcript answer the oracle queries. This inner layer
      --   can be simplified further (unfold checkSingleFoldingStep, use simOracle2 lemmas).
      set inner_oa := simulateQ (QueryImpl.lift (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages))
        (ForInStep.yield <$> checkSingleFoldingStep 𝔽q β ((List.finRange (ℓ / ϑ)).get k) c_cur v stmtIn)
      have h_run'_supp_eq := support_simulateQ_run'_eq (impl := impl) (oa := inner_oa) (s := s_curr)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      -- res_step ∈ (run s).support → res_step.1 ∈ (run' s).support = inner_oa.support
      have h_fst_mem : res_step.1 ∈ ((simulateQ impl inner_oa).run' s_curr).support := by
        simp only [StateT.run', support_map, Set.mem_image]
        exact ⟨res_step, h_res_step_mem, rfl⟩
      rw [h_run'_supp_eq] at h_fst_mem
      dsimp only [inner_oa] at h_fst_mem
      dsimp only [Rel', logical_stepCondition]
      dsimp only [checkSingleFoldingStep] at h_fst_mem

      simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.coe_cast,
        gt_iff_lt, CanonicallyOrderedAdd.mul_pos, guard_eq, Fin.val_last, bind_pure_comp,
        LawfulApplicative.map_pure, dite_eq_ite, map_bind, simulateQ_bind, support_bind,
        Function.comp_apply, simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure,
        support_map, support_ite, support_pure, support_failure, Set.mem_iUnion, Set.mem_image,
        exists_prop] at h_fst_mem

      rcases h_fst_mem with ⟨fiber_vec, h_fiber_vec_mem_support, h_c_k_mem_output⟩
      simp only [h_ϑ_pos, and_true] at h_c_k_mem_output

      -- Simplify the simulation through liftComp/liftM
      simp_rw [← simulateQ_liftComp] at h_fiber_vec_mem_support
      simp only [←liftM_eq_liftComp] at h_fiber_vec_mem_support

      have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := ⟨k, h_k⟩) (v := v) (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (witIn := ()) (challenges := tr.challenges)
        (h_fiber_mem := by
          dsimp only [queryPhaseLogicStep]
          have h_transcript : (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).messages = tr.messages := by
            funext j
            -- TODO : prove this
            sorry
          rw [h_transcript]
          exact h_fiber_vec_mem_support
        )
      simp only at h_fiber_val
      have h_fiber_val_eq : fiber_vec.get = fun (fiberIndex : Fin (2 ^ ϑ)) => oStmtIn ⟨k.val, by simp only [toOutCodewordsCount_last]; omega⟩ (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v fiberIndex) := by
        funext fiberIndex
        exact h_fiber_val fiberIndex
      simp only [h_fiber_val] at h_c_k_mem_output
      simp only [h_k_succ_sub_1_lt, h_k_succ_gt_0, ↓reduceDIte] -- get rid of the final_constant `guard` (second branch of logical_stepCondition) since we only care about the intermediate checks
      -- ⊢ logical_checkSingleFoldingStep 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v stmtIn
      dsimp only [logical_checkSingleFoldingStep]
      by_cases h_k_gt_0 : k.val > 0
      · have h_gt : (k.succ.val - 1) * ϑ > 0 := by sorry
        simp only [h_k_gt_0, ↓reduceIte, Set.mem_image, Set.mem_ite_empty_right,
          Set.mem_singleton_iff, and_true, exists_const, existsAndEq] at h_c_k_mem_output
        have h_k_cast_gt_0 : 0 < k.castSucc := by
          sorry
        simp only [gt_iff_lt, h_k_cast_gt_0, ↓reduceDIte, Fin.val_last] at h_rel_k
        simp only [h_gt, ↓reduceDIte]
        simp only [Fin.val_succ, add_tsub_cancel_right]
        -- Goal: LHS = RHS. We have h_c_k_mem_output.1 : b = (RHS as oStmtIn ... getFiberPoint ...).
        conv_rhs => dsimp only [logical_queryFiberPoints];
        have h_V_check_passed := h_c_k_mem_output.1
        dsimp only [logical_queryFiberPoints]
        -- ⊢ logical_computeFoldedValue 𝔽q β ⟨↑k - 1, ⋯⟩ v stmtIn (logical_queryFiberPoints 𝔽q β oStmtIn ⟨↑k - 1, ⋯⟩ v) =
        --   oStmtIn ⟨↑k, ⋯⟩ (getFiberPoint 𝔽q β ⟨↑k, ⋯⟩ v (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, ⋯⟩ ϑ))
        dsimp only [logical_computeFoldedValue, logical_queryFiberPoints]
        constructor
        · -- V check in the current iteration passes
          rw [←h_V_check_passed]
          rw [←h_rel_k.2] -- rw previous computation of c_cur (in previous iteration)
          rfl
        · -- prove equality relation for the output of the current iteration (i.e. c_next)
          have h_yield := h_c_k_mem_output.2
          rw [← h_yield]
          simp only [ForInStep.state]
          rw [h_fiber_val_eq]
          simp only [Nat.add_one_sub_one, Fin.val_last]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
            apply Fin.eq_of_val_eq;
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.coe_cast]
          let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by sorry⟩
          conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            simp only [add_tsub_cancel_right]; dsimp only [destIdx])]
          conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            simp only [List.getElem_finRange, Fin.eta, Fin.coe_cast]; dsimp only [destIdx])]
          congr 1
          -- only challenges equality left
          simp only [Nat.add_one_sub_one, cast_eq]
          dsimp only [getChallengeSuffix]
          apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_idx_eq := by
            simp only [List.getElem_finRange, Fin.eta, Fin.coe_cast]) (h_le := by sorry) (h_le' := by sorry)
      · have h_ne_gt : ¬ ((k.succ.val - 1) * ϑ > 0) := by sorry
        simp only [h_ne_gt, ↓reduceDIte, true_and]
        -- ⊢ single_point_localized_fold_matrix_form 𝔽q β ⟨(↑k.succ - 1) * ϑ, ⋯⟩ ϑ ⋯ ⋯
        --     (fun j ↦ stmtIn.challenges ⟨(↑k.succ - 1) * ϑ + ↑j, ⋯⟩) (getChallengeSuffix 𝔽q β ⟨↑k.succ - 1, ⋯⟩ v)
        --     (logical_queryFiberPoints 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v) =
        --   res_step.1.state
        simp only [h_k_gt_0, ↓reduceIte, Set.mem_singleton_iff, exists_eq_left] at h_c_k_mem_output
        simp only [gt_iff_lt, Fin.val_last] at h_rel_k
        simp only [Fin.val_succ, add_tsub_cancel_right]
        conv_rhs => dsimp only [logical_queryFiberPoints];
        dsimp only [logical_queryFiberPoints]
        have h_yield := h_c_k_mem_output
        rw [← h_yield]
        simp only [ForInStep.state]
        rw [h_fiber_val_eq]
        simp only [Nat.add_one_sub_one, Fin.val_last]
        have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
          apply Fin.eq_of_val_eq;
          simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.coe_cast]
        let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by sorry⟩
        conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          simp only [add_tsub_cancel_right]; dsimp only [destIdx])]
        conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          simp only [List.getElem_finRange, Fin.eta, Fin.coe_cast]; dsimp only [destIdx])]
        congr 1
        -- only challenges equality left
        simp only [Nat.add_one_sub_one, cast_eq]
        dsimp only [getChallengeSuffix]
        apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_idx_eq := by
          simp only [List.getElem_finRange, Fin.eta, Fin.coe_cast]) (h_le := by sorry) (h_le' := by sorry)
    )

  -- extract the final guard relation from h_c_last_mem
  set v_challenge := (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ with h_v_challenge

  intro k
  dsimp only [logical_stepCondition]
  by_cases h_k_lt : ↑k < ℓ / ϑ
  · simp only [h_k_lt, ↓reduceDIte]
    have h_pred_lt : k.val + 1 - 1 < ℓ / ϑ := by omega

    have res := h_inductive_relations.2
    -- 1. Unpack the existence proof
    rcases res with ⟨bs, ss, h_init, h_s_init, h_final_b, h_final_s, h_steps, h_rel_all⟩

    -- 2. Specialize the relation for the 'input' to the k-th iteration
    -- Since k : Fin (ℓ / ϑ), it can be cast into Fin (ℓ / ϑ + 1)
    have h_rel_for_k_th_level_guard := h_rel_all ⟨k + 1, by simp only [List.length_finRange]; omega⟩

    dsimp only [Rel', checkSingleRepetition_foldRel] at h_rel_for_k_th_level_guard

    have h_res := h_rel_for_k_th_level_guard
    simp only [logical_stepCondition, h_pred_lt, ↓reduceDIte, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_res
    -- rw [h_v] at h_res
    exact h_res.1
  · simp only [h_k_lt, ↓reduceDIte]
    --   ⊢ logical_computeFoldedValue 𝔽q β ⟨ℓ / ϑ - 1, ⋯⟩ v stmtIn (logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, ⋯⟩ v) =
    -- stmtIn.final_constant

    have h_last_guard_relation := h_inductive_relations.1.2
    dsimp only [Rel', Rel, checkSingleRepetition_foldRel] at h_last_guard_relation
    simp only [List.length_finRange, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_last_guard_relation
    have h_lt : 0 < (⟨ℓ/ϑ, by simp only [List.length_finRange, lt_add_iff_pos_right,
      zero_lt_one]⟩ : Fin ((List.finRange (ℓ / ϑ)).length + 1)) := by
      sorry
    dsimp only [logical_computeFoldedValue]
    simp only [h_lt, forall_true_left] at h_last_guard_relation
    -- mem_support_guard_c_last : c_last = stmtIn.final_constant ∧ state_post_single_outer_repetition = state_post_inner_repetition
    rw [mem_support_guard_c_last.1.symm]
    rw [h_last_guard_relation.symm]

    simp only [Fin.val_last]
    let destIdx : Fin r := ⟨(ℓ / ϑ - 1) * ϑ + ϑ, by sorry⟩
    set fiber_vec := logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v with h_fiber_vec_def
    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
      simp only [List.length_finRange]; dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    congr 1
    -- only challenges equality left
    simp only [cast_eq]
    dsimp only [getChallengeSuffix]
    apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_idx_eq := by
      simp only [List.length_finRange]) (h_le := by sorry) (h_le' := by sorry)

/-- Main lemma connecting verifier support to logical proximity checks.
    This is the key lemma used in toFun_full of queryKnowledgeStateFunction.

    The left side matches the hypothesis from StateT.run characterization:
      (stmtOut, oStmtOut) ∈ support ((fun x ↦ x.1) <$> simulateQ impl (Verifier.run ...) s)

    The right side gives us:
      1. stmtOut = true
      2. oStmtOut = mkVerifierOStmtOut ...
      3. ∀ rep, logical_checkSingleRepetition ... (the proximity checks spec)
-/
lemma logical_consistency_checks_passed_of_mem_support_V_run {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem_V_run_support :
      (stmtOut, oStmtOut) ∈ OracleComp.support
      ((fun x ↦ x.1) <$> simulateQ impl (Verifier.run (stmtIn, oStmtIn) tr
        (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier) s)):
    (stmtOut = true ∧
     oStmtOut = OracleVerifier.mkVerifierOStmtOut
       (embed := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed)
       (hEq := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq) oStmtIn tr ∧
     ∀ (rep : Fin γ_repetitions),
       logical_checkSingleRepetition 𝔽q β oStmtIn
         (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.final_constant) := by
  conv at h_mem_V_run_support =>
    dsimp only [Verifier.run, OracleVerifier.toVerifier, queryOracleVerifier]
    dsimp only [queryPhaseLogicStep]
    -- Simplify the `(fun x ↦ x.1) <$> ...` part
    rw [OracleComp.support_map, Set.mem_image]
    -- Group the last two `bind`
    rw [pure_bind]; rw [bind_assoc]; rw [pure_bind]
    -- Distribute `simulateQ` over the `bind`
    rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
    -- Resolve the constant mappings
    simp only [Function.comp_def, simulateQ_pure, pure_bind]
    rw [simulateQ_forIn]
    rw [simulateQ_forIn_stateful_comp (impl := impl)
      (l := List.finRange γ_repetitions) (init := PUnit.unit)]

  rcases h_mem_V_run_support with ⟨x, hx_mem, hx_1_eq_stmtOut_oStmtOut⟩
  -- Expose .run so mem_support_StateT_bind_run (which expects ((ma >>= f).run s).support) matches
  set do_forIn_block := -- this is the whole .verify method of `queryOracleVerifier`, with the simulateQ tucked inside the forIn loop
    (do
      forIn (List.finRange γ_repetitions) PUnit.unit fun a b ↦
      simulateQ impl
        (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages) do
          liftM (checkSingleRepetition 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
            stmtIn stmtIn.final_constant)
          pure (ForInStep.yield PUnit.unit))
      pure true)

  set forIn_bind_mkVerifierOut : StateT σ ProbComp (Bool × (Empty → Unit)) := do_forIn_block >>= (fun (x : Bool) ↦ pure (x, OracleVerifier.mkVerifierOStmtOut (embed := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed) (hEq := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq) oStmtIn tr))
  have h_x_mem_eq : x ∈ OracleComp.support (forIn_bind_mkVerifierOut.run s) := hx_mem
  rw [mem_support_StateT_bind_run] at h_x_mem_eq -- now show the existence of the member of support of the forIn block

  rcases h_x_mem_eq with ⟨y, s', h_y_s'_mem_support_forIn_block, h_x_eq⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h_x_eq
  -- do_forIn_block = (forIn ...) >>= fun _ => pure true; unpack to get (z, s') ∈ support (forIn.run s)
  rw [mem_support_StateT_bind_run] at h_y_s'_mem_support_forIn_block
  rcases h_y_s'_mem_support_forIn_block with ⟨z, s'', h_forIn_run_mem, h_pure⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h_pure
  obtain ⟨rfl, rfl⟩ := h_pure

  set forIn_body := fun (a : Fin γ_repetitions) (b : PUnit) =>
    simulateQ impl (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages) do
      liftM (checkSingleRepetition 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a) stmtIn stmtIn.final_constant)
      pure (ForInStep.yield PUnit.unit))

  -- 1. Apply the extraction lemma
  have h_independent_support_mem_exists := exists_path_of_mem_support_forIn_unit.{0} (spec := []ₒ) (l := List.finRange γ_repetitions) (f := forIn_body) (s_init := s) (s_final := s') (u := PUnit.unit) (h_mem := h_forIn_run_mem)

  set γ_challenges : Fin γ_repetitions →
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ := tr.challenges ⟨0, rfl⟩
  rw [h_x_eq] at hx_1_eq_stmtOut_oStmtOut
  rw [Prod.mk_inj] at hx_1_eq_stmtOut_oStmtOut
  constructor
  · exact hx_1_eq_stmtOut_oStmtOut.1.symm
  · constructor
    · exact hx_1_eq_stmtOut_oStmtOut.2.symm
    · -- 2. Quantify over an arbitrary repetition
      intro rep
      -- ⊢ logical_checkSingleRepetition 𝔽q β oStmtIn (γ_challenges rep) stmtIn stmtIn.final_constant
      have h_rep_th_support_mem := h_independent_support_mem_exists rep (by simp only [List.mem_finRange])
      rcases h_rep_th_support_mem with ⟨state_pre_repetition, state_post_repetition, h_support_rep_ith_iteration⟩
      exact logical_checkSingleRepetition_of_mem_support_forIn_body 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions) (σ := σ) (impl := impl) (oStmtIn := oStmtIn) (tr := tr) (stmtIn := stmtIn) (rep := rep) (state_pre := state_pre_repetition) (forIn_body := forIn_body) (h_forIn_body_eq := rfl) (h_mem := by
        use (ForInStep.yield PUnit.unit, state_post_repetition)
      )

/-- Strong completeness for the query phase logic step.

This proves that for any valid input satisfying `strictFinalSumcheckRelOut`,
the verifier check succeeds with probability 1, and the output satisfies
`acceptRejectOracleRel` (i.e., the statement is `true`). -/
theorem queryPhaseLogicStep_isStronglyComplete :
    (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  intro stmtIn witIn oStmtIn challenges h_relIn

  let f₀ := getFirstOracle 𝔽q β oStmtIn
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let step := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

  -- 1. Generate the Honest Transcript (Deterministic given challenges)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges

  -- 2. Define the honest oracle simulator
  -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) oSpec
  -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- We need to prove:
  -- 1. [⊥ | verifierCheck ...] = 0  (never fails)
  -- 2. [fun b => b = true | verifierCheck ...] = 1  (always returns true)
  -- 3. completeness_relOut holds
  -- 4-5. Prover and verifier agree

  -- Prove safety: verifier check never fails
  have h_guards_pass : [⊥ | simulateQ so (step.verifierCheck stmtIn transcript)] = 0 := by
    -- Unfold the definitions
    dsimp only [step, queryPhaseLogicStep]

    -- 2. Push simulation inside the 'bind' structure
    -- simulateQ (do a <- x; b) = do a <- simulateQ x; simulateQ b
    simp only [simulateQ_bind]
    rw [probFailure_bind_eq_zero_iff]
    -- [⊥|simulateQ so (forIn ...)] = 0 ∧ (∀ x ∈ (simulateQ so (forIn ...)).support, ...))
    conv => -- Simp away the second term (which is simulateQ of pure)
      enter [2]
      simp only [Function.comp_apply, simulateQ_pure, probFailure_pure, implies_true]
    rw [and_true]

    -- 3. Now we are at the outer loop (forIn γ_repetitions).
    -- Push simulateQ inside the loop using the lemma that `simulateQ distributes over the loop structure`
    rw [simulateQ_forIn]

    -- NOW apply the safety lemma
    -- The goal is: [⊥ | forIn ... (fun ... ↦ simulateQ so ...)] = 0
    apply probFailure_forIn_eq_zero_of_body_safe
    intro rep h_rep_mem s_rep

    -- 4. Push simulation inside the inner logic
    simp only [simulateQ_bind]
    rw [probFailure_bind_eq_zero_iff]
    conv =>
      enter [2]
      simp only [bind_pure_comp, map_pure, Function.comp_apply, simulateQ_pure, probFailure_pure, implies_true]
    rw [and_true]

    -- ⊢ [⊥|simulateQ so (liftM (checkSingleRepetition 𝔽q β (transcript.challenges ⟨0, ⋯⟩ rep) stmtIn stmtIn.final_constant))] =
    --   0
    apply checkSingleRepetition_probFailure_eq_zero (h_relIn := h_relIn)

  exact ⟨h_guards_pass, rfl, rfl, rfl⟩

/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp))
  (hInit : init.neverFails) :
  OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
 -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSafe := by simp only [probFailure_eq_zero_iff, IsEmpty.forall_iff, implies_true])
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
    -- Step 2: Convert probability 1 to universal quantification over support
  intro stmtIn oStmtIn witIn h_relIn
  simp only [probEvent_eq_one_iff]

  -- -- Step 3: Unfold protocol definitions
  dsimp only [queryOracleProof, queryOracleReduction, queryOracleProver, queryOracleVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]

  let step := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  let strongly_complete : step.IsStronglyCompleteUnderSimulation := by apply queryPhaseLogicStep_isStronglyComplete

-- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- ⊢ [⊥| do
    --   let challenge ← getChallenge          -- (A) V samples v ← B_{ℓ+R}
    --   let receiveChallengeFn ← pure (...)               -- (B) P receives challenge (pure, never fails)
    --   let __discr ← proverOut ...           -- (C) P computes output (pure, never fails)
    --   let verifierStmtOut ← simulateQ ...   -- (D) V runs verifierCheck ← THIS IS THE KEY
    --       do
    --         let _ ← liftM verifierCheck     -- The guards live here!
    --         pure verifierOut
    --   pure (...)
    -- ] = 0

    -- Step 1: Peel off the safe layers
    -- For each layer:
    --   A: neverFails_getChallenge or neverFails_query
    --   B: neverFails_pure
    --   C: neverFails_pure (after liftComp)

    -- 1.A Handle the `let challenge ← getChallenge`
    simp only [probFailure_bind_eq_zero_iff] -- split `A`
    conv =>
      enter [1]; dsimp only [ProtocolSpec.getChallenge];
      simp only [ChallengeIdx, Fin.isValue, Challenge, Matrix.cons_val_zero, liftComp_query,
        SubSpec.liftM_query_eq_liftM_liftM, liftM_append_right_eq, probFailure_liftM]
    rw [true_and]
    intro chal h_chal_support

    -- 1.B Handle the `let receiveChallengeFn ← pure (...)`
    conv =>
      enter [1]; simp only [ChallengeIdx, Fin.isValue, Challenge, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, liftComp_pure, probFailure_pure]
    rw [true_and]
    intro h_receiveChallengeFn h_receiveChallengeFn_support

    -- 1.C Handle the `let __discr ← proverOut ...`
    -- Note: Use simp instead of rw to avoid typeclass diamond issues with FiniteRange instances
    simp only [probFailure_liftComp]
    split;
    simp only [probFailure_pure, ChallengeIdx, liftComp_pure, support_pure,
      Set.mem_singleton_iff, MessageIdx, Fin.isValue, bind_pure_comp, simulateQ_map,
      Functor.map_map, probFailure_map, probFailure_eq_zero_iff, liftComp_map, support_map,
      OracleComp.support_liftComp, Set.mem_image, exists_and_right, Bool.exists_bool, Prod.mk.eta,
      implies_true, and_true, forall_eq, true_and]
    rw [←probFailure_eq_zero_iff]

    -- Apply the simulateQ safety lemma
    -- Can't apply probFailure_simulateQ_simOracle2_eq_zero here
    have h_logic := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecQuery] at hj
        cases j using Fin.cases
        case zero => exact chal
        case succ j' => exact j'.elim0
      )
    have h_transcript_eq : FullTranscript.mk1 ((FullTranscript.mk1 chal).challenges ⟨0, by rfl⟩) =
      FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions) chal := by
      rfl
    rw [h_transcript_eq]
    exact h_logic.1
  -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
  · intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only

    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [
      support_bind, support_pure, liftComp_support,
      Set.mem_iUnion, Set.mem_singleton_iff,
      exists_eq_left, exists_prop, Prod.exists
    ] at hx_mem_support

    -- Step 2b: Extract the challenge r1 and the trace equations
    let h_trace_support := hx_mem_support

    rcases h_trace_support with ⟨chal, chal_mem_support, prvStmtOut_support,
      prvOStmtOut_support, prvWitOut_support, h_prv_def_support, vStmtOut_support,
      vOracleOut_support, h_ver_def_support, h_total_eq_support⟩

    -- Step 2d: From `h_total_eq_support`, we have that the
      -- **output data of prover & verifier are equal to the corresponding support data**
    simp only [Prod.mk_inj] at h_total_eq_support
    rcases h_total_eq_support with ⟨⟨h_prv_stmtOut_eq_support, h_prv_oracle_eq_support⟩,
      ⟨h_ver_stmtOut_eq_support, h_ver_oracle_eq_support⟩, h_wit_eq_support⟩

    obtain ⟨VStmtOut_computed, h_VStmtOut_computed_mem_support,
      h_ver_def_support_eq⟩ := h_ver_def_support
    -- Key: show i = verifierOut (which is true)
    have h_VStmtOut_computed_eq_true : VStmtOut_computed = true := by
      -- The computation is: do let _ ← verifierCheck; pure verifierOut
      -- verifierOut is defined as true in queryPhaseLogicStep
      simp only [MessageIdx, Fin.isValue, bind_pure_comp, simulateQ_map, support_map, Set.mem_image,
        exists_and_right, Bool.exists_bool] at h_VStmtOut_computed_mem_support
      exact h_VStmtOut_computed_mem_support.2.symm

    -- Extract **concrete equalities for the verifier's output support data**
    simp only [h_VStmtOut_computed_eq_true, Prod.mk.injEq] at h_ver_def_support_eq

    -- Extract **concrete equalities for the prover's output support data**
    dsimp only [queryPhaseLogicStep] at h_prv_def_support
    simp only [Prod.mk_inj] at h_prv_def_support
    rcases h_prv_def_support with ⟨⟨h_prv_logic_stmt, h_prv_logic_oracle⟩, h_prv_logic_wit⟩

    rcases h_ver_def_support_eq with ⟨h_ver_stmtOut_eq, h_ver_OstmtOut_eq⟩

    -- Step 2e: Apply the logic completeness lemma
    have h_logic := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecQuery] at hj
        cases j using Fin.cases
        case zero => exact chal
        case succ j' => exact j'.elim0
      )

    obtain ⟨h_V_check_neverFails, h_relOut, h_agree_stmtOut, h_agree_oracleOut⟩ := h_logic

    -- Step 2g: Rewrite all variables to their concrete values
    rw [
      h_ver_stmtOut_eq_support, h_ver_stmtOut_eq,
      h_ver_oracle_eq_support,  h_ver_OstmtOut_eq,
      -- h_wit_eq_support,         h_prv_logic_wit, -- not used since both are `True`
      h_prv_stmtOut_eq_support, h_prv_logic_stmt,
      h_prv_oracle_eq_support,  -- h_prv_logic_oracle
    ]

    -- Step 2h: Complete the proof using logic properties
    constructor
    · -- relOut holds
      exact h_relOut
    · -- Prover and verifier agree
      constructor
      · exact h_agree_stmtOut  -- Statement agreement
      · exact h_agree_oracleOut  -- Oracle agreement

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

def queryKStateProp (m : Fin (1 + 1))
  (tr : ProtocolSpec.Transcript m
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
  (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (witMid : Unit)
  (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as last KState of finalSumcheck reduction (= relIn)
    Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β
      (input := ⟨⟨stmtIn, oStmtIn⟩, witMid⟩)
  | ⟨1, _⟩ => -- After V sends γ challenges: proximity tests must pass
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ :=
      tr.challenges ⟨0, rfl⟩
    let fold_challenges := stmtIn.challenges
    logical_proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (γ_repetitions := γ_repetitions) (γ_challenges := γ_challenges)
      (final_constant := stmtIn.final_constant) (oStmt := oStmtIn) (stmt := stmtIn)

/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ)
    γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    queryKStateProp 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmtIn:=stmtIn) (witMid:=witMid) (oStmtIn:=oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_V_to_P_eq_P_to_V] at hDir
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩

  -- h_output_mem is about support of the StateT computation
    -- Use StateT.support characterization
    simp only [StateT.run, support_bind, Set.mem_iUnion] at h_output_mem_V_run_support

    -- This should expose the structure: ∃ init_value, init_value ∈ init.support ∧ ...
    rcases h_output_mem_V_run_support with ⟨(s : σ), hs_init, h_output_mem_V_run_support_with_s⟩

    -- Apply the main lemma connecting verifier support to logical proximity checks
    have h_res := logical_consistency_checks_passed_of_mem_support_V_run
      (impl := impl) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (tr := tr)
      (s := s) (stmtOut := stmtOut) (oStmtOut := oStmtOut)
      (h_mem_V_run_support := h_output_mem_V_run_support_with_s)
    -- The lemma gives us:
    exact h_res.2.2

/-- **Single Repetition Proximity Check Bound (Proposition 4.23)**

For a single repetition of the proximity check, the probability that a non-compliant
oracle (not close to RS codeword) passes the fold consistency check is bounded by:
  `(1/2) + 1/(2 * 2^𝓡)`

**Preconditions (from Proposition 4.23 in DG25):**
- `h_not_oracleFoldingConsistent`: At least one oracle is non-compliant
- `h_no_bad_event`: No bad folding events occurred (Definition 4.19)

This is the fundamental proximity testing bound used in the soundness proof. -/
theorem prop_4_23_singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ badEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- Delegates to Soundness Prop 4.23 (Lemma 4.25 supplies the query-rejection property).
  have h_res :=
    (Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_consistent := h_not_oracleFoldingConsistent)
      (h_no_bad := h_no_bad_event)
      (h_le := by
        apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)))
  dsimp only [queryRbrKnowledgeError_singleRepetition]
  conv_rhs => simp only [ENNReal.coe_add];
  rw [←ENNReal.coe_div_of_NNReal (a := 1) (b := (2 * 2^𝓡))]
  exact h_res

theorem singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ badEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- This is Proposition 4.23 (DG25) specialized to a single repetition.
  simpa using
    (prop_4_23_singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_oracleFoldingConsistent := h_not_oracleFoldingConsistent)
      (h_no_bad_event := h_no_bad_event))

open Classical in
/-- Round-by-round knowledge soundness for the oracle verifier (query phase).

**Proof Strategy (RBR Extraction Failure Event):**

The RBR extraction failure event is: `¬ KState(0) ∧ KState(1)`, i.e.,
  - `¬ finalSumcheckRelOutProp` (KState 0 = FALSE), AND
  - `proximityChecksSpec` (KState 1 = TRUE)

By De Morgan's law:
  `¬ finalSumcheckRelOutProp = ¬ (oracleFoldingConsistency ∨ badEvent)`
                             `= ¬ oracleFoldingConsistency ∧ ¬ badEvent`

This means:
  - `¬ oracleFoldingConsistency`: Some oracle is NOT compliant (not close to correct folding)
  - `¬ badEvent`: No bad events detected

**Proposition 4.23 (DG25 - Assuming no bad events):**
If any of the adversary's oracles is not compliant (not close to RS codeword),
then the verifier accepts with at most negligible probability:
  `Pr[V accepts] ≤ ((1/2) + 1/(2 * 2^𝓡))^γ_repetitions`

This is exactly `queryRbrKnowledgeError`. -/
theorem queryOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).rbrKnowledgeSoundness init impl
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  apply OracleReduction.unroll_rbrKnowledgeSoundness (kSF :=  queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
  intro stmtIn_oStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
    (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (i := j) (stmtIn := stmtIn_oStmtIn)
  rw [OracleReduction.probEvent_soundness_goal_unroll_log' (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (P := P) (impl := impl) (prover := prover) (i := j) (stmt := stmtIn_oStmtIn)
    (wit := witIn) (s := initState)]
  have h_j_eq_1 : j = ⟨0, rfl⟩ :=
    match j with
    | ⟨0, h0⟩ => rfl
  subst h_j_eq_1
  conv_lhs => simp only [Fin.isValue, Fin.castSucc_zero];
  rw [OracleReduction.soundness_unroll_runToRound_0_pSpec_1_V_to_P
    (prover := prover) (stmtIn := stmtIn_oStmtIn) (witIn := witIn)]
  simp only [
    bind_pure_comp, liftComp_query, SubSpec.liftM_query_eq_liftM_liftM, liftM_append_right_eq,
    bind_map_left, simulateQ_bind, simulateQ_liftComp, StateT.run'_eq, StateT.run_bind,
    Function.comp_apply, simulateQ_map, simulateQ_query,
    StateT.run_map, map_bind, Functor.map_map]
  rw [probEvent_bind_eq_tsum]
  apply OracleReduction.ENNReal.tsum_mul_le_of_le_of_sum_le_one
  · -- Bound the conditional probability for each transcript
    intro x
    -- rw [OracleComp.probEvent_map]
    simp only [Fin.isValue, Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      Fin.succ_zero_eq_one, probEvent_map]
    dsimp only [Fin.isValue, StateT.run]
    rw [OracleReduction.QueryImpl_append_impl_inr_stateful]
    dsimp only [challengeQueryImpl]
    simp only [ChallengeIdx, Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero,
      StateT.run_monadLift, monadLift_self, bind_pure_comp, probEvent_map]
    rw [OracleComp.probEvent_eq_tsum_ite]
    -- have h_L_eq : [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ.range ⟨0, by rfl⟩ = L := by rfl
    have h_L_inhabited : Inhabited L := ⟨0⟩
    conv_lhs =>
      enter [1, x_1, 2]
      rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr (L := (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))) (x := x_1)]
    dsimp only [Function.comp_apply]
    -- Convert the sum domain from [pSpecFold.Challenge]ₒ.range to L using h_L_eq
    conv_lhs => change (∑' (x_1 : (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))), _)
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr (L := Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) (P := P x.1.1)]
    -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    change Pr_{ let y ← $ᵖ (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[(P x.1.1) y] ≤
      queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, rfl⟩
    -- Factor over independent repetitions using the structure of rbrExtractionFailureEvent
    --
    -- Key observations:
    -- 1. P = rbrExtractionFailureEvent = ∃ witMid : Unit, ¬kSF 0 ... ∧ kSF 1 ...
    -- 2. Since witMid : Unit, the existential is trivial (there's only ())
    -- 3. kSF 1 = logical_proximityChecksSpec = ∀ rep, single_check (challenges rep)
    -- 4. The bound follows from: P y → ∀ rep, single_check (y rep)
    --    So Pr[P y] ≤ Pr[∀ rep, single_check (y rep)] = Pr[single_check c]^γ
    --
    -- Strategy: Use monotonicity of probability, then factor the forall
    obtain ⟨stmtIn, oStmtIn⟩ := stmtIn_oStmtIn

    -- Step 1: Define the single-repetition predicate
    let single_P : ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) → Prop := fun v =>
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtIn v stmtIn stmtIn.final_constant

    -- Case split FIRST: if P is empty, handle directly; otherwise extract preconditions
    by_cases h_P_nonempty : ∃ y, P x.1.1 y
    case neg =>
      -- If no y satisfies P x.1.1 y, then Pr[P x.1.1 _] = 0 ≤ bound trivially
      push_neg at h_P_nonempty
      -- Show Pr[P x.1.1 _] = 0 using that P is never true
      calc Pr_{ let y ← $ᵖ (Fin γ_repetitions →
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[ P x.1.1 y ]
        _ = Pr_{ let y ← $ᵖ (Fin γ_repetitions →
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[ False ] := by
          congr 1; ext y;
          simp only [Fin.isValue, h_P_nonempty, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
            PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, ite_not]
        _ = 0 := by
          simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
            eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte]
        _ ≤ _ := zero_le _
    case pos =>
      -- P is non-empty: extract preconditions from a witness
      obtain ⟨y₀, h_P_y₀⟩ := h_P_nonempty

      -- Step 2: Show P implies the forall form
      have h_P_implies_forall : ∀ y, P x.1.1 y → (∀ rep : Fin γ_repetitions, single_P (y rep)) := by
        intro y h_P
        unfold rbrExtractionFailureEvent at h_P
        rcases h_P with ⟨witMid, h_kSF_false_before, h_kSF_true_after⟩
        unfold queryKnowledgeStateFunction queryKStateProp logical_proximityChecksSpec at h_kSF_true_after
        exact h_kSF_true_after

      -- Step 2b: Extract the preconditions from h_kSF_false_before via De Morgan
      have h_preconditions :
          (¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
            (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
            (stmtOut := stmtIn) (oStmtOut := oStmtIn)) ∧
          (¬ badEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
            (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
            (oStmt := oStmtIn) (challenges := stmtIn.challenges)) := by
        -- Use h_P_y₀ to extract preconditions
        -- First substitute P with its definition
        simp only [P] at h_P_y₀
        unfold rbrExtractionFailureEvent at h_P_y₀
        rcases h_P_y₀ with ⟨witMid, h_kSF_false_before, h_kSF_true_after⟩
        unfold queryKnowledgeStateFunction at h_kSF_false_before
        simp only [Fin.castSucc_zero, queryRbrExtractor] at h_kSF_false_before
        unfold queryKStateProp at h_kSF_false_before
        simp only [Prod.mk.injEq] at h_kSF_false_before
        unfold finalSumcheckRelOutProp finalSumcheckStepFoldingStateProp at h_kSF_false_before
        simp only [Prod.fst, Prod.snd] at h_kSF_false_before
        push_neg at h_kSF_false_before
        exact h_kSF_false_before

      obtain ⟨h_not_consistent, h_no_bad⟩ := h_preconditions

      -- Step 3: Apply monotonicity
      apply le_trans (prob_mono (D := $ᵖ (Fin γ_repetitions →
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))) (P x.1.1)
        (fun y => ∀ rep : Fin γ_repetitions, single_P (y rep)) h_P_implies_forall)

      -- Step 4: Factor independent repetitions
      rw [prob_pow_of_forall_finFun (n := γ_repetitions) (P := single_P)]

      -- Step 5: Bound single repetition using singleRepetition_proximityCheck_bound
      have h_single_repetition_bound :
          Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[ single_P v ] ≤
          queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) :=
        singleRepetition_proximityCheck_bound 𝔽q β stmtIn oStmtIn h_not_consistent h_no_bad

      -- Step 6: Finalize exponential bound
      unfold queryRbrKnowledgeError
      exact ENNReal.pow_le_pow_left h_single_repetition_bound
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply OracleComp.tsum_probOutput_le_one

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
