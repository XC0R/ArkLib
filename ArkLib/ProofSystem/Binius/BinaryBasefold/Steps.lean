/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimulationInfrastructure
import ArkLib.OracleReduction.Completeness
import ArkLib.Data.Probability.Instances

set_option maxHeartbeats 400000  -- Increase if needed
set_option profiler true
set_option profiler.threshold 20  -- Show anything taking over 10ms
namespace Binius.BinaryBasefold.CoreInteraction
/-!
## Binary Basefold single steps
- **Fold step** :
  P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...
  w_{ℓ-i-2})`.
  V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`,
  and sends P `r'_i`.
- **Relay step** : transform relOut of fold step in case of non-commitment round to match
  roundRelation
- **Commit step** :
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
    P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`
- **Final sum-check step** :
  - P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
  - V verifies : `s_ℓ = eqTilde(r, r') * c`
  => `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

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

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

/-- **RBR Extraction Failure Event**: Generic predicate for round-by-round knowledge soundness.

This captures when the RBR extractor fails to produce a valid witness at round `i.1.castSucc`,
but a valid witness exists at round `i.1.succ`. This is the fundamental "bad event" that must
be bounded in all RBR knowledge soundness proofs.

**Usage:** Instantiate with protocol-specific `kSF`, `extractor`, and transcript to get the -/
@[reducible]
def rbrExtractionFailureEvent {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}
  (kSF : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop)
  (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
  (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
  (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i) : Prop :=
  ∃ witMid : WitMid i.1.succ,
    ¬ kSF i.1.castSucc stmtIn transcript
      (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
    kSF i.1.succ stmtIn (transcript.concat challenge) witMid

section FoldStep

/-! ### Helper Lemmas for Fold Step KState Proofs -/

/-- **Lemma 1.1**: Round polynomial from consistent witness sums correctly.
This connects `sumcheckConsistencyProp` to `getSumcheckRoundPoly` evaluation.
Note: `getSumcheckRoundPoly_sum_eq` in Prelude.lean already proves the sum property,
but we need the specific form that connects to our witness structure. -/
lemma roundPoly_eval_sum_of_consistent_witness
    {i : Fin ℓ}
    (stmt : Statement (L := L) Context i.castSucc)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (h_consistent : sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H) :
    let h_star := getSumcheckRoundPoly ℓ 𝓑 i wit.H
    h_star.val.eval (𝓑 0) + h_star.val.eval (𝓑 1) = stmt.sumcheck_target := by
  -- h_consistent says: stmt.sumcheck_target = ∑ x ∈ (univ.map 𝓑)^ᶠ(ℓ - ↑i.castSucc), wit.H.val.eval x
  -- getSumcheckRoundPoly_sum_eq says: h_star(0) + h_star(1) = ∑ x ∈ (univ.map 𝓑)^ᶠ(ℓ - ↑i.castSucc), wit.H.val.eval x
  -- Therefore: h_star(0) + h_star(1) = stmt.sumcheck_target
  intro h_star
  rw [h_consistent]
  exact getSumcheckRoundPoly_sum_eq ℓ 𝓑 i wit.H

/-- **Lemma 1.2a**: Oracle statements preserved through fold step embedding.
For fold step, all oracle indices map via Sum.inl (no new oracles added). -/
lemma foldStep_oracle_unchanged
    (i : Fin ℓ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (transcript : FullTranscript (pSpecFold (L := L))) :
    OracleVerifier.mkVerifierOStmtOut
      (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).embed
      (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).hEq
      oStmtIn transcript = oStmtIn := by
  -- For fold step, embed always maps j ↦ Sum.inl j (identity on indices)
  -- Therefore mkVerifierOStmtOut returns oStmtIn j for all j
  funext j
  let embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).embed
  let hEq := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).hEq
  -- embed j = Sum.inl ⟨j.val, ...⟩ by construction in foldStepLogic
  have hj_bound : j.val < i / ϑ + 1 := by
    have : toOutCodewordsCount ℓ ϑ i.castSucc = i / ϑ + 1 := by simp [toOutCodewordsCount]
    rw [← this]; exact j.isLt
  have h_embed : embed j = Sum.inl ⟨j.val, by omega⟩ := by
    simp only [embed, foldStepLogic, Function.Embedding.coeFn_mk]
    split
    · rfl
    · omega
  rw [OracleVerifier.mkVerifierOStmtOut_inl embed hEq oStmtIn transcript j _ h_embed]
  rfl

/-! ### End of Helper Lemmas -/

/-- The prover for the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    -- Both stmt and wit advances, but oStmt only advances at the commitment rounds only
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where

  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    -- USE THE SHARED KERNEL (Guarantees match with foldStepLogic)
    let h_i := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
    -- Return message and update state
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  -- | ⟨2, h⟩ => nomatch h -- no challenge after third message

  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let t := FullTranscript.mk2 (pSpec := pSpecFold (L := L)) h_i r_i'
    -- 2. Delegate to Logic Instance
    pure ((foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).proverOut stmt wit oStmt t)

open Classical in
/-- The oracle verifier for the `i`-th round of Binary Foldfold. -/
def foldOracleVerifier (i : Fin ℓ) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (pSpec := pSpecFold (L := L)) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn pSpecChallenges => do
    let h_i ← query (spec := [(pSpecFold (L := L)).Message]ₒ) ⟨0, rfl⟩ ()
    let r_i' := pSpecChallenges ⟨1, rfl⟩

    let t := FullTranscript.mk2 h_i r_i'

    let logic := (foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)

    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  -- Reuse embed and hEq from foldStepLogic to ensure consistency
  embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).embed
  hEq := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).hEq

/-- The oracle reduction that is the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)) where
  prover := foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i
  verifier := foldOracleVerifier 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SelectableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Simplifies membership in a conditional singleton set.
  `x ∈ (if c then {a} else {b})` is equivalent to `x = (if c then a else b)`.
-/
lemma mem_ite_singleton {α : Type*} {c : Prop} [Decidable c] {a b x : α} :
    (x ∈ (if c then {a} else {b} : Set α)) ↔ (x = if c then a else b) := by
  split_ifs with h
  · simp only [Set.mem_singleton_iff] -- Case c is True: x ∈ {a} ↔ x = a
  · simp only [Set.mem_singleton_iff] -- Case c is False: x ∈ {b} ↔ x = b

open Classical in
/--
Perfect completeness for the binary folding oracle reduction.

This theorem proves that the honest prover-verifier interaction for one round of binary folding
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
1. Unroll the 2-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes on honest prover messages
4. For correctness: extract the challenge from the support and apply the logic completeness lemma

**Key Technique:**
- Use `foldStep_is_logic_complete` to get the pure logic properties
- Convert the challenge function by proving the only valid challenge index is 1
- Rewrite all intermediate variables to their concrete values
- Apply the logic properties to complete the proof
-/
theorem foldOracleReduction_perfectCompleteness (hInit : init.neverFails) (i : Fin ℓ)
  [(i : pSpecFold.ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge i)]
  [(i : pSpecFold.ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge i)]
  :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc (mp := mp))
      (relOut := strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i (mp := mp))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
      (init := init)
      (impl := impl) := by
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (hInit := hInit)
    (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSafe := by simp only [probFailure_eq_zero_iff, IsEmpty.forall_iff, implies_true])
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn

  -- Step 2: Convert probability 1 to universal quantification over support
  simp_rw [probEvent_eq_one_iff]

  -- Step 3: Unfold protocol definitions
  dsimp only [foldOracleReduction, foldOracleProver, foldOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk2]

  let step := (foldStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
    -- Step 2e: Apply the logic completeness lemma
  let strongly_complete : step.IsStronglyComplete := foldStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (i := i)

  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff, probFailure_liftComp_eq]
    rw [probFailure_eq_zero_iff]
    simp only [neverFails_pure, true_and]

    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      liftComp_pure, support_pure, Set.mem_singleton_iff] at hInputState_mem_support
    -- Now we get equality: hInputState_mem_support : inputState = (foldProverComputeMsg ...)
    conv => enter [1]; erw [probFailure_liftM]; simp only
    rw [true_and]

    intro r_i' h_r_i'_mem_query_1_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      tactic => split; simp only [neverFails_pure]
    rw [true_and]

    intro h_receive_challenge_fn h_receive_challenge_fn_mem_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      tactic => split; simp only [neverFails_pure]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [probFailure_liftComp]
      simp only

    simp only [
      -- probFailure_liftComp,
      -- probFailure_map,
      -- probFailure_bind_eq_zero_iff,
      probFailure_pure,
      implies_true,
      and_true
    ]
    -- simulateQ_query (q : OracleQuery spec α) : simulateQ so q = so.impl q
    simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
      SubSpec.liftM_query_eq_liftM_liftM, guard_eq, bind_pure_comp, simulateQ_bind, simulateQ_query,
      probFailure_eq_zero_iff, neverFails_bind_iff, Function.comp_apply, simulateQ_map,
      simulateQ_ite, simulateQ_pure, simulateQ_failure, neverFails_map_iff, neverFails_pure,
      neverFails_guard]
    simp only [←probFailure_eq_zero_iff]
    constructor
    · -- the oracle query (to get the message `h_i(X)`)
        -- simulateQ-ed over simOracle2 is safe
      simp only [Fin.isValue, probFailure_simOracle2]
    · intro h_i h_i_mem_oracle_query_support
      -- **Unfold the oracle query logic in h_i**

      -- Step 1: Unfold liftM to expose the structure
      -- simp only [←liftM_query_eq_liftM_liftM] at h_i_mem_oracle_query_support
      simp only [liftM, monadLift, MonadLift.monadLift] at h_i_mem_oracle_query_support
      -- Step 2: NOW apply the lemma inside the support
      conv at h_i_mem_oracle_query_support => rw [simOracle2_impl_inr_inr]
      -- Step 3: Extract equality from singleton support
      simp only [Fin.isValue, Matrix.cons_val_zero, support_pure,
        Set.mem_singleton_iff] at h_i_mem_oracle_query_support
      -- Now: h_i = OracleInterface.answer (messages ⟨0, ...⟩) ()
      rw [h_i_mem_oracle_query_support]
      -- Unfold the actually query, which is getting the message computed by prover
      unfold OracleInterface.answer
      dsimp only [instOracleInterfaceMessagePSpecFold]

      -- Step 2e: Apply the logic completeness lemma
      obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
        (witIn := witIn) (h_relIn := h_relIn) (challenges :=
        fun ⟨j, hj⟩ => by
          match j with
          | 0 =>
            have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
              simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
                Direction.not_P_to_V_eq_V_to_P]
            exfalso
            exact hj_ne hj
          | 1 => exact r_i'
        )
      rw [hInputState_mem_support] -- Convert input States into equality
      exact h_V_check
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only

    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [
      support_bind, support_pure, support_liftComp,
      Set.mem_iUnion, Set.mem_singleton_iff,
      exists_eq_left, exists_prop, Prod.exists
    ] at hx_mem_support

    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvStmtOut_support, prvOStmtOut_support, prvWitOut_support,
      h_prv_def_support, vStmtOut_support, vOracleOut_support,
      h_ver_def_support, h_total_eq_support⟩

    -- Step 2c: Simplify the verifier computation
    conv at h_ver_def_support =>
      rw [simulateQ_bind]
      erw [simulateQ_simOracle2_liftM (oSpec := []ₒ) (t₁ := oStmtIn)]
      erw [simOracle2_impl_inr_inr]
      rw [bind_pure_simulateQ_comp]
      -- Deep simplify the `guard`
      simp only [Matrix.cons_val_zero, guard_eq, bind_pure_comp,
        simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure, support_map, support_ite,
        support_pure, support_failure, Set.mem_image, Set.mem_ite_empty_right,
        Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]

    -- Step 2d: Extract all the equalities
    simp only [Prod.mk_inj] at h_total_eq_support
    rcases h_total_eq_support with ⟨⟨h_prv_stmtOut_eq_support, h_prv_oracle_eq_support⟩,
      ⟨h_ver_stmtOut_eq_support, h_ver_oracle_eq_support⟩, h_wit_eq_support⟩

    dsimp only [foldStepLogic, getFoldProverFinalOutput] at h_prv_def_support
    simp only [Prod.mk_inj] at h_prv_def_support
    rcases h_prv_def_support with ⟨⟨h_logic_stmt, h_logic_oracle⟩, h_logic_wit⟩

    rcases h_ver_def_support with ⟨h_V_check_passed, h_ver_stmtOut_eq, h_ver_OstmtOut_eq⟩
    -- h_V_check_passed exists due to unfolding the `guard` in `foldStepLogic`

    -- Step 2e: Apply the logic completeness lemma
    obtain ⟨_h_V_check_but_not_used, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges := fun ⟨j, hj⟩ => by
        -- Convert single challenge r1 to challenge function
        have h_j_eq_1 : j = 1 := by
          dsimp [pSpecFold] at hj
          cases j using Fin.cases
          case zero => simp at hj
          case succ j1 =>
            cases j1 using Fin.cases
            case zero => rfl
            case succ k => exact k.elim0 (α := k.succ.succ = 1)
        subst h_j_eq_1
        exact r1)

    -- Step 2f: Simplify the verifier check
    dsimp only [foldStepLogic, foldProverComputeMsg, step] at h_V_check_passed
    unfold FullTranscript.mk2 at h_V_check_passed
    simp only [Fin.isValue, Transcript_get_message] at h_V_check_passed

    dsimp only [Fin.isValue, foldProverComputeMsg, foldStepLogic, Challenge,
      Matrix.cons_val_one, Matrix.cons_val_zero, Lean.Elab.WF.paramLet] at h_ver_stmtOut_eq
    unfold FullTranscript.mk2 at h_ver_stmtOut_eq
    unfold OracleInterface.answer at h_ver_stmtOut_eq
    simp only [Fin.isValue, Transcript_get_message, Transcript_get_challenge] at h_ver_stmtOut_eq

    -- Step 2g: Rewrite all variables to their concrete values
    rw [
      h_ver_stmtOut_eq_support, h_ver_stmtOut_eq,
      h_ver_oracle_eq_support,  h_ver_OstmtOut_eq,
      h_wit_eq_support,         h_logic_wit,
      h_prv_stmtOut_eq_support, h_logic_stmt,
      h_prv_oracle_eq_support,  h_logic_oracle
    ]

    -- Step 2h: Complete the proof using logic properties
    constructor
    · exact h_rel
    · constructor
      · rfl  -- Statement agreement
      · exact h_agree.2  -- Oracle agreement

open scoped NNReal

open Classical in
/-- Definition of the per-round RBR KS error for Binary FoldFold.
This combines the Sumcheck error (1/|L|) and the LDT Bad Event probability.
For round i : rbrKnowledgeError(i) = err_SC + err_BE where
- err_SC = 1/|L| (Schwartz-Zippel for degree 1)
- err_BE = (if ϑ ∣ (i + 1) then ϑ * |S^(i+1)| / |L| else 0)
  where k = i / ϑ and |S^(j)| is the size of the j-th domain
-/
def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
  let err_SC := (1 : ℝ≥0) / (Fintype.card L)
  -- bad event of `fⱼ` exists RIGHT AFTER the V's challenge of sumcheck round `j+ϑ-1`,
  -- Question: we don't have new oracle here, how can we work with bad events? potentially incorrect here
  let err_BE := if hi : ϑ ∣ (i.val + 1) then
    -- HERE: we view `i` as `j+ϑ-1`, error rate is `ϑ * |S^(j+ϑ)| / |L| = ϑ * |S^(i+1)| / |L|`
    ϑ * (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i.val + 1, by -- ⊢ ↑i + 1 < r
        omega⟩) : ℝ≥0) / (Fintype.card L)
  else 0
  -- Actually err_BE accounts for knowledge error of the oracle (i-ϑ+1), i.e. looking backward last ϑ challenges
  -- TODO: review the definition of err_BE to match the semantic
  err_SC + err_BE

/-- WitMid type for fold step: Witness i.succ at final round, Witness i.castSucc otherwise.
This allows the extractor to work with the actual output witness type at the final round. -/
def foldWitMid (i : Fin ℓ) : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨1, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨2, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly.

Key design: WitMid at the final round (m=2) is Witness i.succ, matching WitOut.
This allows extractOut to be identity and simplifies toFun_full proofs. -/
noncomputable def foldRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L))
    (WitMid := foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _oStmtIn⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both are Witness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1, i.e., Witness i.succ → Witness i.castSucc
      -- Extract backward using the transcript
      {
        t := witMidSucc.t,
        H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ)
          (t := witMidSucc.t) (m := mp.multpoly stmtIn.ctx)
          (i := i.castSucc) (challenges := stmtIn.challenges),
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witMidSucc.t
          (challenges := stmtIn.challenges)
      }
  -- extractOut is now identity since WitMid (Fin.last 2) = WitOut = Witness i.succ
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-- This follows the KState of sum-check -/
def foldKStateProp {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H)

  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := h_i.val.eval r_i'
    let stmtOut : Statement (L := L) Context i.succ := { -- same as in getFoldProverFinalOutput
      ctx := stmtMid.ctx,
      sumcheck_target := newSumcheckTarget,
      challenges := Fin.snoc stmtMid.challenges r_i'
    }
    let oStmtOut := oStmtMid
    let witOut := witMid
    -- Use OUTPUT state: stmtIdx advances to i.succ, oracleIdx stays at i.castSucc (no new oracle)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        -- we reduce the sumcheck consistency check here
        sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

-- Note: this fold step couldn't carry bad-event errors, because we don't have oracles yet.

/-- Knowledge state function (KState) for single round -/
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).KnowledgeStateFunction init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (extractor := foldRbrExtractor (mp:=mp) (𝓡 := 𝓡) (ϑ := ϑ) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    foldKStateProp (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmtMid := stmtMid) (witMid := witMid) (oStmtMid := oStmtMid)
  toFun_empty := fun _ _ => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    -- For pSpecFold, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Direction.not_V_to_P_eq_P_to_V] at hDir
    subst h_m_eq_0

    intro h_kState_round1
    unfold foldKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]

    -- At round 1: masterKStateProp with (explicitVCheck ∧ localizedRoundPolyCheck)
    -- At round 0: masterKStateProp with sumcheckConsistencyProp
    -- Extract the checks from round 1
    obtain ⟨⟨h_explicit, h_localized⟩, h_core⟩ := h_kState_round1

    -- Use Lemma 1.1 (roundPoly_eval_sum_of_consistent_witness)
    -- Key: h_localized says h_i = h_star, and h_explicit says h_i(0) + h_i(1) = s
    -- Therefore h_star(0) + h_star(1) = s, which is what Lemma 1.1 gives us
    constructor
    · -- Prove sumcheckConsistencyProp at round 0
      simp_rw [h_localized] at h_explicit
      rw [h_explicit.symm]
      apply getSumcheckRoundPoly_sum_eq
    · -- The core (badEventExists ∨ oracleWitnessConsistency) is preserved
      exact h_core
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩

    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [foldOracleVerifier]
      -- dsimp only [StateT.run]
      -- simp only [simulateQ_bind, simulateQ_query, simulateQ_pure]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      -- enter [1, i_1, 2, 1, x]
      rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
      erw [simulateQ_simOracle2_liftM (oSpec := []ₒ) (t₁ := oStmtIn)]
      erw [simOracle2_impl_inr_inr]
      unfold OracleInterface.answer
      dsimp only [instOracleInterfaceMessagePSpecFold]
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure,
        bind_map_left, Function.comp_apply]
      unfold Functor.map
      dsimp only [StateT.instMonad]
      simp only [StateT.map_ite] -- simplify the ite from the `guard`
      -- Collapse the ite structure of the OracleComp.support
      simp only [support_ite,                    -- OracleComp.support_ite (outer layer)
        StateT.support_map_const_pure,  -- handle (StateT.map f (pure ()) i_1).support
        StateT.support_map_failure
      ]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]

    rcases h_output_mem_V_run_support with ⟨init_value, h_init_value_mem_support,
      h_V_check_passed, ⟨h_stmtOut_eq, h_oStmtOut_eq⟩, h_initValue_trivial⟩

    simp only [Fin.reduceLast, Fin.isValue] -- simp the `match`

    dsimp only [foldStepRelOut, foldStepRelOutProp, masterKStateProp] at h_relOut
    simp only [Fin.val_succ, Set.mem_setOf_eq] at h_relOut
    dsimp only [foldKStateProp]
    set h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩ with h_i_def
    set r_i' : L := tr.challenges ⟨1, rfl⟩ with h_i_def

    set extractedWitLast : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ := (foldRbrExtractor 𝔽q β i).extractOut (stmtIn, oStmtIn) tr witOut

    have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by
      rw [h_oStmtOut_eq]
      funext j
      -- ⊢ OracleVerifier.mkVerifierOStmtOut (foldStepLogic 𝔽q β i).embed ⋯ oStmtIn tr j = oStmtIn j
      simp only [foldStepLogic, Prod.mk.eta, Fin.isValue, MessageIdx, Fin.is_lt, ↓reduceDIte,
        Fin.eta, Fin.zero_eta, Fin.mk_one, Function.Embedding.coeFn_mk, Sum.inl.injEq,
        OracleVerifier.mkVerifierOStmtOut_inl, cast_eq]
    have h_stmtOut_challenges_eq : ((Fin.snoc stmtIn.challenges r_i') : Fin (↑i + 1) → L) = stmtOut.challenges := by
      -- use the h_stmtOut_eq to prove this
      rw [h_stmtOut_eq]
      unfold foldStepLogic foldVerifierStmtOut
      simp only [Fin.val_succ, Fin.isValue]
    rw [h_oStmtOut_eq_oStmtIn] at h_relOut
    rw [h_stmtOut_challenges_eq]

    have h_stmtOut_sumcheck_target_eq : stmtOut.sumcheck_target = (Polynomial.eval r_i' ↑h_i) := by
      rw [h_stmtOut_eq]; rfl
    dsimp only [masterKStateProp]
    constructor
    · rw [h_stmtOut_sumcheck_target_eq] at h_relOut
      exact h_relOut.1
    · cases h_relOut.2 with
      | inl hBad =>
        left
        exact hBad
      | inr hConsist =>
        right
        rw [h_stmtOut_eq] at hConsist
        rw [←h_stmtOut_challenges_eq]
        exact hConsist

open Classical in
/-- RBR knowledge soundness for a single round oracle verifier -/
theorem foldOracleVerifier_rbrKnowledgeSoundness (hInit : init.neverFails) (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  apply OracleReduction.unroll_rbrKnowledgeSoundness (kSF := foldKnowledgeStateFunction
    (mp:=mp) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 𝔽q β i)
  intro stmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑) (init := init) (impl := impl) (σ := σ) 𝔽q β i)
    (foldRbrExtractor (mp := mp) 𝔽q β i)
    j
    stmtIn
  rw [OracleReduction.probEvent_soundness_goal_unroll_log' (pSpec := pSpecFold
    (L := L)) (P := P) (impl := impl) (prover := prover) (i := j) (stmt := stmtIn)
    (wit := witIn) (s := initState)]
  have h_j_eq_1 : j = ⟨1, rfl⟩ := by
    match j with
    | ⟨0, h0⟩ => nomatch h0
    | ⟨1, _⟩ => rfl
  subst h_j_eq_1
  conv_lhs => simp only [Fin.isValue, Fin.castSucc_one];
  rw [OracleReduction.soundness_unroll_runToRound_1_P_to_V_pSpec_2
    (pSpec := pSpecFold (L := L)) (prover := prover) (hDir0 := rfl)]
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
    have h_L_eq : [(pSpecFold (L := L)).Challenge]ₒ.range ⟨1, by rfl⟩ = L := by rfl
    have h_L_inhabited : Inhabited L := ⟨0⟩
    conv_lhs =>
      enter [1, x_1, 2]
      rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr (L := L) (x := x_1)]
    dsimp only [Function.comp_apply]
    -- Convert the sum domain from [pSpecFold.Challenge]ₒ.range to L using h_L_eq
    conv_lhs => change (∑' (x_1 : L), _)
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr (L := L) (P := P (FullTranscript.mk1 x.1.1))]
    -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    change Pr_{ let y ← $ᵖ L }[ P (FullTranscript.mk1 x.1.1) y ] ≤
      foldKnowledgeError 𝔽q β i ⟨1, by rfl⟩
    sorry
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply OracleComp.tsum_probOutput_le_one

end FoldStep
section CommitStep

def commitPrvState (i : Fin ℓ) : Fin (1 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  | ⟨1, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

def getCommitProverFinalOutput (i : Fin ℓ)
    (inputPrvState : commitPrvState (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 0) :
  (↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩) → L) ×
  commitPrvState (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 1 :=
  let (stmtIn, oStmtIn, witIn) := inputPrvState
  let fᵢ_succ := witIn.f
  let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (oStmtIn := oStmtIn) (newOracleFn := fᵢ_succ) (h_destIdx := by rfl)
    -- The only thing the prover does is to sends f_{i+1} as an oracle
  (fᵢ_succ, (stmtIn, oStmtOut, witIn))

/-- The prover for the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where

  PrvState := commitPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun inputPrvState => by
    let res := getCommitProverFinalOutput 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i inputPrvState
    exact pure res

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction

  output := fun ⟨stmt, oStmt, wit⟩ => by
    exact pure ⟨⟨stmt, oStmt⟩, wit⟩

/-- The oracle verifier for the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn _pSpecChallenges => do
    pure stmtIn

  embed := (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i hCR).embed
  hEq := (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i hCR).hEq

/-- The oracle reduction that is the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleReduction (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  prover := commitOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  verifier := commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i hCR

variable {R : Type} [CommSemiring R] [DecidableEq R] [SelectableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/--
Perfect completeness for the commit step oracle reduction.

This theorem proves that the honest prover-verifier interaction for the commit step
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
The proof follows the same pattern as `foldOracleReduction_perfectCompleteness`:
1. Unroll the 1-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes (trivial - no verification)
4. For correctness: apply the logic completeness lemma

**Key Difference from Fold Step:**
- No challenges (1-message protocol)
- No verification check
- Just extends the oracle with the new function
-/
theorem commitOracleReduction_perfectCompleteness (hInit : init.neverFails) (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i)
    [(j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Fintype ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)]
    [(j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Inhabited ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)] :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (oracleReduction := commitOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i hCR)
      (init := init)
      (impl := impl) := by
  -- Step 1: Unroll the 1-message reduction
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSafe := by simp only [probFailure_eq_zero_iff, IsEmpty.forall_iff, implies_true])
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn

  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]

  -- Step 3: Unfold protocol definitions
  simp only [commitOracleReduction, commitOracleProver, commitOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk1]

  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff, probFailure_liftComp_eq]
    rw [probFailure_eq_zero_iff]
    simp only [neverFails_pure, true_and]

    intro inputState hInputState_mem_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      tactic => split; simp only [neverFails_pure]
    rw [true_and]

    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [
        probFailure_liftComp,
        probFailure_map,
        probFailure_bind_eq_zero_iff,
        probFailure_pure,
        implies_true,
        and_true
      ]
    rw [simulateQ_pure, probFailure_pure]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [
      support_bind, support_pure, support_liftComp,
      Set.mem_iUnion, Set.mem_singleton_iff,
      exists_eq_left, exists_prop, Prod.exists
    ] at hx_mem_support

    -- Step 2b: Extract the trace equations
    let h_trace_support := hx_mem_support
    rcases h_trace_support with ⟨prvStmtOut_support, prvOStmtOut_support, prvWitOut_support,
      h_prv_def_support, vStmtOut_support, vOracleOut_support, h_ver_def_support, h_total_eq_support⟩

    -- Step 2c: Simplify the verifier computation
    conv at h_ver_def_support =>
      rw [simulateQ_pure, support_pure]
      simp only [Set.mem_singleton_iff]
      simp only [Prod.mk.injEq, exists_eq_left]

    -- Step 2d: Extract all the equalities
    simp only [Prod.mk_inj] at h_total_eq_support
    rcases h_total_eq_support with ⟨⟨h_prv_stmtOut_eq_support, h_prv_oracle_eq_support⟩,
      ⟨h_ver_stmtOut_eq_support, h_ver_oracle_eq_support⟩, h_wit_eq_support⟩

    dsimp only [commitStepLogic, getCommitProverFinalOutput] at h_prv_def_support
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h_prv_def_support
    rcases h_prv_def_support with ⟨⟨h_logic_stmt, h_logic_oracle⟩, h_logic_wit⟩

    rcases h_ver_def_support with ⟨h_ver_stmtOut_eq, h_ver_OstmtOut_eq⟩

    -- Step 2e: Apply the logic completeness lemma
    have h_logic := commitStep_is_logic_complete (hCR := hCR) (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (i := i)
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecCommit] at hj
        cases j using Fin.cases
        case zero => simp at hj
        case succ j' => exact j'.elim0
      )

    obtain ⟨h_V_check, h_rel, h_agree⟩ := h_logic

    -- Step 2f: Simplify the verifier check
    -- simp only [commitStepLogic] at h_V_check
    -- unfold FullTranscript.mk1 at h_V_check
    simp only [Fin.isValue, Transcript_get_message] at h_V_check

    -- dsimp? [Fin.isValue, commitStepLogic, Challenge,
      -- Matrix.cons_val_one, Matrix.cons_val_zero, Lean.Elab.WF.paramLet] at h_ver_stmtOut_eq

    -- Step 2g: Rewrite all variables to their concrete values
    rw [
      h_ver_stmtOut_eq_support, h_ver_stmtOut_eq,
      h_ver_oracle_eq_support,  h_ver_OstmtOut_eq,
      h_wit_eq_support,         h_logic_wit,
      h_prv_stmtOut_eq_support, h_logic_stmt,
      h_prv_oracle_eq_support,  h_logic_oracle
    ]

    -- Step 2h: Complete the proof using logic properties
    constructor
    · -- relOut holds
      dsimp only [Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero,
        foldStepLogic, Lean.Elab.WF.paramLet, Fin.val_succ] at h_rel
      exact h_rel
    · -- Prover and verifier agree
      constructor
      · rfl  -- Statement agreement
      · exact h_agree.2  -- Oracle agreement

open scoped NNReal

def commitKnowledgeError {i : Fin ℓ}
    (m : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, hj⟩ => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_P_to_V_eq_V_to_P] at hj -- not a V challenge

/-- The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def commitRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

/-- Note : stmtIn and witMid already advances to state `(i+1)` from the fold step,
while oStmtIn is not. -/
def commitKStateProp (i : Fin ℓ) (m : Fin (1 + 1))
  (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc i_1)
  (tr : Transcript m (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
  : Prop :=

  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut: use transcript message as oracle (what verifier sees)
    -- The verifier sees tr.messages ⟨0, rfl⟩ as the new oracle, not witMid.f
    let newOracle := tr.messages ⟨0, rfl⟩
    let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (newOracleFn := newOracle) (h_destIdx := by rfl)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtOut)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)

/-- Knowledge state function (KState) for single round -/
def commitKState (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp)
      i hCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    commitKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn) (tr := tr) (mp:=mp)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    -- commitKStateProp 0 = foldStepRelOutProp i (same masterKStateProp)
    rw [cast_eq]
    simp only [foldStepRelOut, foldStepRelOutProp, Set.mem_setOf_eq, commitKStateProp]
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- For pSpecCommit, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0

    intro h_kState_round1
    unfold commitKStateProp masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]

    -- At round 1: masterKStateProp with (explicitVCheck ∧ localizedRoundPolyCheck)
    -- At round 0: masterKStateProp with sumcheckConsistencyProp
    -- Extract the checks from round 1
    obtain ⟨h_sumcheck, h_core⟩ := h_kState_round1

    -- Use Lemma 1.1 (roundPoly_eval_sum_of_consistent_witness)
    -- Key: h_localized says h_i = h_star, and h_explicit says h_i(0) + h_i(1) = s
    -- Therefore h_star(0) + h_star(1) = s, which is what Lemma 1.1 gives us
    constructor
    · -- Prove sumcheckConsistencyProp at round 0
      exact h_sumcheck
    · -- The core (badEventExists ∨ oracleWitnessConsistency) is preserved
      cases h_core with
      | inl hBad =>
        left
        -- Use backward preservation lemma for bad events
        exact badEventExistsProp_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR oStmtIn _ stmtIn.challenges hBad
      | inr hConsistent =>
        right
        -- Use backward preservation lemma for oracle consistency
        exact oracleWitnessConsistency_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) i hCR stmtIn witMid oStmtIn _ hConsistent
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- probEvent_relOut_gt_0: the relOut is satisified under oracle verifier's execution
    -- Now we simp the probEvent_relOut_gt_0 to extract equalities for stmtOut, oStmtOut as deterministic computations (oracle verifier execution) of stmtIn, oStmtIn
    simp at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩

    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      simp only [commitOracleVerifier]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      simp only [simulateQ_pure, pure_bind, Function.comp_apply]
      dsimp only [ProbComp]
      simp only [MessageIdx, StateT.mem_support_pure_state, Prod.mk.injEq, exists_eq_right,
        exists_and_right]

    rcases h_output_mem_V_run_support with ⟨h_init_value_mem_support, h_stmtOut_eq, h_oStmtOut_eq⟩
    simp only [Nat.reduceAdd]

    -- h_relOut : ((stmtOut, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
    simp only [roundRelation, roundRelationProp, Set.mem_setOf_eq] at h_relOut

    set extractedWitIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ :=
      (commitRbrExtractor 𝔽q β i).extractOut (stmtIn, oStmtIn) tr witOut
    -- extractedWitIn = witOut by definition of commitRbrExtractor
    -- ⊢ commitKStateProp 𝔽q β i (Fin.last 1) stmtIn extractedWitIn oStmtIn tr
    unfold commitKStateProp
    simp only [Fin.reduceLast, Fin.isValue, Fin.val_succ, h_stmtOut_eq] at h_relOut ⊢
    -- Key: goal's oStmt = snoc_oracle oStmtIn (tr.messages ⟨0, rfl⟩) = oStmtOut
    have h_oStmt_eq : snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) (oStmtIn := oStmtIn)
        (newOracleFn := tr.messages ⟨0, rfl⟩) = oStmtOut := by
      rw [h_oStmtOut_eq]
      exact snoc_oracle_eq_mkVerifierOStmtOut_commitStep 𝔽q β (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR oStmtIn (tr.messages ⟨0, rfl⟩) tr rfl
    rw [h_oStmt_eq]
    exact h_relOut

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem commitOracleVerifier_rbrKnowledgeSoundness (hInit : init.neverFails) (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := mp) i hCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  use commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use commitKState (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR
  intro stmtIn witIn prover ⟨j, hj⟩
  cases j using Fin.cases with
  | zero => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_fin_one,
    Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' => exact Fin.elim0 j'

end CommitStep

section RelayStep
/- the relay is just to place the conditional oracle message -/

def relayPrvState (i : Fin ℓ) : Fin (0 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- The prover for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleProver (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecRelay) where
  PrvState := relayPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage | ⟨x, h⟩ => by exact x.elim0
  receiveChallenge | ⟨x, h⟩ => by exact x.elim0
  output := fun ⟨stmt, oStmt, wit⟩ =>
    pure ⟨⟨stmt, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR oStmt⟩, wit⟩

lemma h_oracle_size_eq_relay (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  toOutCodewordsCount ℓ ϑ i.castSucc =
      toOutCodewordsCount ℓ ϑ i.succ := by
  simp only [toOutCodewordsCount_succ_eq, hNCR, ↓reduceIte]

def relayOracleVerifier_embed (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  Fin (toOutCodewordsCount ℓ ϑ i.succ) →
    Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ pSpecRelay.MessageIdx
  := fun j => Sum.inl ⟨j.val, by rw [h_oracle_size_eq_relay i hNCR]; omega⟩

/-- The oracle verifier for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleVerifier (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay) where
  verify := fun stmtIn _ => pure stmtIn
  embed := ⟨relayOracleVerifier_embed (r := r) (𝓡 := 𝓡) i hNCR, by
    intro a b h_ab_eq
    simp only [relayOracleVerifier_embed, MessageIdx, Sum.inl.injEq, Fin.mk.injEq] at h_ab_eq
    exact Fin.ext h_ab_eq
  ⟩
  hEq := fun oracleIdx => by simp only [MessageIdx, Function.Embedding.coeFn_mk,
    relayOracleVerifier_embed]

/-- The oracle reduction that is the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleReduction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay) where
  prover := relayOracleProver 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
  verifier := relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR

variable {R : Type} [CommSemiring R] [DecidableEq R] [SelectableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] h_β₀_eq_1 [CharP L 2] [SelectableType L] in
lemma strictRoundRelation_relay_preserved (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement Context i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (witIn : Witness 𝔽q β i.succ)
    (h_relIn : ((stmtIn, oStmtIn), witIn) ∈ strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i) :
    ((stmtIn, fun (j : Fin (toOutCodewordsCount ℓ ϑ i.succ)) ↦
      oStmtIn ⟨j.val, by rw [h_oracle_size_eq_relay i hNCR]; omega⟩), witIn)
      ∈ strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i.succ := by
  dsimp only [strictRoundRelation, strictRoundRelationProp,
    strictFoldStepRelOut, strictFoldStepRelOutProp, Fin.val_succ, Set.mem_setOf_eq] at ⊢ h_relIn
  dsimp only [strictOracleWitnessConsistency, strictOracleFoldingConsistencyProp] at h_relIn ⊢
  constructor
  · exact h_relIn.1
  · constructor
    · exact h_relIn.2.1
    · dsimp only [OracleFrontierIndex.mkFromStmtIdx]
      dsimp only [OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc] at h_relIn
      intro (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
      have h_toOutCodewordsCount_eq : toOutCodewordsCount ℓ ϑ i.succ =
        toOutCodewordsCount ℓ ϑ i.castSucc := (h_oracle_size_eq_relay i hNCR).symm
      exact h_relIn.2.2 ⟨j, by omega⟩

omit [CharP L 2] [SelectableType L] in
theorem relayOracleReduction_perfectCompleteness (hInit : init.neverFails) (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecRelay)
      (relIn := strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (oracleReduction := relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR)
      (init := init)
      (impl := impl) := by
  simp only [OracleReduction.perfectCompleteness, relayOracleReduction]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  -- ⊢ ∀ ⟨stmtIn, oStmtIn⟩ witIn h_relIn,
    -- Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
    -- (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut, simulateQ ...] = 1
  intro ⟨stmtIn, oStmtIn⟩ witIn h_relIn
  -- Now simp the prover execution logic
  simp only [pSpecRelay, ChallengeIdx, Reduction.run, Prover.run, Fin.reduceLast, relayOracleProver,
    Fin.isValue, Challenge, relayOracleVerifier,
    OracleReduction.toReduction, OracleVerifier.toVerifier,
    Prover.runToRound, Nat.reduceAdd, Fin.induction_zero,
    liftM_eq_liftComp, bind_pure_comp, pure_bind, liftComp_pure, map_pure,
      Verifier.run, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, probEvent_map, probEvent_eq_one_iff, probFailure_eq_zero_iff, hInit,
    Function.comp_apply, Prod.mk.injEq, true_and]
  intro (s : σ) (hs : s ∈ OracleComp.support init)
  dsimp only [MessageIdx, Fin.isValue]
  -- ⊢ ((stmtIn, fun i_1 ↦ oStmtIn ⟨↑i_1, ⋯⟩), witIn) ∈ strictRoundRelation 𝔽q β i.succ ∧
  -- mapOStmtOutRelayStep 𝔽q β i hNCR oStmtIn = fun i_1 ↦ oStmtIn ⟨↑i_1, ⋯⟩
  constructor
  · exact (strictRoundRelation_relay_preserved (i := i) (hNCR := hNCR) (stmtIn := stmtIn)
    (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn))
  · rfl

def relayKnowledgeError (m : pSpecRelay.ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, _⟩ => j.elim0

/-- The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def relayRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

def relayKStateProp (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
  (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
  : Prop :=
  -- Relay step inherits sumcheckConsistency from foldStepRelOut (relIn) and preserves it
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H
  masterKStateProp (mp := mp) (ϑ := ϑ) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
    (stmt := stmtIn) (wit := witMid) (oStmt := mapOStmtOutRelayStep
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)
    (localChecks := sumCheckConsistency)

/-- The relay step oracle transformation equals mkVerifierOStmtOut.
This shows that mapOStmtOutRelayStep is exactly what the verifier produces. -/
lemma mapOStmtOut_eq_mkVerifierOStmtOut_relayStep
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (transcript : FullTranscript pSpecRelay) :
    let v := relayOracleVerifier (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
    mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn =
    OracleVerifier.mkVerifierOStmtOut v.embed v.hEq oStmtIn transcript := by
  intro v
  funext j
  simp only [mapOStmtOutRelayStep, OracleVerifier.mkVerifierOStmtOut, relayOracleVerifier, v]
  sorry

/-- Knowledge state function (KState) for single round -/
def relayKnowledgeStateFunction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    relayKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp:=mp) -- (𝓑 := 𝓑)
      i hNCR stmtIn witMid oStmtIn
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witIn => by
    rw [cast_eq]
    simp only [foldStepRelOut, foldStepRelOutProp, Set.mem_setOf_eq, relayKStateProp]
    unfold masterKStateProp
    simp only [Fin.val_succ]
    -- After simplification: sumcheckConsistency ∧ core_L ↔ sumcheckConsistency ∧ core_R
    -- where core_L uses castSuccOfSucc and core_R uses mkFromStmtIdx
    -- Both sides have sumcheckConsistency, so we can focus on the core part
    constructor <;> intro h
    · -- Forward: sumcheckConsistency ∧ core_L → sumcheckConsistency ∧ core_R
      constructor
      · exact h.1 -- sumcheckConsistency is preserved
      · cases h.2 with
        | inl hBad =>
          left
          rw [←badEventExistsProp_relay_preserved 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn stmtIn.challenges]
          exact hBad
        | inr hConsist =>
          right
          rw [←oracleWitnessConsistency_relay_preserved' 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) i hNCR stmtIn witIn oStmtIn]
          exact hConsist
    · -- Backward: sumcheckConsistency ∧ core_R → sumcheckConsistency ∧ core_L
      constructor
      · exact h.1 -- sumcheckConsistency is preserved
      · cases h.2 with
        | inl hBad =>
          left
          rw [badEventExistsProp_relay_preserved 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn stmtIn.challenges]
          exact hBad
        | inr hConsist =>
          right
          simp only [←oracleWitnessConsistency_relay_preserved' 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) i hNCR stmtIn witIn oStmtIn] at hConsist
          exact hConsist
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => Fin.elim0 m
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩

    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [relayOracleVerifier]
      -- dsimp only [StateT.run]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      rw [simulateQ_bind] -- adjust this simulateQ_bind, simulateQ_bind]
      -- No oracle query unfolding
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [simulateQ_pure, pure_bind, Function.comp_apply]
      dsimp only [ProbComp] -- unfold ProbComp back to OracleComp
      simp only [MessageIdx, StateT.mem_support_pure_state, Prod.mk.injEq, exists_eq_right,
        exists_and_right]

    rcases h_output_mem_V_run_support with ⟨h_init_value_mem_support,
      h_stmtOut_eq, h_oStmtOut_eq⟩
    simp only [Nat.reduceAdd]

    -- Now h_relOut : ((stmtIn, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
    -- where oStmtOut = OracleVerifier.mkVerifierOStmtOut ...
    simp only [roundRelation, roundRelationProp, Set.mem_setOf_eq] at h_relOut
    unfold masterKStateProp at h_relOut

    -- The goal is relayKStateProp, which expands to masterKStateProp with sumcheckConsistency
    simp only [relayKStateProp]
    unfold masterKStateProp
    -- relayRbrExtractor.extractOut is identity
    simp only [relayRbrExtractor]
    simp only [Fin.val_succ] at h_relOut
    simp only [h_stmtOut_eq] at h_relOut ⊢
    -- Split the conjunction: sumcheck consistency ∧ (bad event ∨ oracle witness consistency)
    constructor
    · -- First goal: sumcheck consistency
      exact h_relOut.1
    · -- Second goal: bad event ∨ oracle witness consistency
      -- Use the lemma to show oStmtOut = mapOStmtOutRelayStep
      have h_oStmt_eq_map : oStmtOut =
        mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn := by
        rw [h_oStmtOut_eq]; symm;
        exact mapOStmtOut_eq_mkVerifierOStmtOut_relayStep
          (Context := Context) (i := i) (hNCR := hNCR) (oStmtIn := oStmtIn) (transcript := tr)
      -- Same oracle size, now rw oracle content
      cases h_relOut.2 with
      | inl hBad =>
        left
        rw [h_oStmt_eq_map] at hBad
        exact hBad
      | inr hConsist =>
        right
        rw [h_oStmt_eq_map] at hConsist
        exact hConsist

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem relayOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (relayKnowledgeError) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  use relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use relayKnowledgeStateFunction (mp:=mp) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hNCR
  intro stmtIn witIn prover j
  exact Fin.elim0 j

end RelayStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

open Classical in
/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    -- Compute the message using the honest transcript from logic
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    -- Construct the transcript from the message and challenges (no challenges in this step)
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Delegate to the logic instance for prover output
    pure ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).proverOut stmtIn witIn oStmtIn t)

open Classical in
/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ) ⟨0, rfl⟩ ()

    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c

    -- Get the logic instance
    let logic := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))

    -- Use guard for verifier check (fails if check doesn't pass)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  embed := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).embed
  hEq := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).hEq

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp))
  (hInit : init.neverFails) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
    (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSafe := by simp only [probFailure_eq_zero_iff, IsEmpty.forall_iff, implies_true])
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
    -- Step 2: Convert probability 1 to universal quantification over support
  simp only [probEvent_eq_one_iff]

  intro stmtIn oStmtIn witIn h_relIn
  haveI : [pSpecFinalSumcheckStep (L := L).Challenge]ₒ.FiniteRange :=
    instFiniteRangePSpecFinalSumcheckStepChallenge
  haveI : ([]ₒ ++ₒ [pSpecFinalSumcheckStep (L := L).Challenge]ₒ).FiniteRange :=
    []ₒ.instFiniteRangeSumAppend [pSpecFinalSumcheckStep (L := L).Challenge]ₒ

  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    -- Step 2e: Apply the logic completeness lemma
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

  -- -- Step 3: Unfold protocol definitions
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier,
    FullTranscript.mk1]

-- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff, probFailure_liftComp_eq]
    rw [probFailure_eq_zero_iff]
    simp only [neverFails_pure, true_and]

    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Nat.reduceAdd, Fin.succ_zero_eq_one, ChallengeIdx,
      Fin.val_last, liftComp_pure, support_pure, Set.mem_singleton_iff] at hInputState_mem_support
    -- Now we get equality: hInputState_mem_support : inputState = (witIn.f ⟨0, ⋯⟩, stmtIn, oStmtIn, witIn, witIn.f ⟨0, ⋯⟩)
    split
    simp only [probFailure_pure, true_and]

    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro prover_final_output h_prover_final_output_support
    conv =>
      simp only [probFailure_liftComp]
      simp only

    simp only [
      -- probFailure_liftComp,
      -- probFailure_map,
      -- probFailure_bind_eq_zero_iff,
      -- probFailure_pure,
      implies_true,
      and_true
    ]

    -- Apply FiniteRange instances for oracle simulation (defined in Spec.lean)
    haveI : [fun j => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Fin.last ℓ) j]ₒ.FiniteRange := by
        apply instFiniteRangeOracleStatementFinLast
    haveI : [(pSpecFinalSumcheckStep (L := L)).Message]ₒ.FiniteRange :=
      instFiniteRangePSpecFinalSumcheckStepMessage
    -- simulateQ_query (q : OracleQuery spec α) : simulateQ so q = so.impl q
    simp only [MessageIdx, Fin.isValue, Message, Nat.reduceAdd, Fin.succ_zero_eq_one,
      SubSpec.liftM_query_eq_liftM_liftM, guard_eq, bind_pure_comp, simulateQ_bind, simulateQ_query,
      probFailure_eq_zero_iff, neverFails_bind_iff, Function.comp_apply, simulateQ_map,
      simulateQ_ite, simulateQ_pure, simulateQ_failure, neverFails_map_iff, neverFails_pure,
      neverFails_guard]
    simp only [←probFailure_eq_zero_iff]
    constructor
    · -- the oracle query (to get the message `c`)
      -- simulateQ-ed over simOracle2 is safe
      simp only [Fin.isValue, probFailure_simOracle2]
    · intro c c_mem_oracle_query_support
      -- **Unfold the oracle query logic in h_i**

      -- Step 1: Unfold liftM to expose the structure
      -- simp only [←liftM_query_eq_liftM_liftM] at c_mem_oracle_query_support
      simp only [liftM, monadLift, MonadLift.monadLift] at c_mem_oracle_query_support
      -- Step 2: NOW apply the lemma inside the support
      conv at c_mem_oracle_query_support => rw [simOracle2_impl_inr_inr]
      -- Step 3: Extract equality from singleton support
      simp only [Fin.isValue, support_pure, Set.mem_singleton_iff] at c_mem_oracle_query_support
      -- Now: h_i = OracleInterface.answer (messages ⟨0, ...⟩) ()
      rw [c_mem_oracle_query_support]
      -- Unfold the actually query, which is getting the message computed by prover
      unfold OracleInterface.answer
      dsimp only [instOracleInterfaceMessagePSpecFinalSumcheckStep]

      -- Step 2e: Apply the logic completeness lemma
      obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
        (witIn := witIn) (h_relIn := h_relIn) (challenges :=
        fun ⟨j, hj⟩ => by
          match j with
          | 0 =>
            have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
              dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
              simp only [ne_eq, reduceCtorEq, not_false_eq_true]
            exfalso
            exact hj_ne hj
        )
      rw [hInputState_mem_support] -- Convert input States into equality
      exact h_V_check
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
    rcases h_trace_support with ⟨prvStmtOut_support, prvOStmtOut_support, prvWitOut_support,
      h_prv_def_support, vStmtOut_support, vOracleOut_support,
      h_ver_def_support, h_total_eq_support⟩

    -- Step 2c: Simplify the verifier computation
    conv at h_ver_def_support =>
      rw [simulateQ_bind]
      erw [simulateQ_simOracle2_liftM (oSpec := []ₒ) (t₁ := oStmtIn)]
      erw [simOracle2_impl_inr_inr]
      rw [bind_pure_simulateQ_comp]
      -- big simp to kill the `guard` here
      simp only [MessageIdx, Fin.val_last, Fin.isValue, guard_eq, bind_pure_comp, simulateQ_map,
        simulateQ_ite, simulateQ_pure, simulateQ_failure, support_map, support_ite, support_pure,
        support_failure, Set.mem_image, Set.mem_ite_empty_right, Set.mem_singleton_iff, and_true,
        exists_const, Prod.mk.injEq, existsAndEq]

    -- Step 2d: Extract all the equalities
    simp only [Prod.mk_inj] at h_total_eq_support
    rcases h_total_eq_support with ⟨⟨h_prv_stmtOut_eq_support, h_prv_oracle_eq_support⟩,
      ⟨h_ver_stmtOut_eq_support, h_ver_oracle_eq_support⟩, h_wit_eq_support⟩

    dsimp only [finalSumcheckStepLogic] at h_prv_def_support
    simp only [Prod.mk_inj] at h_prv_def_support
    rcases h_prv_def_support with ⟨⟨h_logic_stmt, h_logic_oracle⟩, h_logic_wit⟩

    rcases h_ver_def_support with ⟨_h_V_check_but_not_used, h_ver_stmtOut_eq, h_ver_OstmtOut_eq⟩

    -- Step 2e: Apply the logic completeness lemma
    have h_logic := finalSumcheckStep_is_logic_complete 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecFinalSumcheckStep] at hj
        cases j using Fin.cases
        case zero => simp at hj
        case succ j' => exact j'.elim0
      )

    obtain ⟨_h_V_check_but_also_not_used, h_rel, h_agree⟩ := h_logic

    -- Step 2g: Rewrite all variables to their concrete values
    rw [
      h_ver_stmtOut_eq_support, h_ver_stmtOut_eq,
      h_ver_oracle_eq_support,  h_ver_OstmtOut_eq,
      -- h_wit_eq_support,         h_logic_wit, -- not used since both are `True`
      h_prv_stmtOut_eq_support, h_logic_stmt,
      h_prv_oracle_eq_support,  h_logic_oracle
    ]

    -- Step 2h: Complete the proof using logic properties
    constructor
    · -- relOut holds
      exact h_rel
    · -- Prover and verifier agree
      constructor
      · rfl  -- Statement agreement
      · exact h_agree.2  -- Oracle agreement

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

/-- When oracle folding consistency holds, extractMLP must succeed.

This connects the proximity-based `oracleFoldingConsistencyProp` to the decoder:
- `oracleFoldingConsistencyProp` implies each oracle is compliant (fiberwise-close)
- Fiberwise-closeness implies the first oracle is within unique decoding radius
- Berlekamp-Welch decoder succeeds when within UDR, returning `some` -/
lemma extractMLP_some_of_oracleFoldingConsistency
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (h : oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
      (challenges := challenges) (oStmt := oStmt)) :
    ∃ tpoly, extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmt) = some tpoly := by
  sorry

/-- When oracle folding consistency holds from first oracle through the final constant,
the extracted polynomial's evaluation at challenges equals the final constant.

This is the key lemma connecting extraction to the final sumcheck verification:
- `oracleFoldingConsistencyProp` ensures all intermediate foldings are correct
- `h_finalFolding` (isCompliant to final constant) ensures the last step is correct
- Together, they imply the extracted `tpoly` satisfies `tpoly.eval(challenges) = c` -/
lemma extracted_t_poly_eval_eq_final_constant
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin ℓ → L)
    (c : L) -- the final constant from the prover
    (tpoly : MultilinearPoly L ℓ)
    (h_extractMLP : extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmtOut) = some tpoly)
    (h_finalSumcheckStepOracleConsistency : finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtOut) (oStmtOut := oStmtOut)) : c = tpoly.val.eval challenges := by
  -- Approach:
    -- 1. UDR-extracted-f⁰ = tpoly's evaluations on S⁰ (from extractMLP: first oracle decodes to tpoly)
    -- 2. From finalSumcheckStepOracleConsistency we have
    -- - `∀ k. UDR-extracted-f^(ϑ*k) folds to UDR-extracted-f^(ϑ*(k+1))`
    -- - last explicit oracle `UDR-extracted-f^(ϑ*(ℓ/ϑ-1))`
      -- folds to final constant function `fun x => c`

    -- => So we have the direct path of iterated_fold from tpoly's evaluations
      -- all the way to `fun x => c`, which is essentially `tpoly.val.eval challenges`
        -- since `tpoly` only has `ℓ` variables

    -- Reference: h_c_eq proofs inside `finalSumcheckStep_verifierCheck_passed`
      -- (which adopts `iterated_fold_advances_evaluation_poly`)
    -- `Q.E.D`
  sorry

-- #exit
def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ)) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ  (Fin.last ℓ) j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl -- witMidSucc is of type Unit
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle 𝔽q β oStmtMid
    let polyOpt := extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ⟩) (f := f0)
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ - ↑(Fin.last ℓ))] := ⟨MvPolynomial.C stmtMid.sumcheck_target,
      by sorry⟩
    match polyOpt with
    | none =>
      -- Extraction failed - use constant H to satisfy sumcheckConsistencyProp trivially
      exact {
        t := ⟨0, by apply zero_mem⟩,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      -- Build H_ℓ from t and challenges r'
      exact {
        t := tpoly,
        -- projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := tpoly)
          -- (m := BBF_SumcheckMultiplierParam.multpoly stmtMid.ctx)
          -- (i := Fin.last ℓ) (challenges := stmtMid.challenges),
        H := H_constant,
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (mp := BBF_SumcheckMultiplierParam)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    let sumcheckFinalCheck : Prop := stmtIn.sumcheck_target
      = eqTilde (stmtIn.ctx.t_eval_point) stmtIn.challenges * c
    let finalFoldingProp := finalSumcheckStepFoldingStateProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ
        · exact hdiv.out) (input := ⟨stmtOut, oStmtIn⟩)

    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) )
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    finalSumcheckKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (tr := tr) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    rw [cast_eq]
    rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- toFun_next is impacted by how we build extractMid
    -- For pSpecCommit, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]

    -- declare c and stmtOut as in KState (m=1), as well as in honest verifier
    let tr_so_far := (pSpecFinalSumcheckStep (L := L)).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheckStep (L := L)) (tr.concat msg)).1 i_msg0
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }

    intro h_kState_round1
    unfold finalSumcheckKStateProp finalSumcheckStepFoldingStateProp masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]

    -- At round 1: masterKStateProp with (explicitVCheck ∧ localizedRoundPolyCheck)
    -- At round 0: masterKStateProp with sumcheckConsistencyProp
    -- Extract the checks from round 1
    obtain ⟨h_V_check, h_core⟩ := h_kState_round1

    constructor
    · -- Prove sumcheckConsistencyProp at round 0
      unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
      simp only [Fin.val_last, Fin.mk_zero', Fin.coe_ofNat_eq_mod]
      split;
      · simp only [MvPolynomial.eval_C, sum_const, Fintype.card_piFinset, card_map, card_univ,
        Fintype.card_fin, prod_const, tsub_self, Fintype.card_eq_zero, pow_zero, one_smul]
      · simp only [MvPolynomial.eval_C, sum_const, Fintype.card_piFinset, card_map, card_univ,
        Fintype.card_fin, prod_const, tsub_self, Fintype.card_eq_zero, pow_zero, one_smul]
    ·
      -- Case split on h_core first to properly handle witness extraction
      cases h_core with
      | inl hConsistent =>
        -- When we have oracleFoldingConsistency, extractMLP must succeed
        have ⟨tpoly, h_extractMLP⟩ := extractMLP_some_of_oracleFoldingConsistency 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtIn stmtIn.challenges hConsistent.1
        right
        dsimp only [oracleWitnessConsistency]
        constructor
        · -- witnessStructuralInvariant: show H_constant = projectToMidSumcheckPoly
          unfold finalSumcheckRbrExtractor witnessStructuralInvariant
          simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
          -- ⊢ ⟨MvPolynomial.C stmtIn.sumcheck_target, ⋯⟩ =
            -- projectToMidSumcheckPoly ℓ tpoly (BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx) (Fin.last ℓ) stmtIn.challenges
          have h_H_last_eq := projectToMidSumcheckPoly_at_last_eval (ℓ := ℓ) (t := tpoly)
            (m := BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx) (challenges := stmtIn.challenges)
          -- Step 1: Use polynomial extensionality
          refine SetLike.coe_eq_coe.mp ?_
          rw [projectToMidSumcheckPoly_at_last_eq]
          have h_sumcheck_target_eq : stmtIn.sumcheck_target =
            (MvPolynomial.eval stmtIn.challenges
              (BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx).val) *
              (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
            -- h_V_check : stmtIn.sumcheck_target =
            --   eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges * c
            rw [h_V_check]
            congr 1
            change c = tpoly.val.eval stmtIn.challenges
            exact extracted_t_poly_eval_eq_final_constant 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
              (challenges := stmtIn.challenges) (c := c) (tpoly := tpoly)
              (h_extractMLP := h_extractMLP) (h_finalSumcheckStepOracleConsistency := hConsistent)
          simp only [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
        · constructor
          · -- ⊢ firstOracleWitnessConsistencyProp 𝔽q β
              -- ((finalSumcheckRbrExtractor 𝔽q β).extractMid 0 (stmtIn, oStmtIn) (Transcript.concat msg tr) witMid).t (f⁽⁰⁾)
            dsimp only [finalSumcheckRbrExtractor, firstOracleWitnessConsistencyProp]
            simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
              OracleFrontierIndex.val_mkFromStmtIdx]
            have h_extractMLP_eq_some_iff_pair_UDRClose := extractMLP_eq_some_iff_pair_UDRClose 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (f := getFirstOracle 𝔽q β oStmtIn) (tpoly := tpoly).mp (h_extractMLP)
            exact h_extractMLP_eq_some_iff_pair_UDRClose
          · exact hConsistent.1
      | inr hBad =>
        -- When badEventExists, we only need to preserve it
        left
        exact hBad

  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
  -- Same pattern as relay: verifier output (stmtOut, oStmtOut) + h_relOut ⇒ commitKStateProp 1
    simp at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩

    conv at h_output_mem_V_run_support => -- same as fold step
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [finalSumcheckVerifier]
      -- dsimp only [StateT.run]
      -- simp only [simulateQ_bind, simulateQ_query, simulateQ_pure]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      -- enter [1, i_1, 2, 1, x]
      rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
      erw [simulateQ_simOracle2_liftM (oSpec := []ₒ) (t₁ := oStmtIn)]
      erw [simOracle2_impl_inr_inr] -- query prover message
      unfold OracleInterface.answer
      dsimp only [instOracleInterfaceMessagePSpecFinalSumcheckStep]
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure,
        bind_map_left, Function.comp_apply]
      unfold Functor.map
      dsimp only [StateT.instMonad]
      simp only [StateT.map_ite] -- simplify the ite from the `guard`
      -- Collapse the ite structure of the OracleComp.support
      simp only [support_ite,                    -- OracleComp.support_ite (outer layer)
        StateT.support_map_const_pure,  -- handle (StateT.map f (pure ()) i_1).support
        StateT.support_map_failure
      ]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
      simp only [Fin.isValue, exists_eq, and_true, exists_and_right]

    rcases h_output_mem_V_run_support with ⟨init_value, h_init_value_mem_support, h_stmtOut_eq, h_oStmtOut_eq⟩
    simp only [Fin.reduceLast, Fin.isValue]

    -- h_relOut : ((stmtOut, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
    simp only [finalSumcheckRelOut, finalSumcheckRelOutProp, Set.mem_setOf_eq] at h_relOut

    -- Goal: commitKStateProp 1 stmtIn oStmtIn tr witOut
    unfold finalSumcheckKStateProp
    -- Unfold the sendMessage, receiveChallenge, output logic of prover
    dsimp only
    -- stmtOut = stmtIn; need oStmtOut = snoc_oracle oStmtIn witOut.f so goal matches h_relOut
    simp only [h_stmtOut_eq] at h_relOut ⊢
    have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
    -- c equals tr.messages ⟨0, rfl⟩

    constructor
    · -- First conjunct: sumcheck_target = eqTilde r challenges * c
      rw [h_init_value_mem_support]; rfl
    · -- Second conjunct: finalSumcheckStepFoldingStateProp ({ toStatement := stmtIn, final_constant := c }, oStmtIn)
      rw [h_oStmtOut_eq_oStmtIn] at h_relOut
      exact h_relOut

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑)
        (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) )
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
      (rbrKnowledgeError := finalSumcheckKnowledgeError) := by
  use FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
  use finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckKnowledgeStateFunction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) init impl
  intro stmtIn witIn prover ⟨j, hj⟩
  -- pSpecFinalSumcheckStep has 1 message (ChallengeIdx = Fin 1); same pattern as commit
  cases j using Fin.cases with
  | zero => simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
    Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj  -- bound for challenge index 0 (P→V only, no V challenge)
  | succ j' => exact Fin.elim0 j'

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
