/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.RingSwitching.Spec
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Module Binius.BinaryBasefold TensorProduct Nat Matrix ProbabilityTheory
open scoped NNReal

/-!
# Ring-Switching Core Interaction Phase

This module implements the core interactive sumcheck phase of the ring-switching protocol.

### Iterated Sumcheck Steps
6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.

Each iteration of the loop constitutes a single round:
- Round i (for i = 1, ..., ℓ'):
  1. Prover sends sumcheck polynomial h_i(X) over large field L
  2. Verifier samples challenge α_i ∈ L
    - Prover & verifier updates state based on challenge

This is the core computational phase with ℓ' rounds, each with 2 messages, and is the main
source of RBR knowledge soundness error.

### Final Sumcheck Step
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
-/

namespace Binius.RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable (aOStmtIn : AbstractOStmtIn L ℓ')

section IteratedSumcheckStep
variable (i : Fin ℓ')

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check: validates that s = h(0) + h(1). -/
@[reducible]
def sumcheckVerifierCheck (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (h_i : L⦃≤ 2⦄[X]) : Prop :=
  h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtIn.sumcheck_target

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def sumcheckVerifierStmtOut (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (h_i : L⦃≤ 2⦄[X]) (r_i' : L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtIn.challenges r_i'
    }

/-- Pure prover message computation: computes h_i from the witness. -/
@[reducible]
def sumcheckProverComputeMsg (witIn : SumcheckWitness L ℓ' i.castSucc) : L⦃≤ 2⦄[X] :=
  getSumcheckRoundPoly ℓ' 𝓑 (i := i) witIn.H

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def sumcheckProverWitOut (_stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (witIn : SumcheckWitness L ℓ' i.castSucc) (r_i' : L) : SumcheckWitness L ℓ' i.succ :=
  {
      t' := witIn.t',
      H := projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
  }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the i-th round of Ring Switching Sumcheck. -/
def sumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
      (SumcheckWitness L ℓ' i.castSucc)
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
      (SumcheckWitness L ℓ' i.succ)
      (pSpecSumcheckRound L) where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) aOStmtIn i.castSucc
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) aOStmtIn i.succ

  verifierCheck := fun stmtIn transcript =>
    sumcheckVerifierCheck (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (𝓑:=𝓑)
      i stmtIn (transcript.messages ⟨0, rfl⟩)

  verifierOut := fun stmtIn transcript =>
    sumcheckVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn
      (transcript.messages ⟨0, rfl⟩) (transcript.challenges ⟨1, rfl⟩)

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl

  -- honestProverTranscript is the concatenation of sendMessage & receiveChallenge methods
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg := sumcheckProverComputeMsg (L:=L) (ℓ':=ℓ') (𝓑:=𝓑) i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)

  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let h_i := transcript.messages ⟨0, rfl⟩
    let r_i' := transcript.challenges ⟨1, rfl⟩
    let stmtOut := sumcheckVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn h_i r_i'
    let witOut := sumcheckProverWitOut (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn witIn r_i'
    ((stmtOut, oStmtIn), witOut)

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the sumcheck phase. -/
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc × L⦃≤ 2⦄[X]
  | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc ×
    (∀ j, aOStmtIn.OStmtIn j) ×
    SumcheckWitness L ℓ' i.castSucc × L⦃≤ 2⦄[X] × L

/-- The prover for the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleProver (i : Fin ℓ') :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where

  PrvState := iteratedSumcheckPrvState κ L K ℓ ℓ' aOStmtIn i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage -- There are 2 messages in the pSpec
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    let h_i := sumcheckProverComputeMsg (L:=L) (ℓ':=ℓ') (𝓑:=𝓑) i wit
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))

  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let logic := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i
    let t := FullTranscript.mk2 h_i r_i'
    pure (logic.proverOut stmt wit oStmt t)

open Classical in
/-- The oracle verifier for the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    -- next round
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript.
  verify := fun stmtIn pSpecChallenges => do
    -- Message 0 : Receive h_i(X) from prover
    let h_i : L⦃≤ 2⦄[X] ← query (spec := [(pSpecSumcheckRound L).Message]ₒ)
      ⟨0, rfl⟩ ()
    -- Message 1 : Sample challenge r'_i and send to prover
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩

    let t := FullTranscript.mk2 h_i r_i'
    let logic := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i

    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction that is the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleReduction (i : Fin ℓ') :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  prover := iteratedSumcheckOracleProver κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i
  verifier := iteratedSumcheckOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i

/-! ## Strong Completeness Theorem -/

omit [NeZero κ] [Fintype L] [DecidableEq L] [CharP L 2] [SelectableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] in
lemma sumcheckStep_is_logic_complete (i : Fin ℓ') :
    (sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ)
    (ℓ':=ℓ') (h_l:=h_l) (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2

  dsimp only [sumcheckStepLogic, strictSumcheckRoundRelation,
    strictSumcheckRoundRelationProp, masterStrictKStateProp] at h_relIn

  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H
    := h_relIn.1

  -- Fact 1: Verifier check passes
  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    simp only [sumcheckStepLogic, step, sumcheckVerifierCheck]
    rw [h_sumcheck_cons]
    apply getSumcheckRoundPoly_sum_eq (𝓑 := 𝓑) (i := i) (h := witIn.H)

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := rfl

  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    simp only [step, sumcheckStepLogic]
    -- Fact 4: Prover and verifier oracle statements agree
    unfold OracleVerifier.mkVerifierOStmtOut
    funext j
    split
    · rename_i j' heq
      simp only [MessageIdx, Function.Embedding.coeFn_mk, Sum.inl.injEq] at heq
      cases heq
      rfl
    · rename_i heq
      simp only [MessageIdx, Function.Embedding.coeFn_mk, reduceCtorEq] at heq

  -- Key fact: Oracle statements are unchanged in the fold step
  -- (all oracle indices map via Sum.inl in the embedding)
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, sumcheckStepLogic]

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (strictSumcheckRoundRelation)
    simp only [step, sumcheckStepLogic, strictSumcheckRoundRelation,
      strictSumcheckRoundRelationProp, masterStrictKStateProp]
    let r_i' := challenges ⟨1, rfl⟩
    simp only [Fin.val_succ, Set.mem_setOf_eq]
    simp only [Fin.coe_castSucc] at h_relIn
    have h_oracleWitConsistency_In := h_relIn.2
    rw [h_verifierOStmtOut_eq];
    dsimp only [strictOracleWitnessConsistency] at h_oracleWitConsistency_In ⊢
    -- Extract the three components from the input
    obtain ⟨h_wit_struct_In, h_oStmtIn_compat⟩ :=
        h_oracleWitConsistency_In

    constructor
    · -- sumcheckConsistencyProp
      unfold sumcheckConsistencyProp
      dsimp only [verifierStmtOut, proverWitOut, proverOutput]
      simp only [step, sumcheckStepLogic, transcript]
      apply projectToNextSumcheckPoly_sum_eq
    · constructor
      · -- Component 1: witnessStructuralInvariant
        unfold witnessStructuralInvariant at ⊢ h_wit_struct_In
        let h_H_In := h_wit_struct_In
        conv_lhs =>
          dsimp only [proverWitOut, proverOutput, step,
          sumcheckStepLogic]
        conv_lhs =>
          rw [h_H_In]
          rw [←projectToMidSumcheckPoly_succ]
        rfl
      · --Part 2.2: initialCompatibility
        exact h_oStmtIn_compat

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

variable {R : Type} [CommSemiring R] [DecidableEq R] [SelectableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem iteratedSumcheckOracleReduction_perfectCompleteness
    (hInit : init.neverFails) (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i.castSucc)
      (relOut := strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ (L:=L)
        (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (𝓑:=𝓑) (β := β) (h_l := h_l) aOStmtIn i)
      (init := init) (impl := impl) := by
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
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver, iteratedSumcheckOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk2]

  let step := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
    (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i
  let strongly_complete : step.IsStronglyComplete := sumcheckStep_is_logic_complete (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
    (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i

  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY
  · -- Very same structure as fold step of Binary Basefold
    simp only [probFailure_bind_eq_zero_iff, probFailure_liftComp_eq]
    rw [probFailure_eq_zero_iff]
    simp only [neverFails_pure, true_and]

    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      liftComp_pure, support_pure, Set.mem_singleton_iff] at hInputState_mem_support
    -- Now we get equality: hInputState_mem_support : inputState = (foldProverComputeMsg ...)
    conv => enter [1]; simp only [ChallengeIdx, Fin.isValue, Challenge, cons_val_one, cons_val_zero,
      liftComp_query, SubSpec.liftM_query_eq_liftM_liftM, liftM_append_right_eq, probFailure_liftM];
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
      dsimp only [instOracleInterfaceMessagePSpecSumcheckRound]

      -- Step 2e: Apply the logic completeness lemma
      obtain ⟨h_V_check, h_relOut, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
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

  -- GOAL 2 : CORRECTNESS
  · intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- simp the `guard` in oracle verifier logic
    simp only [ChallengeIdx, Fin.isValue, Message, cons_val_zero, Fin.succ_zero_eq_one,
      liftComp_pure, Challenge, cons_val_one, liftComp_query, SubSpec.liftM_query_eq_liftM_liftM,
      liftM_append_right_eq, Fin.succ_one_eq_two, Fin.castSucc_one, Fin.reduceLast, MessageIdx,
      guard_eq, bind_pure_comp, simulateQ_bind, simulateQ_query, map_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure, Functor.map_map,
      liftComp_bind, liftComp_map, Prod.mk.eta, pure_bind, support_bind, support_query,
      Set.mem_univ, liftComp_support, support_map, support_ite, support_pure, support_failure,
      Set.iUnion_true, Set.mem_iUnion, Set.mem_image, Set.mem_ite_empty_right,
      Set.mem_singleton_iff, and_true, Prod.mk.injEq, exists_const, exists_and_left,
      exists_prop] at hx_mem_support

    obtain ⟨r_i', h_i, h_V_check_passed,
      h_prv_defs_eq, h_ver_defs_eq, h_i_mem_query_support, h_witOut_eq⟩ := hx_mem_support

    ------------------------------------------------------------------
    -- Step 1: Unfold liftM to expose the structure
    simp only [liftM, monadLift, MonadLift.monadLift] at h_i_mem_query_support
    -- Step 2: NOW apply the lemma inside the support
    conv at h_i_mem_query_support => rw [simOracle2_impl_inr_inr]
    -- Step 3: Extract equality from singleton support
    simp only [Fin.isValue, Matrix.cons_val_zero, support_pure,
      Set.mem_singleton_iff] at h_i_mem_query_support
    -- Now: h_i = OracleInterface.answer (messages ⟨0, ...⟩) ()
    unfold OracleInterface.answer at h_i_mem_query_support
    dsimp only [instOracleInterfaceMessagePSpecSumcheckRound] at h_i_mem_query_support
    simp only [Fin.isValue, Message, cons_val_zero] at h_i_mem_query_support
    ------------------------------------------------------------------

    rw [Prod.mk_inj] at h_prv_defs_eq
    rcases h_prv_defs_eq with ⟨h_prv_stmtOut_eq, h_prv_oStmtOut_eq⟩
    rcases h_ver_defs_eq with ⟨h_ver_stmtOut_eq, h_ver_oStmtOut_eq⟩

    -- Logic completeness
    obtain ⟨_h_V_check_but_not_used, h_relOut, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn) (challenges := fun ⟨j, hj⟩ =>
        have h_j_eq_1 : j = 1 := by
           dsimp [pSpecSumcheckRound] at hj
           cases j using Fin.cases
           case zero => simp at hj
           case succ j1 =>
             cases j1 using Fin.cases
             case zero => rfl
             case succ k => exact k.elim0 (α := k.succ.succ = 1)
        match j with
        | 0 => by
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, cons_val_zero,
            Direction.not_P_to_V_eq_V_to_P] at hj
        | 1 => r_i'
      )

    -- Unfold
    dsimp only [sumcheckStepLogic, sumcheckProverComputeMsg, step] at h_V_check_passed
    unfold FullTranscript.mk2 at h_V_check_passed
    simp only [Fin.isValue, Transcript_get_message] at h_V_check_passed

    dsimp only [Fin.isValue, sumcheckProverComputeMsg, sumcheckStepLogic,
      Challenge, Matrix.cons_val_one, Matrix.cons_val_zero] at h_ver_stmtOut_eq
    rw [
      h_ver_stmtOut_eq.symm,
      h_ver_oStmtOut_eq.symm,
      h_witOut_eq.symm,
      h_prv_stmtOut_eq.symm,
      h_prv_oStmtOut_eq.symm,
      h_i_mem_query_support
    ]

    constructor
    · exact h_relOut
    · constructor
      · rfl
      · exact h_agree.2

def iteratedSumcheckRoundKnowledgeError (_ : Fin ℓ') : ℝ≥0 := (2 : ℝ≥0) / (Fintype.card L)

/-- Witness type at each message index for the iterated sumcheck step (counterpart of BBF `foldWitMid`).
  At m=0,1 we have input-round witness; at m=2 we have output-round witness so extractOut can be identity. -/
def iteratedSumcheckWitMid (i : Fin ℓ') : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨2, _⟩ => SumcheckWitness L ℓ' i.succ

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both SumcheckWitness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1: extract backward from output witness using input challenges
      {
        t' := witMidSucc.t',
        H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witMidSucc.t')
          (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
          (i := i.castSucc) (challenges := stmtIn.challenges)
      }
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-- KState for the iterated sumcheck step, matching the structure of Binary Basefold's `foldKStateProp`:
- m=0: same as relIn (masterKStateProp at i.castSucc with sumcheckConsistencyProp)
- m=1: after P sends hᵢ(X), before V sends r'ᵢ (explicitVCheck ∧ localizedRoundPolyCheck)
- m=2: after V sends r'ᵢ — OUTPUT state (masterKStateProp at i.succ with stmtOut, witMid, sumcheckConsistencyProp)
  At m=2, witMid has type SumcheckWitness i.succ (via iteratedSumcheckWitMid). -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmtMid : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (witMid : iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i) m)
    (oStmtMid : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as relIn (sumcheckRoundRelation at i.castSucc)
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H)

  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r'ᵢ
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' 𝓑 (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks :=
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )

  | ⟨2, _⟩ => -- After V sends r'ᵢ: use OUTPUT state (witMid is already SumcheckWitness i.succ)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ :=
      sumcheckVerifierStmtOut (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') i stmtMid h_i r_i'
    let oStmtOut := oStmtMid
    let witOut := witMid
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.succ)
      (stmt := stmtOut) (oStmt := oStmtOut) (wit := witOut)
      (localChecks :=
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
        sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H
      )

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmtMid := stmt) (witMid := witMid) (oStmtMid := oStmt)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    simp only [iteratedSumcheckKStateProp, sumcheckRoundRelation, sumcheckRoundRelationProp,
      Set.mem_setOf_eq, Fin.coe_castSucc, cast_eq]
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
    unfold iteratedSumcheckKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]

    -- At round 1: masterKStateProp with (explicitVCheck ∧ localizedRoundPolyCheck)
    -- At round 0: masterKStateProp with sumcheckConsistencyProp
    -- Extract the checks from round 1
    obtain ⟨⟨h_explicit, h_localized⟩, h_core⟩ := h_kState_round1

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
    --   and ((stmtOut, oStmtOut), witOut) ∈ sumcheckRoundRelation at i.succ
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      exists_prop] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩

    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [iteratedSumcheckOracleVerifier]
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

    dsimp only [sumcheckRoundRelation, sumcheckRoundRelationProp, masterKStateProp] at h_relOut
    simp only [Fin.val_succ, Set.mem_setOf_eq] at h_relOut
    dsimp only [iteratedSumcheckKStateProp]
    set h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩ with h_i_def
    set r_i' : L := tr.challenges ⟨1, rfl⟩ with h_i_def

    set extractedWitLast : SumcheckWitness L ℓ' i.succ :=
      (iteratedSumcheckRbrExtractor κ (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (β := β)
        (h_l := h_l) aOStmtIn i).extractOut (stmtIn, oStmtIn) tr witOut

    have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by
      rw [h_oStmtOut_eq]
      funext j
      simp only [MessageIdx, Function.Embedding.coeFn_mk, Sum.inl.injEq,
        OracleVerifier.mkVerifierOStmtOut_inl, cast_eq]
    rw [h_oStmtOut_eq_oStmtIn] at h_relOut
    dsimp only [sumcheckVerifierStmtOut]

    have h_stmtOut_sumcheck_target_eq : stmtOut.sumcheck_target = (Polynomial.eval r_i' ↑h_i) := by
      rw [h_stmtOut_eq]; rfl
    dsimp only [masterKStateProp]
    constructor
    · constructor
      · simpa [h_i_def] using h_V_check_passed
      · rw [h_stmtOut_sumcheck_target_eq] at h_relOut
        exact h_relOut.1
    · obtain ⟨h_wit_struct_In, h_oStmtIn_compat⟩ := h_relOut.2
      constructor
      · -- witnessStructuralInvariant
        unfold witnessStructuralInvariant at h_wit_struct_In ⊢
        dsimp only [Fin.val_succ]
        rw [h_stmtOut_eq] at h_wit_struct_In
        exact h_wit_struct_In
      · -- initialCompatibility
        exact h_oStmtIn_compat

/-- Extraction failure implies a witness-dependent bad sumcheck event (no folding here).
  The extracted `witMid` also carries oracle compatibility at the same `oStmt`. -/
lemma iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) (r_i' : L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
        (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn (init := init) (impl := impl) i)
      (extractor := iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i)
      (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := FullTranscript.mk1 h_i)
      (challenge := r_i')) :
    ∃ witMid : SumcheckWitness L ℓ' i.succ,
      aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2) ∧
      let witBefore : SumcheckWitness L ℓ' i.castSucc :=
        (iteratedSumcheckRbrExtractor.{0,0,0} κ L K β ℓ ℓ' h_l aOStmtIn i).extractMid
          (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid
      let h_star : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' 𝓑 (i := i) (h := witBefore.H)
      badSumcheckEventProp r_i' h_i h_star := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [iteratedSumcheckKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold iteratedSumcheckKStateProp at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd] at h_kState_before_false h_kState_after_true
  simp only [Transcript.concat, sumcheckVerifierStmtOut] at h_kState_before_false h_kState_after_true
  unfold masterKStateProp witnessStructuralInvariant at h_kState_before_false h_kState_after_true
  simp only [iteratedSumcheckRbrExtractor, Fin.isValue] at h_kState_before_false h_kState_after_true
  have h_explicit_after :
      h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtOStmtIn.1.sumcheck_target := by
    simpa using h_kState_after_true.1.1
  have h_sumcheck_after :
      sumcheckConsistencyProp (𝓑 := 𝓑) (Polynomial.eval r_i' h_i.val) witMid.H := by
    simpa using h_kState_after_true.1.2
  have h_wit_struct_after :
      witMid.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witMid.t')
        (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOStmtIn.1.ctx)
        (i := i.succ) (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i') := by
    simpa using h_kState_after_true.2.1
  have h_init_compat : aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2)
    := h_kState_after_true.2.2
  let H_before : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)] :=
    projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witMid.t')
      (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOStmtIn.1.ctx)
      (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
  let h_star_extracted : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' 𝓑 (i := i) (h := H_before)
  have h_eval_eq_extracted : Polynomial.eval r_i' h_i.val
    = Polynomial.eval r_i' h_star_extracted.val := by
    unfold sumcheckConsistencyProp at h_sumcheck_after
    rw [h_wit_struct_after] at h_sumcheck_after
    rw [projectToMidSumcheckPoly_succ (L := L) (ℓ := ℓ') (t := witMid.t')
      (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOStmtIn.1.ctx)
      (i := i) (challenges := stmtOStmtIn.1.challenges) (r_i' := r_i')] at h_sumcheck_after
    have h_sum_eq :=
      projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := 𝓑) (ℓ := ℓ')
        (i := i) (Hᵢ := H_before) (rᵢ := r_i')
    have h_sum_eq' :
        Polynomial.eval r_i' h_star_extracted.val =
          ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - i.succ),
            (projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i) (Hᵢ := H_before)
              (rᵢ := r_i')).val.eval x := by
      simpa [h_star_extracted] using h_sum_eq
    calc
      Polynomial.eval r_i' h_i.val
          = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - i.succ),
              (projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i) (Hᵢ := H_before)
                (rᵢ := r_i')).val.eval x := h_sumcheck_after
      _ = Polynomial.eval r_i' h_star_extracted.val := by
        symm
        exact h_sum_eq'
  have h_hi_ne_extracted : h_i ≠ h_star_extracted := by
    intro h_eq
    apply h_kState_before_false
    constructor
    · constructor
      · exact h_explicit_after
      · simpa [h_star_extracted] using h_eq
    · constructor
      · -- The middle conjunct at m=1 simplifies to `True`.
        trivial
      · -- initialCompatibility is preserved by extractMid(m=1) since t' is unchanged.
        simpa [iteratedSumcheckRbrExtractor, Fin.isValue] using h_init_compat
  have h_bad_extracted : badSumcheckEventProp r_i' h_i h_star_extracted := by
    refine ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
  refine ⟨witMid, h_init_compat, ?_⟩
  simpa [h_star_extracted, H_before, iteratedSumcheckRbrExtractor, Fin.isValue] using h_bad_extracted

/-- Per-transcript bound: for prover message h_i, the probability (over verifier challenge y)
  that extraction fails is at most iteratedSumcheckRoundKnowledgeError (2/|L|).
  Counterpart of BBF `foldStep_doom_escape_probability_bound`; no folding bad event here. -/
lemma iteratedSumcheck_doom_escape_probability_bound (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
          (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      iteratedSumcheckRoundKnowledgeError L ℓ' i := by
  classical
  let compatPred : MultilinearPoly L ℓ' → Prop := fun t =>
    aOStmtIn.initialCompatibility (t, stmtOStmtIn.2)
  by_cases hCompat : ∃ t : MultilinearPoly L ℓ', compatPred t
  · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
    let H_fixed : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)] :=
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t_fixed)
        (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOStmtIn.1.ctx)
        (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
    let h_star_fixed : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' 𝓑 (i := i) (h := H_fixed)
    have h_prob_mono := prob_mono (D := $ᵖ L)
      (f := fun y => rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
          (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y)
      (g := fun y => badSumcheckEventProp y h_i h_star_fixed)
      (h_imp := by
        intro y h_doom
        obtain ⟨witMid, h_mid_compat, h_bad_extracted⟩ :=
          iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck
            (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (impl := impl) (init := init)
            (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i) (r_i' := y)
            (doomEscape := h_doom)
        have h_t_eq : witMid.t' = t_fixed :=
          aOStmtIn.initialCompatibility_unique stmtOStmtIn.2 witMid.t' t_fixed
            h_mid_compat h_t_fixed_compat
        simpa [h_star_fixed, H_fixed, iteratedSumcheckRbrExtractor, Fin.isValue, h_t_eq]
          using h_bad_extracted)
    apply le_trans h_prob_mono
    have h_sz := probability_bound_badSumcheckEventProp (h_i := h_i) (h_star := h_star_fixed)
    conv_rhs =>
      dsimp only [iteratedSumcheckRoundKnowledgeError]
      rw [ENNReal.coe_div (hr := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
        not_false_eq_true])]
      simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
    exact h_sz
  · have h_prob_mono_false := prob_mono (D := $ᵖ L)
      (f := fun y => rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
          (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y)
      (g := fun _ => False)
      (h_imp := by
        intro y h_doom
        obtain ⟨witMid, h_mid_compat, _h_bad_extracted⟩ :=
          iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck
            (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (impl := impl) (init := init)
            (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i) (r_i' := y)
            (doomEscape := h_doom)
        exact (hCompat ⟨witMid.t', h_mid_compat⟩).elim)
    refine le_trans h_prob_mono_false ?_
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ')
      (𝓑:=𝓑) (β := β) (h_l := h_l) aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.succ)
      (rbrKnowledgeError := fun _ => iteratedSumcheckRoundKnowledgeError L ℓ' i) := by
  classical
  apply OracleReduction.unroll_rbrKnowledgeSoundness
    (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K)
    (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn i)
  intro stmtOStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K)
    (ℓ := ℓ) (ℓ' := ℓ') (β := β) (𝓑 := 𝓑) (h_l := h_l) aOStmtIn (impl := impl) (init := init) i)
    (iteratedSumcheckRbrExtractor κ (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (β := β) (h_l := h_l) aOStmtIn i)
    j
    stmtOStmtIn
  rw [OracleReduction.probEvent_soundness_goal_unroll_log' (pSpec := pSpecFold
    (L := L)) (P := P) (impl := impl) (prover := prover) (i := j) (stmt := stmtOStmtIn)
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
    -- Apply the per-transcript bound (Ring-switching counterpart of foldStep_doom_escape_probability_bound)
    exact iteratedSumcheck_doom_escape_probability_bound (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓑 := 𝓑) (β := β) (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i) (stmtOStmtIn := stmtOStmtIn)
      (h_i := x.1.1)
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply OracleComp.tsum_probOutput_le_one

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check: validates that s_{ℓ'} = eq_tilde_eval * s'.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁ (r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
Then `V` computes the final eq value: `(Σ_{u ∈ {0,1}^κ} eq̃ (u_0, ..., u_{κ-1},`
  `r''_0, ..., r''_{κ-1}) ⋅ e_u)`
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_ {κ-1},`
  `r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`. -/
@[reducible]
def finalSumcheckVerifierCheck
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (s' : L) : Prop :=
  let eq_tilde_eval : L := compute_final_eq_value κ L K β ℓ ℓ' h_l
    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  stmtIn.sumcheck_target = eq_tilde_eval * s'

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def finalSumcheckVerifierStmtOut
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (s' : L) : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }

/-- Pure prover message computation: computes s' from the witness. -/
@[reducible]
def finalSumcheckProverComputeMsg
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')) : L :=
  witIn.t'.val.eval stmtIn.challenges

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def finalSumcheckProverWitOut (witIn : SumcheckWitness L ℓ' (Fin.last ℓ')) : WitMLP L ℓ' :=
    { t := witIn.t' }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the final sumcheck step.
This is a 1-message protocol where the prover sends the final constant s'. -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
      (SumcheckWitness L ℓ' (Fin.last ℓ'))
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (MLPEvalStatement L ℓ')
      (WitMLP L ℓ')
      (pSpecFinalSumcheckStep (L := L)) where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ')

  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ aOStmtIn.toStrictRelInput

  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)

  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K ℓ ℓ' stmtIn (transcript.messages ⟨0, rfl⟩)

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

  honestProverTranscript := fun stmtIn witIn _oStmtIn _chal =>
    let s' : L := finalSumcheckProverComputeMsg κ L K ℓ ℓ' witIn stmtIn
    FullTranscript.mk1 s'

  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let s' : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K ℓ ℓ' stmtIn s'
    let witOut := finalSumcheckProverWitOut (L := L) (ℓ' := ℓ') witIn
    ((stmtOut, oStmtIn), witOut)

/-! ## Helper Lemmas for Strong Completeness -/

omit [Fintype L] [DecidableEq L] [CharP L 2] [SelectableType L] [NeZero ℓ'] in
/-- At `Fin.last ℓ'`, the sumcheck consistency sum is over 0 variables,
simplifying to a single evaluation. This is analogous to Binary Basefold's
simplification of `𝓑^ᶠ(0) = {∅}`. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - Fin.last ℓ')])
    (h_cons : sumcheckConsistencyProp (𝓑 := 𝓑) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  -- Since ℓ' - Fin.last ℓ' = 0, the sum is over Fin 0 which has only one element
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [sumcheckConsistencyProp] at h_cons
  -- The piFinset over Fin 0 has only one element: fun _ => 0
  haveI : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso; apply hb_ne
      funext i;
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso; apply h_not_mem
      simp only [Fintype.mem_piFinset]
      intro i; simp only [tsub_self] at i; exact i.elim0)] at h_cons
  exact h_cons

omit [NeZero κ] [Fintype L] [DecidableEq L] [CharP L 2] [SelectableType L]
  [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- The honest prover's message in the final sumcheck step equals `t'(challenges)`. -/
lemma finalSumcheck_honest_message_eq_t'_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.t'.val.eval stmtIn.challenges := by
  -- Direct from the definition of honestProverTranscript
  simp only [finalSumcheckStepLogic, finalSumcheckProverComputeMsg]

/-- **Main helper lemma**: The verifier check passes in the final sumcheck step.

**Proof Structure** (following Binary Basefold's `finalSumcheckStep_verifierCheck_passed`):
1. From `sumcheckConsistencyProp`:
   - `stmtIn.sumcheck_target = ∑ x ∈ 𝓑^ᶠ(0), witIn.H.val.eval x`
   - Since `𝓑^ᶠ(0) = {∅}`, this simplifies to `witIn.H.val.eval (fun _ => 0)`

2. From `witnessStructuralInvariant`:
   - `witIn.H = projectToMidSumcheckPoly t' (m := A_MLE) (Fin.last ℓ') challenges`
   - Using `projectToMidSumcheckPoly_at_last_eval`:
   - `witIn.H.val.eval (fun _ => 0) = A_MLE.eval(challenges) * t'.eval(challenges)`

3. `A_MLE.eval(challenges) = compute_final_eq_value ...` by definition.

4. Combining gives: `target = compute_final_eq_value * t'(challenges) = compute_final_eq_value * s'`
-/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : witnessStructuralInvariant κ L K β ℓ ℓ' h_l stmtIn witIn) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  intro step transcript
  -- Step 1: Simplify sumcheck consistency to single evaluation
  have h_target_eq_H_eval : stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => 0) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ' := ℓ') (𝓑 := 𝓑)
      stmtIn.sumcheck_target witIn.H h_sumcheck_cons

  -- Step 2: Use witnessStructuralInvariant to connect H to projected poly
  have h_H_eq : witIn.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t')
    (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx)
    (i := Fin.last ℓ') (challenges := stmtIn.challenges) := h_wit_struct

  -- Step 3: Apply projectToMidSumcheckPoly_at_last_eval
  have h_proj_eval : (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t')
    (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx)
    (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => 0) =
    ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly
      stmtIn.ctx).val.eval stmtIn.challenges * witIn.t'.val.eval stmtIn.challenges := by
      apply projectToMidSumcheckPoly_at_last_eval

  -- Step 4: Connect multiplier poly to compute_final_eq_value
  -- This requires showing that A_MLE.eval(challenges) = compute_final_eq_value
  have h_mult_eq_eq_value : ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval stmtIn.challenges =
    compute_final_eq_value κ L K β ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
      compute_A_MLE_eval_eq_final_eq_value κ L K β ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching

  -- Step 5: Get the honest message
  have h_msg_eq : transcript.messages ⟨0, rfl⟩ = witIn.t'.val.eval stmtIn.challenges :=
    finalSumcheck_honest_message_eq_t'_eval κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn stmtIn witIn oStmtIn challenges

  -- Step 6: Combine everything
  simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierCheck]
  rw [h_target_eq_H_eval, Subtype.val_inj.mpr h_H_eq, h_proj_eval, h_mult_eq_eq_value, h_msg_eq]

/-! ## Strong Completeness Theorem -/

/-- Final sumcheck step logic is strongly complete.
**Key Proof Obligations:**
1. **Verifier Check**: Show that `stmtIn.sumcheck_target = eq_tilde_eval * s'` where `s' = witIn.t'.val.eval stmtIn.challenges`
   - This should follow from `h_relIn` (sumcheckRoundRelation) which includes `masterKStateProp`
   - The `masterKStateProp` includes:
     * `witnessStructuralInvariant`: `wit.H = projectToMidSumcheckPoly ...`
     * `sumcheckConsistencyProp`: `stmt.sumcheck_target = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - Fin.last ℓ'), wit.H.val.eval x`
       For `i = Fin.last ℓ'`, we have `ℓ' - Fin.last ℓ' = 0`, so this is a sum over 0 variables (a constant)
   - Need to connect these properties to show the verifier check passes

2. **Relation Out**: Show that the output satisfies `aOStmtIn.toStrictRelInput`
   - This involves showing `MLPEvalRelation` and `strictInitialCompatibility` hold for the output
-/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  let s' := transcript.messages ⟨0, rfl⟩

  -- Extract properties from h_relIn BEFORE any simp changes its structure
  simp only [finalSumcheckStepLogic, strictSumcheckRoundRelation,
    strictSumcheckRoundRelationProp, Set.mem_setOf_eq, masterStrictKStateProp] at h_relIn
  obtain ⟨h_sumcheck_cons, h_wit_struct, h_oStmtIn_compat⟩ := h_relIn

  -- Fact 1: Verifier check passes (using the helper lemma)
  let h_VCheck_passed : step.verifierCheck stmtIn transcript :=
    finalSumcheckStep_verifierCheck_passed κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
      stmtIn witIn oStmtIn challenges h_sumcheck_cons h_wit_struct

  -- Fact 2: Prover and verifier statements agree
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic,
      finalSumcheckVerifierStmtOut, finalSumcheckProverWitOut]

  -- Fact 3: Prover and verifier oracle statements agree (no new oracles added)
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl

  -- Fact 4: Output relation holds
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, finalSumcheckStepLogic]
    constructor
    · -- MLPEvalRelation: stmtOut.original_claim = witOut.t.val.eval stmtOut.t_eval_point
      rfl
    · -- initial Compatibility
      exact h_oStmtIn_compat

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

/-! ## Prover and Verifier Implementation -/

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' := finalSumcheckProverComputeMsg κ L K ℓ ℓ' witIn stmtIn
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `s'` from the prover's message
    let s' : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ) ⟨0, rfl⟩ ()

    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) s'

    -- Get the logic instance
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn

    -- Use guard for verifier check (fails if check doesn't pass)
    have : Decidable (logic.verifierCheck stmtIn t) := Classical.propDecidable _
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  embed := (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).embed
  hEq := (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).hEq

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
  verifier := finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp))
  (hInit : init.neverFails) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (relIn := strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toStrictRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
      (init := init) (impl := impl) := by
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

  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    -- Step 2e: Apply the logic completeness lemma
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete
    κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) aOStmtIn

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
      liftComp_pure, support_pure, Set.mem_singleton_iff] at hInputState_mem_support
    -- Now we get equality: hInputState_mem_support : inputState
      -- = (witIn.f ⟨0, ⋯⟩, stmtIn, oStmtIn, witIn, witIn.f ⟨0, ⋯⟩)
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

    -- -- Apply FiniteRange instances for oracle simulation (defined in Spec.lean)
    -- haveI : [fun j => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    --   (Fin.last ℓ) j]ₒ.FiniteRange := by
    --     apply instFiniteRangeOracleStatementFinLast
    -- haveI : [(pSpecFinalSumcheckStep (L := L)).Message]ₒ.FiniteRange :=
    --   instFiniteRangePSpecFinalSumcheckStepMessage
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
      obtain ⟨h_V_check, h_relOut, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
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
    obtain ⟨h_V_check, h_relOut, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
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
    -- Step 2g: Rewrite all variables to their concrete values
    rw [
      h_ver_stmtOut_eq_support, h_ver_stmtOut_eq,
      h_ver_oracle_eq_support,  h_ver_OstmtOut_eq,
      h_wit_eq_support,         h_logic_wit, -- should use because both witnesses are not trivial
      h_prv_stmtOut_eq_support, h_logic_stmt,
      h_prv_oracle_eq_support,  h_logic_oracle
    ]

    -- Step 2h: Complete the proof using logic properties
    constructor
    · -- relOut holds
      exact h_relOut
    · -- Prover and verifier agree
      constructor
      · rfl  -- Statement agreement
      · exact h_agree.2  -- Oracle agreement

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

/-- The round-by-round extractor for the final sumcheck step.
  We do not collapse the witness away (unlike BBF): WitMid stays as full SumcheckWitness,
  and we pass the polynomial t' (WitMLP) plus MLPEvalStatement to a final PCS invocation. -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc

  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t)
      (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/-- KState for the final sumcheck step, in the same style as BBF `finalSumcheckKStateProp`:
  m=0: same as relIn (masterKStateProp with sumcheckConsistencyProp).
  m=1: name prover message as `c`, build output statement `stmtOut`, then
  sumcheckFinalCheck ∧ finalEvalCheck ∧ oracleCompatProp
    (no folding; RS has only sumcheck + oracle compat). -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmtIn) (oStmt := oStmtIn) (wit := witMid)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)

  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges,
      original_claim := c
    }
    let sumcheckFinalVCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K β ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
      stmtIn.sumcheck_target = eq_tilde_eval * c
    let finalEvalCheck : Prop := witMid.t'.val.eval stmtOut.t_eval_point = stmtOut.original_claim
    let oracleCompatProp : Prop := aOStmtIn.initialCompatibility ⟨witMid.t', oStmtIn⟩
    let witnessStructProp : Prop := witnessStructuralInvariant κ L K β ℓ ℓ' h_l stmtIn witMid

    sumcheckFinalVCheck ∧ finalEvalCheck ∧ oracleCompatProp ∧ witnessStructProp

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K β ℓ ℓ' h_l
    (m := m) (tr := tr) (stmtIn := stmt) (witMid := witMid) (oStmtIn := oStmt)
  toFun_empty := fun stmt witMid => by rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- Only round is m=0 → m=1; extractMid is identity (RS keeps full SumcheckWitness).
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]

    intro h_kState_round1
    unfold finalSumcheckKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
      at h_kState_round1

    -- m=1 gives: sumcheckFinalCheck ∧ finalEvalCheck ∧ oracleCompatProp ∧ witnessStructProp
    obtain ⟨h_sumcheckFinalCheck, h_finalEvalCheck, h_oracleCompat, h_witStruct⟩ := h_kState_round1

    -- Goal: masterKStateProp at m=0 = sumcheckConsistencyProp ∧ witnessStructuralInvariant ∧ initialCompatibility
    unfold RingSwitching.masterKStateProp
    constructor
    · -- sumcheckConsistencyProp: at Fin.last ℓ' the sum is a single term witMid.H.val.eval (fun _ => 0)
      unfold sumcheckConsistencyProp
      simp only [Fin.val_last]
      -- haveI : IsEmpty (Fin 0) := Fin.isEmpty
      rw [Finset.sum_eq_single (a := fun _ => (0 : L))
        (h₀ := fun b _ hb_ne => by
          exfalso; apply hb_ne
          funext i; simp only [tsub_self] at i; exact i.elim0)
        (h₁ := fun h_not_mem => by
          exfalso; apply h_not_mem
          simp only [Fintype.mem_piFinset]
          intro i; simp only [tsub_self] at i; exact i.elim0)]
      simp only [finalSumcheckRbrExtractor]
      have h_H_eval : witMid.H.val.eval (fun _ => 0) =
          ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
            stmtIn.challenges * witMid.t'.val.eval stmtIn.challenges := by
        rw [h_witStruct]
        apply projectToMidSumcheckPoly_at_last_eval
      have h_mult_eq : ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
          stmtIn.challenges = compute_final_eq_value κ L K β ℓ ℓ' h_l stmtIn.ctx.t_eval_point
          stmtIn.challenges stmtIn.ctx.r_batching :=
        compute_A_MLE_eval_eq_final_eq_value κ L K β ℓ ℓ' h_l
          stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
      refine Eq.trans h_sumcheckFinalCheck ?_
      let msgIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨⟨0, Nat.zero_lt_succ 0⟩, hDir⟩
      let c : L := FullTranscript.messages (Transcript.concat msg tr) msgIdx
      have h_eq : (MvPolynomial.eval stmtIn.challenges) (((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
          (MvPolynomial.eval stmtIn.challenges) witMid.t'.val =
          (compute_final_eq_value κ L K β ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges
            stmtIn.ctx.r_batching) * c := by
        rw [h_mult_eq]
        simp_rw [Fin.val_last]
        rw [h_finalEvalCheck]; rfl
      exact (h_H_eval.trans h_eq).symm
    · constructor
      · exact h_witStruct
      · exact h_oracleCompat
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
  -- Same pattern as relay: verifier output (stmtOut, oStmtOut) + h_relOut ⇒ commitKStateProp 1
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      exists_prop] at probEvent_relOut_gt_0
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
    simp only [AbstractOStmtIn.toRelInput, MLPEvalRelation, Set.mem_setOf_eq] at h_relOut

    -- Goal: commitKStateProp 1 stmtIn oStmtIn tr witOut
    unfold finalSumcheckKStateProp
    -- Unfold the sendMessage, receiveChallenge, output logic of prover
    dsimp only
    -- stmtOut = stmtIn; need oStmtOut = snoc_oracle oStmtIn witOut.f so goal matches h_relOut
    simp only [h_stmtOut_eq] at h_relOut ⊢
    have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
    -- c equals tr.messages ⟨0, rfl⟩

    constructor
    · -- First conjunct: V checks sumcheck_target = eqTilde r challenges * c
      rw [h_init_value_mem_support]; rfl
    · -- Second conjunct: finalSumcheckStepFoldingStateProp ({ toStatement := stmtIn, final_constant := c }, oStmtIn)
      rw [h_oStmtOut_eq_oStmtIn] at h_relOut
      constructor
      · exact h_relOut.1
      · constructor
        · exact h_relOut.2
        · dsimp only [witnessStructuralInvariant, finalSumcheckRbrExtractor]

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := finalSumcheckKnowledgeError (L := L)) := by
  use (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
  use finalSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn
  use finalSumcheckKnowledgeStateFunction κ L K β ℓ ℓ' h_l aOStmtIn init impl
  intro stmtIn witIn prover ⟨j, hj⟩
  -- pSpecFinalSumcheckStep has 1 message (ChallengeIdx = Fin 1); same pattern as commit
  cases j using Fin.cases with
  | zero => simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
    Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' => exact Fin.elim0 j'

end FinalSumcheckStep

section LargeFieldReduction

/-- Composed oracle verifier for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleVerifier :=
  OracleVerifier.seqCompose (m := ℓ') (oSpec := []ₒ)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ))
    (V := fun (i: Fin ℓ') => iteratedSumcheckOracleVerifier κ (𝓑 := 𝓑) L K β ℓ ℓ' h_l aOStmtIn i)

/-- Composed oracle reduction for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckLoop L ℓ')
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := SumcheckWitness L ℓ' (Fin.last ℓ')) :=
  OracleReduction.seqCompose (m:=ℓ') (oSpec:=[]ₒ)
    (OStmt := fun _ => (aOStmtIn.OStmtIn (L := L) (ℓ' := ℓ')))
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (Oₘ := fun _ j => instOracleInterfaceMessagePSpecSumcheckRound L j)
    (R := fun (i : Fin ℓ') =>
      iteratedSumcheckOracleReduction (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (i := i))

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheckStep (L := L))

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheckStep (L := L))

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness (hInit : init.neverFails) :
  OracleReduction.perfectCompleteness
    (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (relIn := strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (relOut := aOStmtIn.toStrictRelInput)
    (init := init)
    (impl := impl) := by
  -- Follows from append_perfectCompleteness of interactionPhase and finalSumcheck
  apply OracleReduction.append_perfectCompleteness
    (rel₂ := (strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l aOStmtIn (Fin.last ℓ')))
  · exact OracleReduction.seqCompose_perfectCompleteness (hInit:=hInit)
      (rel := fun i => strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i)
      (R := fun i => iteratedSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)
      (h := fun i =>
        iteratedSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
          (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (𝓑:=𝓑) (aOStmtIn:=aOStmtIn)
          (init:=init) (impl:=impl) (hInit:=hInit) i
      )
  · exact finalSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
      (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl) hInit

/-- standard sumcheck error -/
def coreInteractionRbrKnowledgeError (_ : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  (2 : ℝ≥0) / (Fintype.card L) -- this terms comes from the sumcheck
    -- steps, i.e. iteratedSumcheckRoundKnowledgeError

/-- RBR knowledge soundness for the sumcheck loop (seqCompose over ℓ'). -/
theorem sumcheckLoopOracleVerifier_rbrKnowledgeSoundness :
  (sumcheckLoopOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) aOStmtIn).rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn 0)
    (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ'))
    (rbrKnowledgeError := fun _ => (2 : ℝ≥0) / Fintype.card L) :=
  OracleVerifier.seqCompose_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel := fun i => sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)
    (V := fun i => iteratedSumcheckOracleVerifier κ (𝓑 := 𝓑) L K β ℓ ℓ' h_l aOStmtIn i)
    (rbrKnowledgeError := fun roundIdx _challengeIdx =>
      -- Each round has exactly one challenge, so _challengeIdx is not used in the error
      iteratedSumcheckRoundKnowledgeError L ℓ' roundIdx)
    (h := fun i =>
      iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)

/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := coreInteractionOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (init := init)
    (impl := impl)
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  let hAppend := OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn 0)
    (rel₂ := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ'))
    (rel₃ := aOStmtIn.toRelInput)
    (V₁ := sumcheckLoopOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (V₂ := finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (rbrKnowledgeError₁ := fun _ => (2 : ℝ≥0) / Fintype.card L)
    (rbrKnowledgeError₂ := finalSumcheckKnowledgeError (L := L))
    (h₁ := by
      simpa using (sumcheckLoopOracleVerifier_rbrKnowledgeSoundness
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
    )
    (h₂ := by
      simpa using (finalSumcheckOracleVerifier_rbrKnowledgeSoundness
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
    )
  exact OracleVerifier.rbrKnowledgeSoundness_of_eq_error
    (init := init) (impl := impl)
    (h_ε := by
      intro i
      change (2 : ℝ≥0) / Fintype.card L =
        ((fun _ => (2 : ℝ≥0) / Fintype.card L) ⊕ᵥ finalSumcheckKnowledgeError (L := L))
          (ChallengeIdx.sumEquiv.symm i)
      rcases h_idx : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
      · simp
      · rcases i₂ with ⟨j, hj⟩
        cases j using Fin.cases with
        | zero =>
            exfalso
            simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true,
              Fin.isValue, Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
        | succ j' => exact Fin.elim0 j'
    )
    (h := hAppend)

end LargeFieldReduction
end
end Binius.RingSwitching.SumcheckPhase
