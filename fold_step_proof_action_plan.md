# Fold Step RBR KS: Concrete Action Plan

## Overview
This document provides a step-by-step plan to complete the RBR knowledge soundness proof for the fold step in Binary Basefold.

**Current Status**: 3 critical properties unproved (marked with `sorry` in `Steps2.lean`)
**Goal**: Complete all proofs for `foldOracleVerifier_rbrKnowledgeSoundness`

---

## Phase 1: Foundation Lemmas [Priority: CRITICAL]

### Task 1.1: Round Polynomial Evaluation Lemma
**File**: `ArkLib/ProofSystem/Binius/BinaryBasefold/RoundPolyProperties.lean` (new file)
**Estimated Time**: 2-3 hours

**Goal**: Prove that the round polynomial computed from a consistent H satisfies the sumcheck equation.

```lean
/-- The round polynomial from a consistent multilinear polynomial sums correctly -/
lemma getSumcheckRoundPoly_eval_sum 
  (h_consistent : sumcheckConsistencyProp (𝓑 := 𝓑) s H) :
  let h_star := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H)
  h_star.val.eval (𝓑 0) + h_star.val.eval (𝓑 1) = s := by
  -- Strategy:
  -- 1. Unfold getSumcheckRoundPoly definition
  -- 2. Use sumcheckConsistencyProp to relate H evaluations to s
  -- 3. Show the sum equals the original target
  sorry
```

**Dependencies**: 
- `getSumcheckRoundPoly` definition
- `sumcheckConsistencyProp` definition
- Basic polynomial evaluation lemmas

**Test**: Apply this to prove a simple case for ℓ=1

---

### Task 1.2: Round Polynomial Uniqueness
**File**: Same as 1.1
**Estimated Time**: 1-2 hours

```lean
/-- If two polynomials agree on evaluation, they are equal up to degree bound -/
lemma poly_equality_from_evals 
  (h1 : p.eval (𝓑 0) + p.eval (𝓑 1) = s)
  (h2 : p = getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H)) :
  sumcheckConsistencyProp s H := by
  -- Strategy:
  -- 1. Use h2 to get structure of p
  -- 2. Apply h1 and properties of getSumcheckRoundPoly
  -- 3. Derive sumcheckConsistencyProp
  sorry
```

---

### Task 1.3: Oracle Statement Preservation Through Fold
**File**: `ArkLib/ProofSystem/Binius/BinaryBasefold/OraclePreservation.lean` (new file)
**Estimated Time**: 2-3 hours

```lean
/-- In fold step, oracle statements are preserved via embedding -/
lemma foldStep_oracle_agreement 
  (i : Fin ℓ)
  (stmtIn : Statement (L := L) Context i.castSucc)
  (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
  (witIn : Witness 𝔽q β i.castSucc)
  (h_relIn : ((stmtIn, oStmtIn), witIn) ∈ 
    strictRoundRelation 𝔽q β i.castSucc)
  (transcript : FullTranscript (pSpecFold (L := L))) :
  let logic := foldStepLogic 𝔽q β i
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut 
    logic.embed logic.hEq oStmtIn transcript
  verifierOStmtOut = oStmtIn := by
  -- Strategy:
  -- 1. Unfold mkVerifierOStmtOut
  -- 2. Case split on logic.embed
  -- 3. For Sum.inl j: immediate by hEq
  -- 4. For Sum.inr (message): no messages add oracles in fold
  sorry
```

**Key Insight**: The fold step uses `Sum.inl` mapping exclusively, so all oracles are preserved from input.

---

### Task 1.4: Schwartz-Zippel for Degree 1 Polynomials
**File**: `ArkLib/Data/Polynomial/Probability.lean` (enhance existing file)
**Estimated Time**: 4-6 hours

```lean
/-- Schwartz-Zippel lemma for univariate polynomials of degree ≤ 1 over finite fields -/
lemma schwartz_zippel_degree_one 
  [Fintype L] [Field L]
  (p q : L⦃≤ 1⦄[X])
  (h_ne : p ≠ q) :
  [fun r => p.val.eval r = q.val.eval r | uniform L] ≤ 
    (1 : ℝ≥0) / (Fintype.card L) := by
  -- Strategy:
  -- 1. Consider difference polynomial d = p - q
  -- 2. Show d ≠ 0 and deg d ≤ 1
  -- 3. A nonzero degree-1 polynomial has at most 1 root
  -- 4. Probability of hitting root ≤ 1/|L|
  sorry
```

**Dependencies**:
- Existing probability infrastructure
- Polynomial root counting lemmas
- May exist partially in mathlib

**Note**: Check if mathlib has this already - likely exists in some form.

---

## Phase 2: KState Property Proofs [Priority: HIGH]

### Task 2.1: Complete toFun_next (Steps2.lean:499-530)
**File**: `Steps2.lean`
**Estimated Time**: 3-4 hours
**Dependencies**: Tasks 1.1, 1.2

**Current Code**:
```lean
toFun_next := fun m hDir stmtIn tr msg witMid => by
  have h_m_eq_0 : m = 0 := by ...
  subst h_m_eq_0
  intro h_kState_round1
  -- Goal: Show round 0 KState from round 1 KState
  sorry
```

**Proof Outline**:
```lean
toFun_next := fun m hDir stmtIn tr msg witMid => by
  have h_m_eq_0 : m = 0 := by
    cases m using Fin.cases with
    | zero => rfl
    | succ m' => simp [pSpecFold, Matrix.cons_val_one] at hDir
  subst h_m_eq_0
  
  intro h_kState_round1
  
  -- Unfold both KState definitions
  unfold foldKStateProp at h_kState_round1 ⊢
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h_kState_round1 ⊢
  
  -- At round 1, we have masterKStateProp with:
  --   localChecks = explicitVCheck ∧ localizedRoundPolyCheck
  -- At round 0, we need masterKStateProp with:
  --   localChecks = sumcheckConsistencyProp
  
  -- Extract components from h_kState_round1
  obtain ⟨⟨h_explicit, h_localized⟩, h_core⟩ := h_kState_round1
  
  -- The core (badEventExists ∨ oracleWitnessConsistency) is identical
  constructor
  · -- Prove sumcheckConsistencyProp from h_explicit and h_localized
    -- h_localized says: h_i = h_star where h_star = getSumcheckRoundPoly(H)
    -- h_explicit says: h_i(0) + h_i(1) = stmt.sumcheck_target
    -- Use Task 1.2: this implies sumcheckConsistencyProp
    apply poly_equality_from_evals
    · rw [h_localized]; exact h_explicit
    · exact h_localized
  · exact h_core
```

**Verification**: Run on simple test case to ensure logic is sound.

---

### Task 2.2: Complete toFun_full (Steps2.lean:531-565)
**File**: `Steps2.lean`
**Estimated Time**: 4-5 hours
**Dependencies**: Task 1.3

**Current Code**:
```lean
toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut h_relOut => by
  simp at h_relOut
  rcases h_relOut with ⟨stmtOut, ⟨oStmtOut, h_conj⟩⟩
  have h_simulateQ := h_conj.1
  have h_foldStepRelOut := h_conj.2
  
  -- Two sorries:
  -- 1. Oracle agreement (line 546-551)
  -- 2. KState at round 2 (line 552-565)
  sorry
```

**Proof Outline**:
```lean
toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut h_relOut => by
  simp at h_relOut
  rcases h_relOut with ⟨stmtOut, ⟨oStmtOut, h_conj⟩⟩
  have h_simulateQ := h_conj.1
  have h_foldStepRelOut := h_conj.2
  
  -- Extract the witness
  set witLast := (foldRbrExtractor ...).extractOut ⟨stmtLast, oStmtLast⟩ tr witOut
  simp only [Fin.reduceLast, Fin.isValue]
  
  -- SORRY 1: Oracle agreement
  have h_oStmt : oStmtLast = oStmtOut := by
    -- The verifier's oracle output comes from mkVerifierOStmtOut
    -- which preserves all oracle statements (Task 1.3)
    have h_embed := (foldStepLogic ...).embed
    have h_hEq := (foldStepLogic ...).hEq
    
    -- From h_simulateQ, we know verifier computed oStmtOut
    -- From Task 1.3, verifier's oracle output equals input
    apply foldStep_oracle_agreement
    assumptions...
  
  -- SORRY 2: KState at round 2
  unfold foldKStateProp
  simp only [Fin.val_last]
  
  -- Goal: masterKStateProp at (i.castSucc, round 2) with:
  --   localChecks = localizedRoundPolyCheck ∧ nextSumcheckTargetCheck
  
  -- From h_foldStepRelOut, we have:
  --   masterKStateProp at i.succ with sumcheckConsistencyProp
  
  -- Key insight: foldStepRelOut structure matches round 2 requirements
  -- The extractor builds witLast to satisfy these constraints
  
  constructor
  · -- Local checks
    constructor
    · -- localizedRoundPolyCheck
      -- From relOut structure and verifier's computation
      sorry -- Need to extract from h_foldStepRelOut
    · -- nextSumcheckTargetCheck  
      -- From verifier's check passing
      sorry -- Need to extract from h_simulateQ
  · -- Core (badEventExists ∨ oracleWitnessConsistency)
    -- Inherited from foldStepRelOut
    sorry -- Extract from h_foldStepRelOut.masterKStateProp
```

**Note**: This requires understanding the exact structure of `foldStepRelOut` and how it relates to the round 2 KState.

---

## Phase 3: Main RBR KS Theorem [Priority: HIGH]

### Task 3.1: Complete foldOracleVerifier_rbrKnowledgeSoundness (Steps2.lean:568-605)
**File**: `Steps2.lean`
**Estimated Time**: 6-8 hours
**Dependencies**: Tasks 1.4, 2.1, 2.2

**Current Code**:
```lean
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
  (foldOracleVerifier ...).rbrKnowledgeSoundness ... := by
  use fun _ => Witness ...
  use foldRbrExtractor ...
  use foldKnowledgeStateFunction ...
  intro stmtIn witIn prover j
  -- Proof of doom escape bound
  sorry
```

**Proof Structure**:
```lean
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
  (foldOracleVerifier ...).rbrKnowledgeSoundness ... := by
  -- Provide witnesses
  use fun _ => Witness (L := L) 𝔽q β i.castSucc
  use foldRbrExtractor ...
  use foldKnowledgeStateFunction ...
  
  intro stmtIn witIn prover j
  
  -- j.val must be 1 (only challenge)
  have h_j_eq_1 : j.val = 1 := by ...
  
  -- Unfold the doom escape probability
  rw [rbrKnowledgeSoundness]
  
  -- Goal: Pr[¬KState(0) ∧ KState(2)] ≤ foldKnowledgeError(i)(j)
  
  -- Case analysis on why KState(0) is false:
  by_cases h_relIn : (stmtIn, witIn) ∈ relIn
  
  case pos =>
    -- If input is valid, KState(0) is true by toFun_empty
    -- So the event probability is 0
    simp [foldKnowledgeStateFunction]
    apply probEvent_eq_zero_iff.mpr
    intro state h_state
    -- Contradiction: KState(0) is true but assumed false
    have := (foldKnowledgeStateFunction ...).toFun_empty stmtIn witIn
    simp [h_relIn] at this
    exact absurd this ...
  
  case neg =>
    -- Input is invalid, so KState(0) is false
    -- For KState(2) to be true after random challenge:
    -- The prover must have sent h_i such that h_i(r_i') matches h_star(r_i')
    
    -- Two cases for doom escape:
    -- A. h_i = h_star (honest polynomial) - but then KState(1) would be true
    -- B. h_i ≠ h_star but h_i(r_i') = h_star(r_i') by luck
    
    -- Focus on case B (case A leads to contradiction):
    
    -- The key: if h_i ≠ h_star, agreement at random point is unlikely
    calc
      [fun ⟨transcript, challenge, _⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | ... prover execution ...] 
      ≤ [fun challenge => 
          let h_i := (extract from prover message)
          let h_star := (honest polynomial from witIn)
          h_i.eval challenge = h_star.eval challenge ∧ h_i ≠ h_star
        | challenge ← uniform L] + (bad event probability)
        := by
          -- Split event into polynomial disagreement + bad events
          apply probEvent_mono
          intro state h_state
          ... -- case analysis
      _ ≤ (1 : ℝ≥0) / Fintype.card L + (bad event probability)
        := by
          -- Apply Schwartz-Zippel (Task 1.4)
          apply schwartz_zippel_degree_one
          ... -- show h_i ≠ h_star
      _ = foldKnowledgeError 𝔽q β i j
        := by
          -- Definition of foldKnowledgeError
          unfold foldKnowledgeError
          simp only [h_j_eq_1]
          -- err_SC = 1/|L|
          -- err_BE = (conditional bad event term)
          ring_nf
```

**Critical Components**:
1. Extract h_i from prover's transcript
2. Show disagreement between h_i and h_star implies doom escape
3. Apply Schwartz-Zippel
4. Add bad event probability for commitment rounds
5. Match with error definition

---

## Phase 4: Testing & Validation [Priority: MEDIUM]

### Task 4.1: Create Test Cases
**File**: `ArkLib/ProofSystem/Binius/BinaryBasefold/Tests/FoldStepKS.lean` (new file)
**Estimated Time**: 2-3 hours

```lean
-- Test 1: Verify KState properties on small field
example : ... := foldOracleVerifier_rbrKnowledgeSoundness (L := ZMod 5) (ℓ := 1) (i := 0)

-- Test 2: Verify error bound computation
example : foldKnowledgeError (L := ZMod 7) (ℓ := 3) (i := 1) ⟨1, _⟩ = ...

-- Test 3: Verify toFun_next on concrete witness
example : ...
```

### Task 4.2: Verify Integration with Rest of Protocol
**Estimated Time**: 1-2 hours

- Check that fold step KS composes correctly with commit step
- Verify that error bounds accumulate properly
- Ensure no circular dependencies

---

## Implementation Schedule

### Week 1: Foundation
- **Days 1-2**: Tasks 1.1, 1.2 (Round polynomial lemmas)
- **Days 3-4**: Task 1.3 (Oracle preservation)
- **Day 5**: Task 1.4 (Schwartz-Zippel) - start

### Week 2: Core Proofs
- **Days 1-2**: Task 1.4 (Schwartz-Zippel) - complete
- **Days 3-4**: Task 2.1 (toFun_next)
- **Day 5**: Task 2.2 (toFun_full) - start

### Week 3: Completion
- **Days 1-2**: Task 2.2 (toFun_full) - complete
- **Days 3-5**: Task 3.1 (Main RBR KS theorem)

### Week 4: Testing & Cleanup
- **Days 1-2**: Task 4.1, 4.2 (Testing)
- **Days 3-4**: Documentation
- **Day 5**: Buffer for unexpected issues

---

## Risk Mitigation

### High Risk Items:
1. **Schwartz-Zippel formalization** - May be more complex than expected
   - Mitigation: Check mathlib early, adapt existing proofs
   
2. **Probability reasoning** - ProbComp infrastructure may be insufficient
   - Mitigation: Study existing probability proofs in codebase first

3. **Type constraints** - Complex type dependencies may cause issues
   - Mitigation: Use `#check` and `#print` extensively, keep types explicit

### Medium Risk Items:
1. **Oracle agreement lemma** - May require deep understanding of embedding
2. **Bad event probability** - Commitment round analysis may be subtle
3. **Integration** - Ensuring everything composes correctly

---

## Success Criteria

✅ **Completion Criteria**:
- [ ] All `sorry`s in `foldOracleVerifier_rbrKnowledgeSoundness` removed
- [ ] All `sorry`s in `foldKnowledgeStateFunction` removed
- [ ] Main theorem compiles and type checks
- [ ] Test cases pass
- [ ] No new axioms introduced

✅ **Quality Criteria**:
- [ ] Proofs are well-commented
- [ ] Helper lemmas are reusable
- [ ] Error bounds are explicit and tight
- [ ] Code follows project style guide

---

## Resources & References

### Key Files:
- `Steps2.lean`: Main implementation
- `ReductionLogic.lean`: Logic completeness proofs
- `Basic.lean`: Relation definitions
- `Spec.lean`: Protocol specification

### Key Definitions:
- `rbrKnowledgeSoundness`: RoundByRound.lean:363
- `KnowledgeStateFunction`: RoundByRound.lean:130
- `masterKStateProp`: Basic.lean:1554
- `foldStepRelOut`: Basic.lean:1653

### Mathlib Resources:
- `Data.Polynomial.Eval`: Polynomial evaluation
- `Probability.ProbabilityMassFunction`: Probability theory
- `FieldTheory.Finite.Basic`: Finite field properties

---

## Next Steps

1. **Immediate**: Start with Task 1.1 (Round polynomial evaluation)
2. **This Week**: Complete Phase 1 (Foundation Lemmas)
3. **Next Week**: Begin Phase 2 (KState Property Proofs)
4. **Month Goal**: Complete entire RBR KS proof

**Current Blocker**: None - ready to start Task 1.1

**Point of Contact**: Review progress after completing Phase 1
