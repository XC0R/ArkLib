# Lemmas Added to Steps2.lean

## Summary

Added **4 helper lemmas** (statements only, proofs to be filled) for the Fold step KState proofs.
These lemmas **reuse existing infrastructure** from the codebase instead of duplicating work.

---

## Location

File: `ArkLib/ProofSystem/Binius/BinaryBasefold/Steps2.lean`  
Lines: ~53-97 (section FoldStep, before foldOracleProver definition)

---

## Lemmas Added

### 1. `roundPoly_eval_sum_of_consistent_witness`
**Purpose**: Connects witness consistency to round polynomial evaluation  
**Reuses**: `getSumcheckRoundPoly_sum_eq` from `Prelude.lean:298`

```lean
lemma roundPoly_eval_sum_of_consistent_witness
    {i : Fin ℓ}
    (stmt : Statement (L := L) Context i.castSucc)
    (wit : Witness (L := L) 𝔽q β i.castSucc)
    (h_consistent : sumcheckConsistencyProp stmt.sumcheck_target wit.H) :
    let h_star := getSumcheckRoundPoly ℓ 𝓑 i wit.H
    h_star.val.eval (𝓑 0) + h_star.val.eval (𝓑 1) = stmt.sumcheck_target
```

**Usage**: Enables `toFun_next` proof (Fold.2.1 in attack plan)

---

### 2. `foldStep_oracle_unchanged`
**Purpose**: Shows fold step preserves oracle statements (no new oracles added)  
**Reuses**: `OracleVerifier.mkVerifierOStmtOut` pattern from `ReductionLogic.lean:355-379`

```lean
lemma foldStep_oracle_unchanged
    (i : Fin ℓ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (transcript : FullTranscript (pSpecFold (L := L))) :
    OracleVerifier.mkVerifierOStmtOut
      (foldStepLogic ...).embed
      (foldStepLogic ...).hEq
      oStmtIn transcript = oStmtIn
```

**Usage**: Enables `toFun_full` proof - oracle agreement part (Fold.2.2a in attack plan)  
**Pattern**: Similar to `snoc_oracle_eq_mkVerifierOStmtOut_commitStep` in `ReductionLogic.lean:557-595`

---

### 3. `foldStep_extracted_witness_consistent`
**Purpose**: Shows extracted witness satisfies polynomial consistency at round 2  
**Reuses**: Structure from `strictFoldStepRelOut` definition

```lean
lemma foldStep_extracted_witness_consistent
    (i : Fin ℓ)
    (stmtIn witOut transcript ...)
    (h_relOut : ((stmtOut, oStmtIn), witOut) ∈ strictFoldStepRelOut ...) :
    let h_i := transcript.messages ⟨0, rfl⟩
    let r_i' := transcript.challenges ⟨1, rfl⟩
    let h_star := getSumcheckRoundPoly ℓ 𝓑 i (projectToMidSumcheckPoly ...)
    h_i = h_star ∧ h_i.val.eval r_i' = h_star.val.eval r_i'
```

**Usage**: Enables `toFun_full` proof - witness consistency part (Fold.2.2b in attack plan)

---

### 4. `prob_poly_agreement_degree_one`
**Purpose**: Schwartz-Zippel for degree-1 univariate polynomials  
**Reuses**: `prob_schwartz_zippel_mv_polynomial` from `ArkLib/Data/Probability/Instances.lean:460`

```lean
lemma prob_poly_agreement_degree_one
    [Fintype L]
    (p q : L⦃≤ 1⦄[X])
    (h_ne : p ≠ q) :
    Pr_{ let r ←$ᵖ L }[ p.val.eval r = q.val.eval r ] ≤
      (1 : ℝ≥0) / (Fintype.card L : ℝ≥0)
```

**Usage**: Enables `rbrKnowledgeSoundness` proof (Fold.2.3 in attack plan)  
**Note**: This is a specialization of the existing multivariate Schwartz-Zippel to univariate case

---

## Updated Code Sections

### Modified: `toFun_next` (Lines ~527-552)
- Added structured proof outline
- Referenced Lemma 1 for sumcheck consistency derivation
- Preserved core (badEventExists ∨ oracleWitnessConsistency)
- **Status**: Ready for proof, just needs Lemma 1 applied

### Modified: `toFun_full` (Lines ~553-580)
- Added structured proof outline with clear goals
- Referenced Lemmas 2a and 2b for oracle and witness consistency
- Split into 3 sub-goals: oracle agreement, local checks, core preservation
- **Status**: Ready for proof after Lemmas 2a/2b completed

### Modified: `rbrKnowledgeSoundness` (Lines ~625-648)
- Added detailed proof strategy comments
- Referenced Lemma 3 (Schwartz-Zippel)
- Outlined doom escape probability argument
- **Status**: Ready for proof after Lemmas 1-3 completed

---

## Existing Infrastructure Leveraged

### From `Prelude.lean`:
- ✅ `getSumcheckRoundPoly` (line 231)
- ✅ `getSumcheckRoundPoly_eval_eq` (line 259)
- ✅ `getSumcheckRoundPoly_sum_eq` (line 298) - **KEY LEMMA**

### From `Basic.lean`:
- ✅ `sumcheckConsistencyProp` (line 1279)
- ✅ `strictFoldStepRelOut` (line 1873)
- ✅ `masterKStateProp` (line 1554)

### From `ReductionLogic.lean`:
- ✅ `OracleVerifier.mkVerifierOStmtOut` usage patterns (lines 116, 355, 540, etc.)
- ✅ `snoc_oracle_eq_mkVerifierOStmtOut_commitStep` pattern (lines 557-595)
- ✅ `foldStep_is_logic_complete` structure (lines 325-415)

### From `ArkLib/Data/Probability/Instances.lean`:
- ✅ `prob_schwartz_zippel_mv_polynomial` (line 460)
- ✅ `prob_uniform_eq_card_filter_div_card` (line 83)
- ✅ `Pr_le_Pr_of_implies` (line 353)
- ✅ `Pr_add_split_by_complement` (line 396)

---

## Next Steps

### Immediate (Week 1):
1. **Lemma 1**: `roundPoly_eval_sum_of_consistent_witness`
   - Use `getSumcheckRoundPoly_sum_eq` from Prelude.lean
   - Connect to `sumcheckConsistencyProp` definition
   - **Estimated**: 3-4 hours

2. **Lemma 2a**: `foldStep_oracle_unchanged`
   - Follow pattern from `foldStep_is_logic_complete` (ReductionLogic.lean:355-379)
   - Show all embeddings are Sum.inl (no Sum.inr messages)
   - **Estimated**: 2-3 hours

3. **Lemma 3**: `prob_poly_agreement_degree_one`
   - Specialize `prob_schwartz_zippel_mv_polynomial` to univariate case
   - May be straightforward if we can convert between univariate and n=1 multivariate
   - **Estimated**: 4-6 hours

### After Foundation Lemmas (Week 2):
4. **Lemma 2b**: `foldStep_extracted_witness_consistent`
   - Extract from `strictFoldStepRelOut` structure
   - Connect transcript to polynomial evaluations
   - **Estimated**: 3-4 hours

5. **Complete toFun_next**: Apply Lemma 1
   - **Estimated**: 1-2 hours

6. **Complete toFun_full**: Apply Lemmas 2a, 2b
   - **Estimated**: 2-3 hours

7. **Complete rbrKnowledgeSoundness**: Apply Lemma 3
   - Formalize doom escape argument
   - Add bad event probability
   - **Estimated**: 6-8 hours

---

## Benefits of This Approach

1. **No Duplication**: Reuses 10+ existing definitions and lemmas
2. **Type Safety**: Lemmas type-check with existing infrastructure
3. **Clarity**: Clear separation between helper lemmas and main proofs
4. **Maintainability**: Changes to base definitions automatically propagate
5. **Reviewability**: Small, focused lemmas easier to review and prove

---

## Files Modified

- ✅ `Steps2.lean`: Added 4 lemma statements + updated 3 proof outlines

## Files NOT Modified (Existing Infrastructure)

- `Prelude.lean`: Used as-is
- `Basic.lean`: Used as-is
- `ReductionLogic.lean`: Used as-is
- `ArkLib/Data/Probability/Instances.lean`: Used as-is

---

## Testing Plan

After completing each lemma:
1. Verify it type-checks with existing infrastructure
2. Test on small examples (e.g., ℓ=1, small field)
3. Use in main proofs to ensure it provides needed properties
4. Check no circular dependencies introduced

---

## Status: Ready to Begin

All lemma statements compile. No blockers. Can start with Lemma 1 immediately.
