# Fold Step Implementation Progress

## ✅ COMPLETED (January 27, 2026)

### 1. Helper Lemmas

#### Lemma 1.1: roundPoly_eval_sum_of_consistent_witness
- **Status**: ✅ COMPLETE
- **Location**: Steps2.lean:62-74
- **Strategy**: Direct application of `getSumcheckRoundPoly_sum_eq`
- **Proof**: Connects sumcheckConsistencyProp to round polynomial evaluation

#### Lemma 1.2a: foldStep_oracle_unchanged
- **Status**: ✅ COMPLETE
- **Location**: Steps2.lean:76-107
- **Strategy**: Prove oracle statements unchanged via Sum.inl embedding
- **Proof**: Uses `mkVerifierOStmtOut_inl` with funext

#### Lemma 1.3: prob_poly_agreement_degree_one
- **Status**: ✅ COMPLETE (moved to ArkLib/Data/Probability/Instances.lean)
- **Location**: Instances.lean:496-546
- **Strategy**: Convert to MvPolynomial (n=1) and apply `prob_schwartz_zippel_mv_polynomial`
- **Key Components**:
  1. ✅ Non-zero preservation via `toMvPolynomial_ne_zero_iff`
  2. ✅ Eval equivalence via `MvPolynomial.eval_toMvPolynomial`
  3. ✅ Probability bijection via `prob_uniform_singleton_finFun_eq`
  4. ✅ Degree preservation via `toMvPolynomial_totalDegree_le` (added to ToMathlib/MvPolynomial/Equiv.lean)
- **Result**: Fully proven, no sorry placeholders!

### 2. KState Properties

#### Item 2.1: Fold.toFun_next
- **Status**: ✅ COMPLETE  
- **Location**: Steps2.lean:604-610
- **Proof**: 3-line proof using `simp_rw` and `getSumcheckRoundPoly_sum_eq`
- **Key Insight**: Substitution h_localized into h_explicit gives the exact form needed

---

## ⏸ DEFERRED / IN PROGRESS

### 3. Remaining Items

#### Lemma 1.2b: foldStep_extracted_witness_consistent
- **Status**: ⏸ DEFERRED (likely not needed)
- **Location**: Steps2.lean:109-121
- **Note**: May not be necessary for toFun_full proof

#### Item 2.2: Fold.toFun_full
- **Status**: ⏸ DEFERRED (by user request)
- **Location**: Steps2.lean:611-650
- **Reason**: Requires complex simulateQ & oracle simulation reasoning
- **User Note**: "I'll do later"
- **Current State**: Has structured outline with sorry placeholders

#### Item 2.3: Fold.rbrKnowledgeSoundness
- **Status**: ⏸ IN PROGRESS (structure outlined)
- **Location**: Steps2.lean:652-696
- **Dependencies**: Items 2.1 (✅), Lemma 1.3 (✅), Item 2.2 (deferred)
- **Current State**: Has detailed proof strategy comments, needs implementation
- **Challenge**: Complex case analysis of doom escape paths

---

## Summary

**Fully Completed**: 4/7 items (57%)
- ✅ Lemma 1.1 (roundPoly_eval_sum_of_consistent_witness)
- ✅ Lemma 1.2a (foldStep_oracle_unchanged)
- ✅ Lemma 1.3 (prob_poly_agreement_degree_one) - **FULLY PROVEN IN INSTANCES.LEAN**
- ✅ Item 2.1 (toFun_next)

**Deferred/In Progress**: 3/7 items (43%)
- ⏸ Lemma 1.2b (may skip)
- ⏸ Item 2.2 (toFun_full) - deferred by user
- ⏸ Item 2.3 (rbrKnowledgeSoundness) - strategy outlined, needs implementation

**Build Status**: ✅ Compiles cleanly

**Key Achievement**: Lemma 1.3 is now a **complete, proven theorem** with:
- Proper MvPolynomial conversion
- Supporting lemma `toMvPolynomial_totalDegree_le` added to ToMathlib
- No sorry placeholders
- Reuses existing Schwartz-Zippel infrastructure

**Next Priority**: Item 2.3 (rbrKnowledgeSoundness)
- Dependency on Item 2.2 (toFun_full) may block full completion
- Can outline proof structure and identify gaps
