# Binary Basefold: Complete RBR KS Attack Plan

## ANSWER: **YES** - All properties CAN be proved

All 4 steps (Fold, Commit, Relay, Final) have provable KState properties and rbrKnowledgeSoundness theorems.

---

## Status Summary

### Total Proof Obligations: **13 items**

| Step | toFun_empty | toFun_next | toFun_full | rbrKS | Total |
|------|-------------|------------|------------|-------|-------|
| **Fold** | ✅ Done | ❌ TODO | ❌ TODO | ❌ TODO | 3 |
| **Commit** | ❌ TODO | ❌ TODO | ❌ TODO | ❌ TODO | 4 |
| **Relay** | ❌ TODO | ✅ Done | ❌ TODO | ✅ Done | 2 |
| **Final** | ❌ TODO | ❌ TODO | ❌ TODO | ❌ TODO | 4 |

**Remaining**: 11 proof obligations

---

## Attack Order (Priority-Based)

### Phase 1: Foundation [CRITICAL - Week 1]

#### 1.1 Helper Lemma: Round Polynomial Evaluation
**Priority**: CRITICAL  
**Effort**: 3-4 hours  
**Blocks**: Fold.toFun_next

```lean
lemma getSumcheckRoundPoly_eval_sum :
  sumcheckConsistencyProp s H →
  let h := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H)
  h.val.eval (𝓑 0) + h.val.eval (𝓑 1) = s
```

#### 1.2 Helper Lemma: Oracle Preservation
**Priority**: CRITICAL  
**Effort**: 2-3 hours  
**Blocks**: Fold.toFun_full, Commit steps

```lean
lemma foldStep_oracle_agreement :
  -- Oracle statements preserved through fold embedding
  verifierOStmtOut = oStmtIn (via Sum.inl)
```

#### 1.3 Helper Lemma: Schwartz-Zippel
**Priority**: CRITICAL  
**Effort**: 4-6 hours  
**Blocks**: All rbrKS theorems

```lean
lemma schwartz_zippel_degree_one :
  [Field L] → p ≠ q → deg p ≤ 1 → deg q ≤ 1 →
  Pr[p.eval r = q.eval r | r ← uniform L] ≤ 1/|L|
```

---

### Phase 2: Fold Step [HIGH - Week 2]

#### 2.1 Fold.toFun_next (Lines 499-530)
**Priority**: HIGH  
**Effort**: 2-3 hours  
**Dependencies**: Item 1.1

**Strategy**:
- Round 1 has: `h_i = h_star ∧ h_i(0) + h_i(1) = s`
- Round 0 needs: `sumcheckConsistencyProp(s, H)`
- Apply Item 1.1 to derive consistency

**Code Location**: Steps2.lean:499-530

---

#### 2.2 Fold.toFun_full (Lines 531-565)
**Priority**: HIGH  
**Effort**: 3-4 hours  
**Dependencies**: Item 1.2

**Two Sub-items**:
- **2.2a** Oracle agreement (line 546-551 sorry)
- **2.2b** KState at round 2 (line 552-565 sorry)

**Strategy**:
- Use Item 1.2 for oracle preservation
- Extract witness satisfies round 2 checks from relOut

**Code Location**: Steps2.lean:531-565

---

#### 2.3 Fold.rbrKnowledgeSoundness (Lines 568-605)
**Priority**: HIGH  
**Effort**: 6-8 hours  
**Dependencies**: Items 1.3, 2.1, 2.2

**Strategy**:
- Doom escape: false@0 → true@2 after random challenge
- Apply Schwartz-Zippel (Item 1.3)
- Error = 1/|L| + bad_event_prob

**Code Location**: Steps2.lean:568-605

---

### Phase 3: Commit Step [MEDIUM - Week 2-3]

#### 3.1 Commit.toFun_empty (Line 913)
**Priority**: MEDIUM  
**Effort**: 2-3 hours  
**Dependencies**: Understanding of commitKStateProp

**Strategy**:
- Match relIn = foldStepRelOut to commitKStateProp at round 0
- Both use masterKStateProp with localChecks = True
- Should be straightforward unfolding

**Code Location**: Steps2.lean:913

---

#### 3.2 Commit.toFun_next (Lines 914-917)
**Priority**: MEDIUM  
**Effort**: 2-3 hours  
**Dependencies**: Item 3.1

**Strategy**:
- Only 1 P_to_V message (m = 0)
- Round 1 adds oracle, round 0 doesn't have it yet
- Show adding oracle preserves masterKStateProp

**Code Location**: Steps2.lean:914-917

---

#### 3.3 Commit.toFun_full (Lines 918-919)
**Priority**: MEDIUM  
**Effort**: 3-4 hours  
**Dependencies**: Items 3.1, 3.2

**Strategy**:
- relOut = roundRelation(i.succ)
- Verifier just returns input (no checks)
- Show extracted witness satisfies round 1 KState

**Code Location**: Steps2.lean:918-919

---

#### 3.4 Commit.rbrKnowledgeSoundness (Lines 922-935)
**Priority**: MEDIUM  
**Effort**: 2-3 hours  
**Dependencies**: Items 3.1-3.3

**Strategy**:
- No challenges (pSpecCommit has 0 challenges)
- Error = 0 (no doom escape possible)
- Vacuous proof via `Fin.elim0`

**Code Location**: Steps2.lean:922-935

---

### Phase 4: Relay Step [LOW - Week 3]

#### 4.1 Relay.toFun_empty (Lines 1124-1131)
**Priority**: LOW  
**Effort**: 2-3 hours  
**Dependencies**: Understanding oracle mapping

**Strategy**:
- Already has helper: `oracleWitnessConsistency_relay_preserved`
- Show mapping preserves masterKStateProp
- Oracle indices adjust but consistency maintained

**Code Location**: Steps2.lean:1124-1131

---

#### 4.2 Relay.toFun_full (Lines 1133-1136)
**Priority**: LOW  
**Effort**: 1-2 hours  
**Dependencies**: Item 4.1

**Strategy**:
- Verifier returns input unchanged
- relOut preserves structure
- Almost definitional equality

**Code Location**: Steps2.lean:1133-1136

**Note**: Relay.toFun_next and Relay.rbrKnowledgeSoundness are ✅ DONE (vacuous via Fin.elim0)

---

### Phase 5: Final Sumcheck Step [MEDIUM-HIGH - Week 3-4]

#### 5.1 Final.toFun_empty (Line 1532)
**Priority**: MEDIUM  
**Effort**: 2-3 hours  
**Dependencies**: Understanding finalSumcheckKStateProp

**Strategy**:
- relIn = roundRelation(Fin.last ℓ)
- Round 0: masterKStateProp with localChecks = True
- Match structures

**Code Location**: Steps2.lean:1532

---

#### 5.2 Final.toFun_next (Lines 1533-1536)
**Priority**: MEDIUM  
**Effort**: 3-4 hours  
**Dependencies**: Item 5.1

**Strategy**:
- Only 1 P_to_V message (m = 0)
- Round 1: additional check for final constant c
- Show c = f^(ℓ)(0) implies consistency

**Code Location**: Steps2.lean:1533-1536

---

#### 5.3 Final.toFun_full (Lines 1537-1538)
**Priority**: HIGH  
**Effort**: 4-5 hours  
**Dependencies**: Items 5.1, 5.2

**Strategy**:
- relOut = finalSumcheckRelOut
- Includes finalFoldingStateProp check
- Show extracted witness satisfies all constraints

**Code Location**: Steps2.lean:1537-1538

---

#### 5.4 Final.rbrKnowledgeSoundness (Lines 1541-1553)
**Priority**: HIGH  
**Effort**: 5-6 hours  
**Dependencies**: Items 5.1-5.3

**Strategy**:
- No challenges in final step
- Error = 0 (deterministic verification)
- OR: If c is treated as "challenge", apply similar Schwartz-Zippel

**Code Location**: Steps2.lean:1541-1553

---

## Recommended Attack Order

### Week 1: Foundation + Fold Basics
1. ✅ Item 1.1: Round poly eval lemma (3-4h)
2. ✅ Item 1.2: Oracle preservation (2-3h)
3. ✅ Item 2.1: Fold.toFun_next (2-3h)
4. ✅ Item 2.2: Fold.toFun_full (3-4h)
5. ⏳ Item 1.3: Schwartz-Zippel START (2-3h this week)

**Milestone**: Fold KState properties complete

---

### Week 2: Fold RBR KS + Commit
1. ✅ Item 1.3: Schwartz-Zippel COMPLETE (2-3h)
2. ✅ Item 2.3: Fold.rbrKnowledgeSoundness (6-8h)
3. ✅ Item 3.1: Commit.toFun_empty (2-3h)
4. ✅ Item 3.2: Commit.toFun_next (2-3h)
5. ⏳ Item 3.3: Commit.toFun_full START (1-2h)

**Milestone**: Fold step complete, Commit 75% done

---

### Week 3: Commit + Relay + Final Basics
1. ✅ Item 3.3: Commit.toFun_full COMPLETE (2h)
2. ✅ Item 3.4: Commit.rbrKnowledgeSoundness (2-3h)
3. ✅ Item 4.1: Relay.toFun_empty (2-3h)
4. ✅ Item 4.2: Relay.toFun_full (1-2h)
5. ✅ Item 5.1: Final.toFun_empty (2-3h)
6. ⏳ Item 5.2: Final.toFun_next START (2h)

**Milestone**: Commit + Relay complete, Final 25% done

---

### Week 4: Final Step Completion
1. ✅ Item 5.2: Final.toFun_next COMPLETE (1-2h)
2. ✅ Item 5.3: Final.toFun_full (4-5h)
3. ✅ Item 5.4: Final.rbrKnowledgeSoundness (5-6h)
4. 🧪 Integration testing (4-6h)
5. 📝 Documentation (2-3h)

**Milestone**: ALL STEPS COMPLETE 🎉

---

## Detailed Item List (Attack Sheet)

### Critical Path Items (Must do first)
- [ ] **1.1** Round poly eval lemma [3-4h]
- [ ] **1.2** Oracle preservation [2-3h]
- [ ] **1.3** Schwartz-Zippel [4-6h]

### Fold Step Items
- [x] **Fold.toFun_empty** [DONE - line 498]
- [ ] **2.1** Fold.toFun_next [2-3h] ← depends on 1.1
- [ ] **2.2** Fold.toFun_full [3-4h] ← depends on 1.2
- [ ] **2.3** Fold.rbrKnowledgeSoundness [6-8h] ← depends on 1.3, 2.1, 2.2

### Commit Step Items
- [ ] **3.1** Commit.toFun_empty [2-3h]
- [ ] **3.2** Commit.toFun_next [2-3h] ← depends on 3.1
- [ ] **3.3** Commit.toFun_full [3-4h] ← depends on 3.1, 3.2
- [ ] **3.4** Commit.rbrKnowledgeSoundness [2-3h] ← depends on 3.1-3.3

### Relay Step Items
- [ ] **4.1** Relay.toFun_empty [2-3h]
- [x] **Relay.toFun_next** [DONE - line 1132 - Fin.elim0]
- [ ] **4.2** Relay.toFun_full [1-2h] ← depends on 4.1
- [x] **Relay.rbrKnowledgeSoundness** [DONE - line 1155 - Fin.elim0]

### Final Step Items
- [ ] **5.1** Final.toFun_empty [2-3h]
- [ ] **5.2** Final.toFun_next [3-4h] ← depends on 5.1
- [ ] **5.3** Final.toFun_full [4-5h] ← depends on 5.1, 5.2
- [ ] **5.4** Final.rbrKnowledgeSoundness [5-6h] ← depends on 5.1-5.3

---

## Dependency Graph

```
         1.1 (Round Poly)
              ↓
           2.1 (Fold.toFun_next)
              ↓
    1.2 (Oracle) → 2.2 (Fold.toFun_full)
              ↓           ↓
    1.3 (SZ) → 2.3 (Fold.rbrKS)
                    ↓
              [Fold Complete]
                    ↓
    3.1 (Commit.empty) → 3.2 (Commit.next) → 3.3 (Commit.full) → 3.4 (Commit.rbrKS)
                                                                      ↓
                                                              [Commit Complete]
                                                                      ↓
    4.1 (Relay.empty) → 4.2 (Relay.full)
              ↓
        [Relay Complete]
              ↓
    5.1 (Final.empty) → 5.2 (Final.next) → 5.3 (Final.full) → 5.4 (Final.rbrKS)
                                                                      ↓
                                                              [ALL COMPLETE] 🎉
```

---

## Difficulty Ratings

| Item | Difficulty | Reason |
|------|-----------|---------|
| 1.1 | ⭐⭐⭐ | Polynomial evaluation properties |
| 1.2 | ⭐⭐ | Oracle embedding mechanics |
| 1.3 | ⭐⭐⭐⭐ | Probability theory + Schwartz-Zippel |
| 2.1 | ⭐⭐ | Uses 1.1 directly |
| 2.2 | ⭐⭐⭐ | Oracle agreement + witness extraction |
| 2.3 | ⭐⭐⭐⭐⭐ | Full RBR KS with Schwartz-Zippel |
| 3.1 | ⭐⭐ | Structural matching |
| 3.2 | ⭐⭐ | Oracle addition preservation |
| 3.3 | ⭐⭐ | Simple verifier logic |
| 3.4 | ⭐ | Vacuous (no challenges) |
| 4.1 | ⭐⭐ | Oracle mapping |
| 4.2 | ⭐ | Almost definitional |
| 5.1 | ⭐⭐ | Structural matching |
| 5.2 | ⭐⭐⭐ | Final constant properties |
| 5.3 | ⭐⭐⭐⭐ | Final folding state |
| 5.4 | ⭐⭐⭐⭐ | Final RBR KS (possibly vacuous) |

---

## Risk Assessment

### High Risk (Need Mitigation)
1. **Item 1.3 (Schwartz-Zippel)**: May need mathlib updates
   - **Mitigation**: Check mathlib early, adapt existing proofs
   
2. **Item 2.3 (Fold.rbrKS)**: Complex probability reasoning
   - **Mitigation**: Study existing RBR KS proofs in codebase

3. **Item 5.3/5.4 (Final step)**: Final folding consistency subtle
   - **Mitigation**: Understand `finalFoldingStateProp` deeply first

### Medium Risk
- Oracle agreement lemmas (Items 1.2, 2.2a)
- Bad event probability analysis (Item 2.3)
- Extractor correctness (Items 2.2, 5.3)

### Low Risk
- Structural matching items (3.1, 4.1, 5.1)
- Vacuous proofs (3.4, relay items)
- Definition unfolding (most toFun_empty items)

---

## Success Criteria

### Per-Step Completion
- ✅ **Fold**: All 3 items done
- ✅ **Commit**: All 4 items done
- ✅ **Relay**: All 2 items done (2 already trivial)
- ✅ **Final**: All 4 items done

### Global Completion
- [ ] All 13 sorries removed
- [ ] All theorems compile
- [ ] No new axioms introduced
- [ ] Test cases pass
- [ ] Documentation complete

---

## Estimated Total Effort

| Phase | Items | Hours | Days (6h/day) |
|-------|-------|-------|---------------|
| Foundation | 1.1-1.3 | 9-13 | 1.5-2 |
| Fold | 2.1-2.3 | 11-15 | 2-2.5 |
| Commit | 3.1-3.4 | 9-12 | 1.5-2 |
| Relay | 4.1-4.2 | 3-5 | 0.5-1 |
| Final | 5.1-5.4 | 14-18 | 2.5-3 |
| Testing | - | 6-9 | 1-1.5 |
| **TOTAL** | **13 items** | **52-72h** | **9-12 days** |

**Realistic Timeline**: 2-3 weeks with focused effort

---

## Next Immediate Actions

1. **TODAY**: Start Item 1.1 (Round poly eval lemma)
2. **Tomorrow**: Complete 1.1, start Item 1.2
3. **Day 3**: Complete 1.2, start Item 1.3
4. **Day 4-5**: Complete Item 1.3
5. **Day 6**: Start Fold step (Items 2.1-2.2)

**Current Status**: Ready to begin - no blockers

---

## File Locations Quick Reference

- **Steps2.lean**: Main file with all 13 items
- **ReductionLogic.lean**: Logic completeness proofs (helper lemmas)
- **Basic.lean**: Relation definitions (masterKStateProp, roundRelation, etc.)
- **RoundByRound.lean**: RBR KS definitions and framework

---

## Conclusion

**YES** - All 13 proof obligations across all 4 steps are provable. The structure is sound, dependencies are clear, and the proof strategy is well-defined. With focused effort following this attack plan, completion is achievable in 2-3 weeks.
