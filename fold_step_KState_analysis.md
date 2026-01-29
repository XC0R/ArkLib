# Analysis: Fold Step KState & RBR Knowledge Soundness

## Summary

The fold step in Binary Basefold has a well-defined `KState`, `relIn`, and `relOut` structure. However, **three critical properties remain unproved** (marked with `sorry`), which are essential for establishing RBR knowledge soundness.

## 1. Definitions Overview

### 1.1 Input Relation (`relIn`)
```lean
relIn := roundRelation 𝔽q β (ϑ := ϑ) i.castSucc
```

The `roundRelation` requires:
- **Local checks**: `sumcheckConsistencyProp` - the witness polynomial H must satisfy sumcheck properties
- **Master state**: `masterKStateProp` which combines:
  - `oracleWitnessConsistency`: Witness oracles are compliant with folding
  - `badEventExists`: Bad folding events may exist (tracked for soundness)
  - Formula: `badEventExists ∨ oracleWitnessConsistency`

### 1.2 Output Relation (`relOut`)
```lean
relOut := foldStepRelOut 𝔽q β (ϑ := ϑ) i
```

The `foldStepRelOut` is similar to `roundRelation` but:
- Statement index advances: `i.castSucc → i.succ`
- Oracle index remains: `i.castSucc` (no commitment yet)
- Uses `masterKStateProp` with `OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc`

### 1.3 Knowledge State (`foldKStateProp`)

The KState has **3 rounds** (m ∈ {0, 1, 2}):

#### **Round 0** (Before prover message):
```lean
masterKStateProp with localChecks := sumcheckConsistencyProp
```
- Equivalent to `relIn`
- Witness must satisfy sumcheck consistency
- Oracle/bad-event disjunction holds

#### **Round 1** (After P sends h_i(X)):
```lean
masterKStateProp with localChecks := 
  explicitVCheck ∧ localizedRoundPolyCheck
```
where:
- `explicitVCheck`: `h_i(0) + h_i(1) = stmt.sumcheck_target`
- `localizedRoundPolyCheck`: `h_i = h_star` (h_star is the honest polynomial from witness)

#### **Round 2** (After V sends challenge r_i'):
```lean
masterKStateProp with localChecks := 
  localizedRoundPolyCheck ∧ nextSumcheckTargetCheck
```
where:
- `localizedRoundPolyCheck`: `h_i = h_star`
- `nextSumcheckTargetCheck`: `h_i.eval r_i' = h_star.eval r_i'`

---

## 2. Required Properties for RBR Knowledge Soundness

The `KnowledgeStateFunction` structure requires **three properties**:

### 2.1 ✅ `toFun_empty` (Implemented)
```lean
toFun_empty : ∀ stmtIn witMid,
  ⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn ↔ toFun 0 stmtIn default witMid
```

**Status**: ✅ This is satisfied by construction
- Both `relIn` and `toFun 0` use identical `masterKStateProp` definitions
- Proven via `rfl`

### 2.2 ❌ `toFun_next` (UNPROVED - Line 499-530)
```lean
toFun_next : ∀ m, pSpec.dir m = .P_to_V →
  ∀ stmtIn tr msg witMid, toFun m.succ stmtIn (tr.concat msg) witMid →
    toFun m.castSucc stmtIn tr (extractor.extractMid m stmtIn (tr.concat msg) witMid)
```

**What needs proving**: 
If the knowledge state holds at round 1 (after P's message), then it must also hold at round 0.

**Proof Strategy** (from code comments):
1. At round 1, we have: `explicitVCheck ∧ localizedRoundPolyCheck`
2. At round 0, we need: `sumcheckConsistencyProp`
3. **Key Lemma**: If `h_i = h_star` (localizedRoundPolyCheck) and `h_i(0) + h_i(1) = s` (explicitVCheck), then `sumcheckConsistencyProp` holds for `h_star`
4. This is a logical soundness lemma connecting polynomial consistency to sumcheck consistency

**Difficulty**: Medium
- Requires proving that the round polynomial h_i computed from a consistent H satisfies sumcheck properties
- Should follow from the relationship between `getSumcheckRoundPoly` and `sumcheckConsistencyProp`

### 2.3 ❌ `toFun_full` (UNPROVED - Line 531-565)
```lean
toFun_full : ∀ stmtIn tr witOut,
  [fun stmtOut => (stmtOut, witOut) ∈ relOut | ...] > 0 →
  toFun (.last n) stmtIn tr (extractor.extractOut stmtIn tr witOut)
```

**What needs proving**:
If the verifier can output a statement in `relOut` with probability > 0, then the knowledge state holds at round 2.

**Proof Strategy** (from code comments):
1. `relOut` requires `masterKStateProp` at `i.succ` with sumcheck consistency
2. Need to show: if verifier outputs `(stmtOut, oStmtOut)` with `witOut ∈ relOut`, then `foldKStateProp` holds at round 2
3. **Key Lemmas**:
   - Oracle statements match: `oStmtLast = oStmtOut` (line 546-551, marked sorry)
   - The verifier's check implies the local checks (polynomial consistency)
   - The extracted witness `witLast` satisfies constraints

**Difficulty**: Medium-Hard
- Requires proving oracle statement agreement between prover/verifier
- Need to connect verifier's guard condition to knowledge state properties
- Uses the fact that `foldStepRelOut` implies the necessary consistency

---

## 3. The Main RBR KS Theorem (Line 568-605)

### 3.1 ❌ Main Theorem (UNPROVED)
```lean
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
  (foldOracleVerifier ...).rbrKnowledgeSoundness ... (foldKnowledgeError i)
```

**What needs proving**:
The "doom escape" probability is bounded by `foldKnowledgeError i`.

**Error Analysis**:
```lean
foldKnowledgeError i = err_SC + err_BE
where:
  err_SC = 1/|L|  (Schwartz-Zippel)
  err_BE = if ϑ | (i+1) then ϑ * |S^(i+1)| / |L| else 0
```

**Proof Strategy** (from code comments, lines 589-604):

1. **Setup**: The doom escape event is:
   - KState is false at round 0 (before prover message)
   - KState becomes true at round 2 (after random challenge r_i')

2. **Case Analysis**:
   - If KState is false at round 0, then either:
     - (A) The extracted witness doesn't satisfy `relIn`, OR
     - (B) The prover's polynomial `h_i ≠ h_star` (the correct round polynomial)

3. **Schwartz-Zippel Application**:
   - After V's random challenge `r_i'`, KState can only be true at round 2 if:
     - `h_i(r_i') = h_star(r_i')` (nextSumcheckTargetCheck)
   - But if `h_i ≠ h_star`, this happens with probability ≤ `deg/|L|` where deg ≤ 2
   - For degree 1 polynomials: probability ≤ `1/|L|`

4. **Bad Event Analysis**:
   - At round i, if `ϑ | (i+1)` (commitment round), new bad events can occur
   - The bad event probability is `ϑ * |S^(i+1)| / |L|`
   - This comes from the LDT (List Decoding Test) analysis

5. **Total Error**: `err_SC + err_BE = 1/|L| + (if ϑ|(i+1) then ... else 0)`

**Difficulty**: Hard
- Requires formal Schwartz-Zippel lemma for polynomial agreement
- Need to formalize the relationship between false→true transitions and polynomial disagreement
- Must handle the commitment round bad events correctly

---

## 4. Can These Properties Be Proved?

### Short Answer: **YES**, all properties are provable

### Evidence:

1. **Structural Completeness**: The `foldStep_is_logic_complete` theorem (ReductionLogic.lean) provides strong completeness guarantees that should support these proofs.

2. **Similar Patterns**:
   - The `commitStep` and `relayStep` have similar KState structures
   - The proof patterns for perfect completeness (lines 178-380) provide templates

3. **Existing Infrastructure**:
   - `masterKStateProp` has well-defined semantics
   - Oracle consistency lemmas exist in the codebase
   - Sumcheck polynomial relationships are established

### Proof Dependencies:

#### For `toFun_next`:
- ✅ `getSumcheckRoundPoly` definition
- ✅ `sumcheckConsistencyProp` properties
- ❓ **Needed**: Lemma connecting round polynomial to sumcheck consistency

#### For `toFun_full`:
- ✅ `foldStepRelOut` definition
- ✅ Oracle embedding properties
- ❓ **Needed**: Oracle statement agreement lemma
- ❓ **Needed**: Verifier output implies extracted witness correctness

#### For main RBR KS theorem:
- ✅ Schwartz-Zippel infrastructure (exists in mathlib)
- ✅ Bad event definitions
- ❓ **Needed**: Formal connection between false→true transitions and polynomial disagreement
- ❓ **Needed**: Probability bound on bad events

---

## 5. Recommended Proof Strategy

### Phase 1: Helper Lemmas (Priority: HIGH)
1. **Lemma 1**: Round polynomial consistency
   ```lean
   lemma roundPoly_from_consistent_H : 
     sumcheckConsistencyProp s H →
     let h_i := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H)
     h_i.eval (𝓑 0) + h_i.eval (𝓑 1) = s
   ```

2. **Lemma 2**: Oracle statement preservation
   ```lean
   lemma foldStep_oracle_agreement :
     foldStepRelOut (...) →
     verifier outputs (stmtOut, oStmtOut) →
     oStmtOut = oStmtIn (via embedding)
   ```

3. **Lemma 3**: Extracted witness satisfies KState
   ```lean
   lemma extracted_witness_satisfies_KState :
     (stmtOut, witOut) ∈ foldStepRelOut →
     verifier check passes →
     foldKStateProp 2 stmt tr (extractOut ... witOut)
   ```

### Phase 2: Property Proofs (Priority: MEDIUM)
1. Prove `toFun_next` using Lemma 1
2. Prove `toFun_full` using Lemmas 2 & 3
3. Verify KState function is well-formed

### Phase 3: Main Theorem (Priority: HIGH)
1. Formalize Schwartz-Zippel for degree-1 polynomials over L
2. Prove doom-escape bound using polynomial disagreement argument
3. Add bad event analysis for commitment rounds
4. Complete the RBR KS theorem

---

## 6. Blockers & Missing Infrastructure

### Critical Missing Pieces:
1. **Polynomial Evaluation Lemmas**: Connection between `getSumcheckRoundPoly`, sumcheck consistency, and evaluation properties
2. **Oracle Agreement Infrastructure**: Formal proof that oracle statements are preserved through fold step
3. **Probability Theory**: Formalized Schwartz-Zippel with explicit degree bounds
4. **Bad Event Tracking**: Precise characterization of when bad events occur in commitment rounds

### Available Resources:
- ✅ Strong completeness for fold step logic
- ✅ Oracle embedding framework
- ✅ Transcript and protocol spec infrastructure
- ✅ Basic probability theory (ProbComp)

---

## 7. Conclusion

**Can all properties be proved?** ✅ **YES**

**Are they ready to prove now?** ⚠️ **PARTIALLY**
- `toFun_next`: Ready with 1-2 helper lemmas
- `toFun_full`: Needs oracle agreement lemma (moderate effort)
- Main RBR KS: Needs Schwartz-Zippel formalization (substantial effort)

**Estimated Effort**:
- Helper lemmas: 2-3 days
- Property proofs: 1-2 days
- Main theorem: 3-5 days
- **Total**: ~1-2 weeks for a focused effort

**Priority Actions**:
1. Prove the roundPoly consistency lemma (enables `toFun_next`)
2. Establish oracle agreement (enables `toFun_full`)
3. Formalize Schwartz-Zippel for this specific use case
4. Complete the main theorem with probability bounds

The structure is sound, the definitions are correct, and the proof obligations are clear. The remaining work is **technically feasible** and follows **established patterns** in the codebase.
