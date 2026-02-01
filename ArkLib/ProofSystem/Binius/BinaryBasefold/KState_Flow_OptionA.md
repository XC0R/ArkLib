# Binary Basefold: KState & Relation Flow Analysis (Option D - REJECTED)

This document analyzes Option D (simplified intermediate steps without oracle props)
and explains **why it doesn't work**.

---

## ⚠️ CRITICAL: Option D Has Fatal Flaws

**Option D proposed:** Remove oracle properties from intermediate steps, only add them at final sumcheck.

**Status: REJECTED** for two critical reasons:

### Flaw 1: Missing Proposition 4.22 Error Bound

The paper's total soundness error (from Spec.md lines 667-678):
```
Total Error ≤ (2·ℓ)/|L| + 2^{ℓ+𝓡}/|L| + ((1/2) + 1/(2·2^𝓡))^γ
              ─────────   ─────────────   ──────────────────────
              Sumcheck    Prop 4.22       Prop 4.23
                          (bad events)    (proximity gap)
```

**With Option D:**
- Sumcheck error: ✅ captured at fold steps
- Prop 4.22 error: ❌ **NOT CAPTURED** - no extraction failure when bad event occurs
- Prop 4.23 error: ✅ captured at Query Phase

**Why bad events aren't captured:**

When bad event occurs at fold step (V→P challenge `r_i`):
- KState(before) = TRUE (oracle was compliant)
- Bad event makes oracle non-compliant OR the global OR stays TRUE
- With global OR: KState(after) = TRUE (badEvent is true!)
- Extraction failure = `¬KState(before) ∧ KState(after)` = `¬TRUE ∧ TRUE` = FALSE
- **No extraction failure recorded!**

The bad event probability from Prop 4.22 is absorbed into the OR but never bounded.

### Flaw 2: Prop 4.23 Requires "No Bad Events" Assumption

From Spec.md line 625:
> **Proposition 4.23 (Assuming no bad events).** If any of A's oracles is not compliant...

And Lemma 4.24 Case 2 (line 634):
> **Assuming bad event E_{i*} didn't occur**

**The Problem:**
- Prop 4.23's analysis ASSUMES no bad events occurred
- If a bad event DID occur (far oracle's fold becomes close), the bound doesn't apply
- The oracle might now appear "compliant" and proximity tests pass
- This is exactly what Prop 4.22 bounds separately

### Flaw 3: Final Sumcheck toFun_next Breaks

At final sumcheck, the prover sends constant `c`. With Option D:
- KState(0) = `sumcheckConsistencyProp(H)` (no oracle props)
- KState(1) = `sumcheckFinalCheck` (c matches formula)
- toFun_next: KState(1) → KState(0)

**The Problem:**
- The constant `c` should equal `H(challenges)` where `H` is the multilinear polynomial
- But `c` is also the result of folding all oracles: `fold(f^{(ℓ-ϑ)}, ...) = c`
- Without oracle props, there's no connection between prover's `c` and correct `H`
- A cheating prover could send wrong `c` that satisfies the formula but not the actual polynomial
- **Cannot prove `sumcheckFinalCheck → sumcheckConsistencyProp`** without oracle information

---

## Original Design Rationale (For Reference)

### The Problem with Global OR at Intermediate Steps

The original design had `(badEvent ∨ oracleConsistencies)` at every step.
This causes **Case 4 Problem** at commit step `toFun_next`:

| Case | New Oracle State | badEvent | consistent | badEvent ∨ consist |
|------|-----------------|----------|------------|-------------------|
| 1 | Close, consistent folding | False | True | ✅ |
| 2 | Close, bad folding event | True | False | ✅ |
| 3 | Far, appears close after fold | True | False | ✅ |
| 4 | Far, stays far after fold | **False** | **False** | ❌ |

**Case 4:** An arbitrary oracle that is "far from code and stays far" has neither
a bad event nor consistency. The OR is FALSE.

### Why Option D Was Proposed

The idea was to defer `(badEvent ∨ oracleConsistencies)` to `finalSumcheckRelOut`,
avoiding Case 4 at commit steps.

### Why Global OR Works for Query Phase

Query Phase has protocol spec `[V→P]` (only V sends challenges, no P→V messages).
- `toFun_next` is not needed (no P→V messages)
- The RBR extraction failure is bounded by Proposition 4.23

This is exactly `queryRbrKnowledgeError`.

---

## Notation

- `simplifiedKStateProp(stmtIdx, stmt, wit, localChecks)` = `localChecks ∧ witnessStructuralInvariant wit`
- `finalSumcheckStepFoldingStateProp` = `oracleFoldingConsistency ∨ foldingBadEventExists` (global OR)
- `sumcheckConsistencyProp(s, H)` = `s = ∑ x ∈ (univ.map 𝓑)^ᶠ(ℓ - i), H.val.eval x`
- `witnessStructuralInvariant wit` = `wit.H = projectToMidSumcheckPoly wit.t ∧ wit.f = getMidCodewords wit.t`

---

## FOLD STEP (Round `i : Fin ℓ`)

**Protocol Spec:** `pSpecFold = [P→V: L⦃≤2⦄[X], V→P: L]` (size = 2)

### relIn: `roundRelation i.castSucc`
```
simplifiedKStateProp(
  stmtIdx    := i.castSucc,
  stmt       := stmt,
  wit        := wit,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

↓ **[toFun_empty]** ✅ (definitional equality via `rfl`)

### foldKStateProp m=0
```
simplifiedKStateProp(
  stmtIdx    := i.castSucc,
  stmt       := stmt,
  wit        := witMid,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target witMid.H
)
```

↓ **[toFun_next]** ✅ (P sends h_i(X))
- Proves: `explicitVCheck ∧ localizedRoundPolyCheck` ⟹ `sumcheckConsistencyProp`
- Key lemma: `getSumcheckRoundPoly_sum_eq`
- `witnessStructuralInvariant`: passes through (wit unchanged)

### foldKStateProp m=1
```
simplifiedKStateProp(
  stmtIdx    := i.castSucc,
  stmt       := stmt,
  wit        := witMid,
  localChecks := explicitVCheck ∧ localizedRoundPolyCheck
    where explicitVCheck   := h_i(0) + h_i(1) = stmt.sumcheck_target
          localizedRoundPolyCheck := h_i = h_star
)
```

↓ (V→P challenge r_i') No toFun_next needed

### foldKStateProp m=2 (= Fin.last 2)
```
simplifiedKStateProp(
  stmtIdx    := i.succ,                              -- ADVANCED
  stmt       := stmtOut,
  wit        := witOut,
  localChecks := sumcheckConsistencyProp stmtOut.sumcheck_target witOut.H
)
```

↓ **[toFun_full]** ✅ (V completes round)
- Uses: `h_relOut : foldStepRelOutProp`
- Computes: `witOut := getFoldProverFinalOutput(..., witMid, h_i, r_i')`
- `witnessStructuralInvariant witOut`: follows from `witnessStructuralInvariant witMid` + projection lemma

↓ **[RBR Knowledge Soundness theorem]** ✅
- Error bound: `foldKnowledgeError` (Schwartz-Zippel for sumcheck)

### relOut: `foldStepRelOut i`
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmt,
  wit        := wit,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

---

## COMMIT STEP (Round `i : Fin ℓ`, when `isCommitmentRound ℓ ϑ i`)

**Protocol Spec:** `pSpecCommit = [P→V: OracleFunction]` (size = 1)

### relIn: `foldStepRelOut i`
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmtIn,
  wit        := witIn,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witIn.H
)
```

↓ **[toFun_empty]** ✅ (definitional equality)

### commitKStateProp m=0
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmtIn,
  wit        := witMid,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witMid.H
)
```

↓ **[toFun_next]** ✅ TRIVIAL (P sends oracle)
- No oracle properties in KState!
- Just pass through `localChecks` and `witnessStructuralInvariant`

### commitKStateProp m=1 (= Fin.last 1)
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmtIn,
  wit        := witMid,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witMid.H
)
```

↓ **[toFun_full]** ✅ TRIVIAL (verifier completes)
- Uses: `h_relOut : roundRelationProp i.succ`
- Relation is identical to KState (no oracle properties to prove)

↓ **[RBR Knowledge Soundness theorem]** ✅
- Error bound: 0 (no challenges, deterministic)

### relOut: `roundRelation i.succ`
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmt,
  wit        := wit,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

---

## RELAY STEP (Round `i : Fin ℓ`, when `¬isCommitmentRound ℓ ϑ i`)

**Protocol Spec:** `pSpecRelay = []` (size = 0, no messages)

### relIn: `foldStepRelOut i`
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmtIn,
  wit        := witIn,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witIn.H
)
```

↓ **[toFun_empty]** ✅ (uses preservation lemmas, identical state)

### relayKStateProp (m=0 = Fin.last 0)
```
simplifiedKStateProp(
  stmtIdx    := i.succ,
  stmt       := stmtIn,
  wit        := witMid,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witMid.H
)
```

↓ **[toFun_full]** ✅ (no messages, so toFun_next not needed)
- Uses: `h_relOut : roundRelationProp i.succ`
- Trivial: same state

↓ **[RBR Knowledge Soundness theorem]** ✅
- Error bound: 0 (no messages at all)

### relOut: `roundRelation i.succ`
```
(same as commit step relOut)
```

---

## FINAL SUMCHECK STEP (at `i = Fin.last ℓ`)

**Protocol Spec:** `pSpecFinalSumcheckStep = [P→V: L]` (size = 1)

### relIn: `roundRelation (Fin.last ℓ)`
```
simplifiedKStateProp(
  stmtIdx    := Fin.last ℓ,
  stmt       := stmt,
  wit        := wit,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

↓ **[toFun_empty]** ✅ (definitional equality)

### finalSumcheckKStateProp m=0
```
simplifiedKStateProp(
  stmtIdx    := Fin.last ℓ,
  stmt       := stmt,
  wit        := witMid,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target witMid.H
)
```

↓ **[toFun_next]** ✅ (P sends final constant c)
- Proves: sumcheck final check
- `witnessStructuralInvariant`: passes through

### finalSumcheckKStateProp m=1 (= Fin.last 1)
```
sumcheckFinalCheck ∧ finalSumcheckStepFoldingStateProp
  where sumcheckFinalCheck := stmt.sumcheck_target = eqTilde(r) * c
        finalSumcheckStepFoldingStateProp := oracleFoldingConsistency ∨ foldingBadEventExists  -- GLOBAL OR HERE
```

↓ **[toFun_full]** ✅ (verifier completes)
- Uses: `h_relOut : finalSumcheckRelOutProp`
- Key: This is where the global OR gets introduced

↓ **[RBR Knowledge Soundness theorem]** ✅
- Error bound: 0 (verifier just computes, no randomness in final check)

### relOut: `finalSumcheckRelOut`
```
finalSumcheckRelOutProp = finalSumcheckStepFoldingStateProp (stmtOut, oStmt)
  where finalSumcheckStepFoldingStateProp := oracleFoldingConsistency ∨ foldingBadEventExists  -- GLOBAL OR
```

---

## QUERY PHASE (γ_repetitions proximity tests)

**Protocol Spec:** `pSpecQuery = [V→P: (Fin γ_repetitions → sDomain)]` (size = 1, V→P only)

**Key Design Choice:** Global OR is deliberate here for Proposition 4.23!

### relIn: `finalSumcheckRelOut`
```
finalSumcheckStepFoldingStateProp = oracleFoldingConsistency ∨ foldingBadEventExists
```

↓ **[toFun_empty]** ✅ (definitional equality)

### queryKStateProp m=0
```
finalSumcheckRelOutProp = oracleFoldingConsistency ∨ foldingBadEventExists
```

↓ (V→P challenges γ_challenges) No toFun_next needed (V→P message)

### queryKStateProp m=1 (= Fin.last 1)
```
proximityChecksSpec γ_challenges oStmt fold_challenges final_constant
  -- All γ_repetitions proximity tests pass
```

↓ **[toFun_full]** ✅
- Uses: `h_relOut : acceptRejectOracleRel` (trivially true = accept)
- Proves: if `finalSumcheckStepFoldingStateProp` holds, then proximity checks can pass

↓ **[RBR Knowledge Soundness theorem]** ✅ (Proposition 4.23)
- Extraction failure event: `¬ KState(0) ∧ KState(1)`
  = `¬ (oracleFoldingConsistency ∨ badEvent) ∧ proximityTestsPassed`
  = `¬ oracleFoldingConsistency ∧ ¬ badEvent ∧ proximityTestsPassed`
- This means: some oracle is NOT compliant, no bad events, but tests pass
- By Proposition 4.23: `Pr[tests pass | some oracle not compliant] ≤ ((1/2) + 1/(2·2^𝓡))^γ`
- Error bound: `queryRbrKnowledgeError = ((1/2) + 1/(2·2^𝓡))^γ_repetitions`

### relOut: `acceptRejectOracleRel`
```
acceptRejectOracleRel = ((true, isEmptyElim), ())  -- trivially accept
```

---

## Summary: Security Proof Requirements (Option D - WITH ISSUES)

| Step | Transition | Proof | Status | Notes |
|------|-----------|-------|--------|-------|
| Fold | relIn → KState 0 | toFun_empty | ✅ | definitional |
| Fold | KState 0 → KState 1 | toFun_next | ✅ | `getSumcheckRoundPoly_sum_eq` |
| Fold | KState 1 → KState 2 | (V→P) | N/A | no proof needed |
| Fold | KState 2 → relOut | toFun_full | ✅ | projection lemmas |
| Fold | RBR KS Error | - | ⚠️ | **Missing Prop 4.22 bad event error!** |
| Commit | relIn → KState 0 | toFun_empty | ✅ | definitional |
| Commit | KState 0 → KState 1 | toFun_next | ✅ | TRIVIAL (no oracle props) |
| Commit | KState 1 → relOut | toFun_full | ✅ | TRIVIAL (no oracle props) |
| Relay | relIn → KState 0 | toFun_empty | ✅ | preservation lemmas |
| Relay | KState 0 → relOut | toFun_full | ✅ | trivial |
| Final | relIn → KState 0 | toFun_empty | ✅ | definitional |
| Final | KState 0 → KState 1 | toFun_next | ❌ | **BROKEN: can't connect c ↔ H without oracle props** |
| Final | KState 1 → relOut | toFun_full | ⚠️ | introduces global OR (where from?) |
| Query | relIn → KState 0 | toFun_empty | ✅ | definitional |
| Query | KState 0 → KState 1 | (V→P) | N/A | no proof needed |
| Query | KState 1 → relOut | toFun_full | ✅ | proximity → accept |
| Query | RBR KS | Prop 4.23 | ⚠️ | **Only valid assuming no bad events!** |

---

## Key Design Decisions (Analysis)

### 1. Oracle Properties Only at Final Step (REJECTED)

**Option D proposed:**
```lean
-- Intermediate steps (fold, commit, relay):
simplifiedKStateProp = localChecks ∧ witnessStructInv
-- No (badEvent ∨ oracleConsist)

-- Only at final sumcheck:
finalSumcheckKStateProp m=1 = sumcheckFinalCheck ∧ (oracleConsist ∨ badEvent)
```

**Why this fails:**
1. Final sumcheck toFun_next can't prove `c` is consistent with `H`
2. Prop 4.22 bad event error is not captured anywhere
3. Prop 4.23 assumes no bad events, but we haven't bounded them

### 2. Global OR Structure for Query Phase

The `oracleFoldingConsistency ∨ foldingBadEventExists` structure is designed for Prop 4.23:

- If `oracleFoldingConsistency`: all oracles are compliant → honest case
- If `foldingBadEventExists`: some oracle caused bad event → **should be bounded by Prop 4.22**
- If neither (some oracle not compliant, no bad event): bounded by Prop 4.23

**Critical insight:** The paper's analysis bounds bad events SEPARATELY (Prop 4.22), 
then applies Prop 4.23 CONDITIONAL on no bad events. The RBR framework needs to capture both.

### 3. Extractor Design

The extractor produces witnesses where `witnessStructuralInvariant` holds by construction:
```lean
extractedWit = {
  t := witOut.t,
  H := projectToMidSumcheckPoly witOut.t ...,
  f := getMidCodewords witOut.t ...
}
```

### 4. Paper's Soundness Structure vs RBR

**Paper's approach:**
```
Pr[cheat success] ≤ Pr[sumcheck fails] + Pr[bad event] + Pr[accept | no bad event ∧ non-compliant]
                    ────────────────   ──────────────   ────────────────────────────────────────
                    Sumcheck error     Prop 4.22        Prop 4.23
```

**RBR approach:**
```
Pr[extraction fails] = ∑ over rounds i: Pr[¬KState(i) ∧ KState(i+1)]
```

The paper uses a **partition** over outcomes (bad event vs no bad event).
RBR uses **sequential** extraction failures at each round.

These don't align naturally for oracle commitment protocols where:
- Oracles are received at commit steps (no challenges)
- Bad events occur at fold steps (when challenges are applied)
- The OR structure "hides" bad events from extraction failure

---

## Comparison: Original vs Option D (UPDATED)

| Aspect | Original | Option D |
|--------|----------|----------|
| Commit toFun_next | ❌ BLOCKED (Case 4) | ✅ Trivial |
| Commit toFun_full | Issues (oracle projection) | ✅ Trivial |
| Fold toFun_full | Needs `witnessStructInv` in OR | ✅ Works |
| Final Sumcheck toFun_next | ✅ Works (has oracle props) | ❌ **BROKEN** (no connection c ↔ H) |
| Query Phase | ✅ Works | ⚠️ Missing Prop 4.22 error |
| Prop 4.22 Error | ⚠️ Unclear where captured | ❌ **NOT CAPTURED** |
| Prop 4.23 Validity | ✅ Applies (with bad event tracking) | ⚠️ Conditional on no bad events |

---

## The Fundamental Tension

We have two conflicting requirements:

1. **Commit step toFun_next needs oracle props to NOT be in KState**
   - Otherwise Case 4 problem blocks the proof
   
2. **Final sumcheck + security analysis needs oracle props IN KState**
   - Otherwise can't connect `c` to `H`
   - Otherwise Prop 4.22 error not captured

### Possible Resolutions

**Option E: Hybrid Oracle Tracking**

Track oracle properties ONLY for oracles that have been "verified" (had challenges applied):
- At commit step: new oracle is NOT verified yet, don't include in KState
- After fold step: oracle HAS been verified (challenges applied), include in KState

This might avoid Case 4 because:
- We only assert `(badEvent ∨ consistent)` for verified oracles
- New oracle at commit step isn't verified yet
- Case 4 (far, no bad event) only matters for verified oracles, where challenges determine the outcome

**Option F: Accept Non-Zero Error at Commit Step**

The RBR extraction failure at commit step:
- `¬KState(0) ∧ KState(1)` = prover was "bad" but became "good" by sending oracle

For Case 4 (far oracle, no bad event):
- KState(0) might be TRUE (old oracles were good)
- KState(1) should be TRUE (far oracle triggers bad event OR... ?)

Actually, a far oracle that stays far DOES trigger a bad event (Case 3 in foldingBadEvent).
Need to re-examine whether Case 4 is actually possible...

**Option G: Re-examine Case 4**

Looking at `foldingBadEvent` definition:
- Case 1 (close): bad event = disagreements vanish
- Case 2 (far): bad event = folding makes it appear close

If new oracle is far and stays far, that means Case 2's bad event is FALSE.
But `isCompliant` is also FALSE (oracle not close to code).

So `badEvent ∨ consistent` = `FALSE ∨ FALSE` = FALSE.

**Case 4 IS real.** The oracle is far, doesn't trigger Case 2 bad event, and isn't consistent.

---

## Next Steps

1. Re-examine whether the RBR framework is the right fit for FRI-Binius
2. Consider whether a different soundness proof structure is needed
3. Investigate if the global OR structure can be modified to handle commit steps
4. Check if there's a way to "delay" oracle verification in the KState

The key insight: **the paper's soundness proof uses a different structure than RBR**.
The paper uses: `Pr[cheat] ≤ Pr[bad event] + Pr[accept | no bad event ∧ non-compliant]`
RBR uses: `Pr[extraction fails] = ∑ Pr[KState false → true at round i]`

These might not align perfectly for protocols with oracle commitments.
