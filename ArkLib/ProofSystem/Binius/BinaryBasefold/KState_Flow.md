# Binary Basefold: Complete KState & Relation Flow

This document traces all Knowledge States (KState) and Relations through the Binary Basefold protocol steps,
showing which security proofs connect each consecutive pair.

AI prompt:
```
I want you to gather ALL the current KState (with specific m index) & rbr ks relations (relIn/relOut) of the steps of Binary Basefold. From fold -> commit/relay -> final sumcheck step. From relIn -> KState 0 -> KState 1 -> ... KState (Fin.last pSpec_size) -> relOut. Each KState/relation per line. write them into a markdown. Between each consecutive pair of 2 KState/relation, write out which secuiity proof that the transition between them involve, e.g. toFun_next, toFun_full, rbr KS, etc. Write into a markdown file 
```
## Notation

- `masterKStateProp(stmtIdx, oracleIdx, stmt, wit, oStmt, localChecks)` = `localChecks ∧ (badEventExistsProp ∨ oracleWitnessConsistency)`
- `oracleWitnessConsistency` = `witnessStructuralInvariant ∧ firstOracleConsistency ∧ oracleFoldingConsistency`
- `sumcheckConsistencyProp(s, H)` = `s = ∑ x ∈ (univ.map 𝓑)^ᶠ(ℓ - i), H.val.eval x`

---

## FOLD STEP (Round `i : Fin ℓ`)

**Protocol Spec:** `pSpecFold = [P→V: L⦃≤2⦄[X], V→P: L]` (size = 2)

### relIn: `roundRelation i.castSucc`
```
roundRelationProp i.castSucc = masterKStateProp(
  stmtIdx    := i.castSucc,
  oracleIdx  := mkFromStmtIdx i.castSucc,
  stmt       := stmt,
  wit        := wit,
  oStmt      := oStmt,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

↓ **[toFun_empty]** (definitional equality via `rfl`)

### foldKStateProp m=0
```
masterKStateProp(
  stmtIdx    := i.castSucc,
  oracleIdx  := mkFromStmtIdx i.castSucc,
  stmt       := stmt,
  wit        := witMid,
  oStmt      := oStmt,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target witMid.H
)
```

↓ **[toFun_next]** (P sends h_i(X))
- Proves: `explicitVCheck ∧ localizedRoundPolyCheck` ⟹ `sumcheckConsistencyProp`
- Key lemma: `getSumcheckRoundPoly_sum_eq`
- Core `(badEvent ∨ oracleConsistency)` preserved: `exact h_core`

### foldKStateProp m=1
```
masterKStateProp(
  stmtIdx    := i.castSucc,
  oracleIdx  := mkFromStmtIdx i.castSucc,
  stmt       := stmt,
  wit        := witMid,
  oStmt      := oStmt,
  localChecks := explicitVCheck ∧ localizedRoundPolyCheck
    where explicitVCheck   := h_i(0) + h_i(1) = stmt.sumcheck_target
          localizedRoundPolyCheck := h_i = h_star
)
```

↓ **[toFun_full]** (V sends r_i', verifier completes)
- Uses: `h_relOut : foldStepRelOutProp`
- Computes: `witOut := getFoldProverFinalOutput(..., witMid, h_i, r_i')`
- **ISSUE**: Needs `h_witOut_H_eq : witOut.H = projectToNextSumcheckPoly extractedWitLast.H r_i'`
- Splits on `badEvent ∨ oracleConsistency` in `h_relOut`

### foldKStateProp m=2 (= Fin.last 2)
```
masterKStateProp(
  stmtIdx    := i.succ,                              -- ADVANCED
  oracleIdx  := mkFromStmtIdxCastSuccOfSucc i,       -- LAGGING (oracle not committed yet)
  stmt       := stmtOut,
  wit        := witOut,
  oStmt      := oStmtOut,
  localChecks := sumcheckConsistencyProp stmtOut.sumcheck_target witOut.H
)
```

↓ **[RBR Knowledge Soundness theorem]**

### relOut: `foldStepRelOut i`
```
foldStepRelOutProp i = masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdxCastSuccOfSucc i,       -- LAGGING
  stmt       := stmt,
  wit        := wit,
  oStmt      := oStmt,                               -- oracle count at i.castSucc
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

---

## COMMIT STEP (Round `i : Fin ℓ`, when `isCommitmentRound ℓ ϑ i`)

**Protocol Spec:** `pSpecCommit = [P→V: OracleFunction]` (size = 1)

### relIn: `foldStepRelOut i`
```
foldStepRelOutProp i = masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdxCastSuccOfSucc i,       -- LAGGING
  stmt       := stmtIn,
  wit        := witIn,
  oStmt      := oStmtIn,                             -- oracle count at i.castSucc
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witIn.H
)
```

↓ **[toFun_empty]** (definitional equality)

### commitKStateProp m=0
```
masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdxCastSuccOfSucc i,       -- LAGGING
  stmt       := stmtIn,
  wit        := witMid,
  oStmt      := oStmtIn,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witMid.H
)
```

↓ **[toFun_next]** (P sends new oracle f_{i+1})
- **PROBLEM**: `oracleIdx` advances from `mkFromStmtIdxCastSuccOfSucc i` to `mkFromStmtIdx i.succ`
- This requires proving oracle consistency for the NEW oracle
- But at toFun_next, we don't know if the new oracle is consistent!
- **CURRENTLY SORRY**

### commitKStateProp m=1 (= Fin.last 1)
```
masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdx i.succ,                -- ADVANCED (synchronized)
  stmt       := stmtIn,
  wit        := witMid,
  oStmt      := snoc_oracle oStmtIn (tr.messages ⟨0, rfl⟩),  -- EXTENDED with new oracle
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witMid.H
)
```

↓ **[toFun_full]** (verifier completes)
- Uses: `h_relOut : roundRelationProp i.succ`
- Key lemma: `snoc_oracle_eq_mkVerifierOStmtOut_commitStep`
- Splits on `badEvent ∨ oracleConsistency` in `h_relOut`

↓ **[RBR Knowledge Soundness theorem]**

### relOut: `roundRelation i.succ`
```
roundRelationProp i.succ = masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdx i.succ,                -- SYNCHRONIZED
  stmt       := stmt,
  wit        := wit,
  oStmt      := oStmt,                               -- oracle count at i.succ
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

---

## RELAY STEP (Round `i : Fin ℓ`, when `¬isCommitmentRound ℓ ϑ i`)

**Protocol Spec:** `pSpecRelay = []` (size = 0, no messages)

### relIn: `foldStepRelOut i`
```
foldStepRelOutProp i = masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdxCastSuccOfSucc i,       -- LAGGING
  stmt       := stmtIn,
  wit        := witIn,
  oStmt      := oStmtIn,
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witIn.H
)
```

↓ **[toFun_empty]** (uses `badEventExistsProp_relay_preserved`, `oracleWitnessConsistency_relay_preserved`)

### relayKStateProp (m=0 = Fin.last 0)
```
masterKStateProp(
  stmtIdx    := i.succ,
  oracleIdx  := mkFromStmtIdx i.succ,                -- ADVANCED (no new oracle, just remapped)
  stmt       := stmtIn,
  wit        := witMid,
  oStmt      := mapOStmtOutRelayStep oStmtIn,        -- REMAPPED (same count, different type)
  localChecks := sumcheckConsistencyProp stmtIn.sumcheck_target witMid.H
)
```

↓ **[toFun_full]** (no messages, so toFun_next not needed)
- Uses: `h_relOut : roundRelationProp i.succ`
- Key lemma: `mapOStmtOut_eq_mkVerifierOStmtOut_relayStep`

↓ **[RBR Knowledge Soundness theorem]**

### relOut: `roundRelation i.succ`
```
(same as commit step relOut)
```

---

## FINAL SUMCHECK STEP (at `i = Fin.last ℓ`)

**Protocol Spec:** `pSpecFinalSumcheckStep = [P→V: L]` (size = 1)

### relIn: `roundRelation (Fin.last ℓ)`
```
roundRelationProp (Fin.last ℓ) = masterKStateProp(
  stmtIdx    := Fin.last ℓ,
  oracleIdx  := mkFromStmtIdx (Fin.last ℓ),
  stmt       := stmt,
  wit        := wit,
  oStmt      := oStmt,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target wit.H
)
```

↓ **[toFun_empty]** (definitional equality)

### finalSumcheckKStateProp m=0
```
masterKStateProp(
  stmtIdx    := Fin.last ℓ,
  oracleIdx  := mkFromStmtIdx (Fin.last ℓ),
  stmt       := stmt,
  wit        := witMid,
  oStmt      := oStmt,
  localChecks := sumcheckConsistencyProp stmt.sumcheck_target witMid.H
)
```

↓ **[toFun_next]** (P sends final constant c)
- Proves: KState 0 ⟹ KState 1
- **CURRENTLY SORRY**

### finalSumcheckKStateProp m=1 (= Fin.last 1)
```
sumcheckFinalCheck ∧ finalSumcheckStepFoldingStateProp
  where sumcheckFinalCheck := stmt.sumcheck_target = eqTilde(r) * c
        finalSumcheckStepFoldingStateProp := oracleFoldingConsistency ∨ foldingBadEventExists
```

↓ **[toFun_full]** (verifier completes)
- Uses: `h_relOut : finalSumcheckRelOutProp`

↓ **[RBR Knowledge Soundness theorem]**

### relOut: `finalSumcheckRelOut`
```
finalSumcheckRelOutProp = finalSumcheckStepFoldingStateProp (stmtOut, oStmt)
  where finalSumcheckStepFoldingStateProp := oracleFoldingConsistency ∨ foldingBadEventExists
```

---

## Summary: Security Proof Requirements

| Step | Transition | Proof | Status | Issue |
|------|-----------|-------|--------|-------|
| Fold | relIn → KState 0 | toFun_empty | ✓ | definitional |
| Fold | KState 0 → KState 1 | toFun_next | ✓ | uses `getSumcheckRoundPoly_sum_eq` |
| Fold | KState 1 → KState 2 | toFun_next | N/A | V→P message (no proof needed) |
| Fold | KState 2 → relOut | toFun_full | **sorry** | needs `witnessStructuralInvariant` |
| Commit | relIn → KState 0 | toFun_empty | ✓ | definitional |
| Commit | KState 0 → KState 1 | toFun_next | **sorry** | oracleIdx advances, can't prove oracle consistency |
| Commit | KState 1 → relOut | toFun_full | ✓ | uses `snoc_oracle_eq_mkVerifierOStmtOut_commitStep` |
| Relay | relIn → KState 0 | toFun_empty | ✓ | uses preservation lemmas |
| Relay | KState 0 → relOut | toFun_full | ✓ | uses `mapOStmtOut_eq_mkVerifierOStmtOut_relayStep` |
| Final | relIn → KState 0 | toFun_empty | ✓ | definitional |
| Final | KState 0 → KState 1 | toFun_next | **sorry** | pending |
| Final | KState 1 → relOut | toFun_full | ✓ | |

---

## Key Observations

### 1. The `oracleIdx` Advancement Problem (Commit Step)

At `commitKStateProp`:
- **m=0**: `oracleIdx = mkFromStmtIdxCastSuccOfSucc i` (lagging, oracle at `i.castSucc`)
- **m=1**: `oracleIdx = mkFromStmtIdx i.succ` (synchronized, oracle at `i.succ`)

This advancement happens at `toFun_next`, but we receive an **arbitrary** oracle message.
We cannot prove the new oracle is consistent without information from `relOut`.

**Proposed Fix**: Don't advance `oracleIdx` at `toFun_next`. Keep it lagging until `toFun_full`.

### 2. The `witnessStructuralInvariant` Problem (Fold Step)

At `foldKStateProp m=2`, we need to prove:
```
witOut.H = projectToNextSumcheckPoly extractedWitLast.H r_i'
```

This requires `witnessStructuralInvariant witOut`, which is only available in the
`oracleWitnessConsistency` case, not in the `badEvent` case.

**Proposed Fix**: Put `witnessStructuralInvariant` outside the OR in `masterKStateProp`:
```
masterKStateProp = localChecks ∧ witnessStructuralInvariant ∧ (badEvent ∨ oracleConsistencies)
```

### 3. The Extractor Design

The extractor always produces witnesses where `H` and `f` are computed from `t`:
```lean
extractedWitLast = {
  t := witOut.t,
  H := projectToMidSumcheckPoly witOut.t ...,
  f := getMidCodewords witOut.t ...
}
```

This means `witnessStructuralInvariant extractedWitLast` holds **by construction**.
The question is whether `witnessStructuralInvariant witOut` also holds.
