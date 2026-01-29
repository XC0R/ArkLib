# Fold Step KState: Visual Analysis

## KState Transition Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         FOLD STEP (Round i)                             │
│                         Protocol: P → V → V                             │
│                         Messages: h_i(X), r_i'                          │
└─────────────────────────────────────────────────────────────────────────┘

Round 0: BEFORE PROVER MESSAGE
┌──────────────────────────────────────────────────────────────────────┐
│  foldKStateProp (m=0)                                                │
│                                                                      │
│  masterKStateProp with:                                              │
│    localChecks := sumcheckConsistencyProp(s, H)                     │
│    core := badEventExists ∨ oracleWitnessConsistency               │
│                                                                      │
│  ≡ relIn = roundRelation(i.castSucc)                               │
│                                                                      │
│  Witness: wit_0 with H, f, t                                        │
└──────────────────────────────────────────────────────────────────────┘
         │
         │ Prover sends: h_i(X) = Σ_{w ∈ B_{ℓ-i-1}} H(r'_0,...,r'_{i-1}, X, w)
         ↓
Round 1: AFTER PROVER MESSAGE, BEFORE CHALLENGE
┌──────────────────────────────────────────────────────────────────────┐
│  foldKStateProp (m=1)                                                │
│                                                                      │
│  masterKStateProp with:                                              │
│    localChecks :=                                                    │
│      explicitVCheck: h_i(0) + h_i(1) = s                           │
│      localizedRoundPolyCheck: h_i = h_star                         │
│        where h_star := getSumcheckRoundPoly(H)                     │
│    core := badEventExists ∨ oracleWitnessConsistency               │
│                                                                      │
│  Witness: wit_0 (same as round 0)                                   │
│  Transcript: contains h_i(X)                                         │
└──────────────────────────────────────────────────────────────────────┘
         │
         │ Verifier samples: r_i' ← L
         ↓
Round 2: AFTER CHALLENGE (FULL TRANSCRIPT)
┌──────────────────────────────────────────────────────────────────────┐
│  foldKStateProp (m=2)                                                │
│                                                                      │
│  masterKStateProp with:                                              │
│    localChecks :=                                                    │
│      localizedRoundPolyCheck: h_i = h_star                         │
│      nextSumcheckTargetCheck: h_i(r_i') = h_star(r_i')             │
│    core := badEventExists ∨ oracleWitnessConsistency               │
│                                                                      │
│  Witness: wit_0 (extractor is identity)                             │
│  Transcript: contains h_i(X) and r_i'                               │
└──────────────────────────────────────────────────────────────────────┘
         │
         │ Verifier outputs: stmt_{i+1}, oStmt_{i.castSucc}
         │ Prover outputs: stmt_{i+1}, oStmt_{i.castSucc}, wit_{i+1}
         ↓
         ╔═══════════════════════════════════════════════════════════╗
         ║  MUST SATISFY: relOut = foldStepRelOut(i)                ║
         ║                                                           ║
         ║  masterKStateProp(i.succ) with:                          ║
         ║    stmtIdx := i.succ                                     ║
         ║    oracleIdx := i.castSucc (no commitment yet)           ║
         ║    localChecks := sumcheckConsistencyProp(s', H')        ║
         ║      where H' is the folded polynomial                   ║
         ╚═══════════════════════════════════════════════════════════╝
```

---

## Property Requirements

### 1. toFun_empty ✅ (Trivial - by construction)
```
        relIn
          ↕
  foldKStateProp(0)

Proof: Both use identical masterKStateProp definitions
```

### 2. toFun_next ❌ (NEEDS PROOF)
```
  foldKStateProp(1)  →  foldKStateProp(0)
         ↓                      ↑
   [with h_i]           [witness extracted]

Challenge: Prove that if the prover sent a polynomial h_i that passes
          the checks at round 1, then the witness at round 0 must
          have been consistent.

Key Insight: 
  - At round 1: h_i = h_star ∧ h_i(0) + h_i(1) = s
  - At round 0: sumcheckConsistencyProp(s, H)
  - Need: h_star satisfying round 1 checks ⟹ H satisfies round 0 checks
```

### 3. toFun_full ❌ (NEEDS PROOF)
```
         Pr[(stmtOut, witOut) ∈ relOut] > 0
                    ↓
         foldKStateProp(2) holds

Challenge: Show that if verifier can output a valid statement with
          probability > 0, then the extracted witness satisfies the
          full KState at round 2.

Key Steps:
  1. Verifier output implies guard passed
  2. Guard passing implies polynomial consistency checks
  3. relOut structure matches foldKStateProp(2) requirements
```

---

## RBR Knowledge Soundness: The Doom Escape Event

```
┌────────────────────────────────────────────────────────────────────┐
│  DOOM ESCAPE: False → True transition after random challenge       │
└────────────────────────────────────────────────────────────────────┘

Timeline:
  Round 0 → Round 1 → Challenge r_i' → Round 2
    ❌         ❌           (random)        ✅
  FALSE      FALSE                        TRUE

Interpretation:
  - At round 0: (stmt, wit_extracted) ∉ relIn
  - At round 1: KState still false (same witness)
  - After r_i': KState becomes true!

How is this possible?
  Case 1: Prover sent incorrect polynomial h_i ≠ h_star
          BUT h_i(r_i') = h_star(r_i') by luck!
          
  Case 2: Bad event occurred (folding consistency violated)

Schwartz-Zippel Bound:
  If h_i ≠ h_star (both degree ≤ d), then:
    Pr[h_i(r_i') = h_star(r_i') | r_i' ← L] ≤ d / |L|
  
  For sumcheck: d = 1, so probability ≤ 1/|L|

Bad Event Bound:
  If ϑ | (i+1) (commitment round):
    New bad events can occur with probability ϑ * |S^(i+1)| / |L|
  Else: 0

Total Error:
  foldKnowledgeError(i) = 1/|L| + err_BE
```

---

## Polynomial Relationship Diagram

```
                    Witness H: ℕ^{ℓ-i} → L
                           │
                           │ projectToMidSumcheckPoly
                           ↓
              Mid-Polynomial H_i: ℕ^{ℓ-i} → L
                           │
                           │ getSumcheckRoundPoly
                           ↓
           Round Polynomial h_star: L[X] (degree 1)
                           │
                           │ (honest prover)
                           ↓
              Prover Message: h_i(X) : L[X]
                           │
                           │ Verifier checks:
                           │   1. h_i(0) + h_i(1) = s
                           │   2. (implicitly) h_i = h_star?
                           ↓
                    Challenge: r_i' ← L
                           │
                           ↓
         Next Target: s' = h_i(r_i') = h_star(r_i')

KEY QUESTION: When does h_i ≠ h_star but h_i(r_i') = h_star(r_i')?
ANSWER: With probability ≤ 1/|L| (Schwartz-Zippel)
```

---

## Proof Obligations Summary

### Helper Lemmas Needed:

1. **Round Polynomial Properties**
   ```lean
   lemma getSumcheckRoundPoly_consistent :
     sumcheckConsistencyProp s H →
     let h := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H)
     h.eval (𝓑 0) + h.eval (𝓑 1) = s
   ```

2. **Oracle Preservation**
   ```lean
   lemma foldStep_preserves_oracle :
     embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx →
     ∀ j, oStmtOut j = (via embed) oStmtIn
   ```

3. **Verifier Output Validity**
   ```lean
   lemma verifier_output_satisfies_relOut :
     verifier.run succeeds →
     guard passes →
     (stmtOut, witOut) ∈ foldStepRelOut
   ```

4. **Schwartz-Zippel Instantiation**
   ```lean
   lemma polynomial_agreement_probability :
     h_i ≠ h_star →
     deg h_i ≤ 1 →
     deg h_star ≤ 1 →
     Pr[h_i.eval r = h_star.eval r | r ← L] ≤ 1 / |L|
   ```

---

## Proof Strategy Checklist

- [ ] Phase 1: Basic Lemmas
  - [ ] Round polynomial evaluation properties
  - [ ] Sumcheck consistency preservation
  - [ ] Oracle embedding correctness

- [ ] Phase 2: toFun_next
  - [ ] Show h_i = h_star implies H consistent
  - [ ] Show checks at round 1 imply checks at round 0
  - [ ] Handle masterKStateProp preservation

- [ ] Phase 3: toFun_full
  - [ ] Extract oracle agreement from verifier
  - [ ] Show relOut implies KState at round 2
  - [ ] Verify extracted witness correctness

- [ ] Phase 4: Main RBR KS
  - [ ] Formalize doom escape probability
  - [ ] Apply Schwartz-Zippel
  - [ ] Add bad event probability
  - [ ] Combine error terms

- [ ] Phase 5: Integration
  - [ ] Verify extractor correctness
  - [ ] Check all type constraints
  - [ ] Complete the theorem
