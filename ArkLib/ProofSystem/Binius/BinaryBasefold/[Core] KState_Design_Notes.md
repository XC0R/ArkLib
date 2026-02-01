# KState Design Principles for Round-by-Round Knowledge Soundness

## Key Lesson: Witness Types Should Track Extraction, Not Honest Computation

When defining `KnowledgeStateFunction` for round-by-round (RBR) knowledge soundness proofs, the witness type at each protocol stage should match what the **extractor** produces, not what an honest prover would compute.

### The Problem

In the fold step KState, we initially had code like:

```lean
| ⟨2, _⟩ => -- After V sends challenge
  let ⟨⟨stmtOut, oStmtOut⟩, witOut⟩ := getFoldProverFinalOutput ... witMid ...
  masterKStateProp ... (wit := witOut) ...
```

This failed with a type mismatch because:
- `witMid : foldWitMid i ⟨2, _⟩ = Witness i.succ` (already the output type)
- `getFoldProverFinalOutput` expects `Witness i.castSucc` (input type)

### The Root Cause

The code was trying to **simulate honest prover witness computation** inside KState. But the prover is potentially malicious, so:
1. We cannot assume the prover follows honest computation
2. The witness at each stage comes from the **extractor** running on the transcript
3. KState only verifies that extracted witnesses satisfy required invariants

### The Correct Design

#### 1. Define `WitMid m` to match extractor output at each round

```lean
def foldWitMid (i : Fin ℓ) : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => Witness i.castSucc  -- Before any messages
  | ⟨1, _⟩ => Witness i.castSucc  -- After P→V message (extractor hasn't advanced yet)
  | ⟨2, _⟩ => Witness i.succ      -- After V→P challenge (extractor has advanced)
```

The witness type changes at the round where the extractor advances (typically after receiving a challenge).

#### 2. Use `extractOut = id` pattern

When `WitMid (final round) = WitOut`:
- `extractOut` can be the identity function
- `toFun_full` proofs become simpler (no witness transformation needed)
- The extracted witness is directly usable in the output relation

#### 3. Compute statement/oracle updates from transcript, not witness

In KState at the final round:
```lean
| ⟨2, _⟩ => 
  let h_i := tr.messages ⟨0, rfl⟩
  let r_i' := tr.challenges ⟨1, rfl⟩
  -- Compute stmtOut from transcript (what verifier computes)
  let stmtOut := { ctx := stmt.ctx, sumcheck_target := h_i.eval r_i', ... }
  -- Use witMid directly (already the right type from extractor)
  let witOut := witMid
  masterKStateProp ... (stmt := stmtOut) (wit := witOut) ...
```

### Summary

| Aspect | Wrong Approach | Correct Approach |
|--------|----------------|------------------|
| Witness source | Honest prover simulation | Extractor output |
| `WitMid m` type | Fixed across all rounds | Changes when extractor advances |
| Statement computation | From witness evolution | From transcript (verifier's view) |
| `extractOut` | Complex transformation | Identity (when possible) |

### Why This Works

1. **Soundness is about extraction**: We're proving that if the verifier accepts, there exists a valid witness. The extractor constructs this witness from the transcript.

2. **Malicious prover**: The prover may not follow the protocol, so we can't rely on witness evolution matching honest computation.

3. **Transcript is ground truth**: The verifier only sees the transcript. KState properties should be expressible in terms of transcript-derived values.

4. **Type-level encoding**: Having `WitMid m` change types at extraction points makes it impossible to accidentally use honest-prover logic where extraction logic is needed.
