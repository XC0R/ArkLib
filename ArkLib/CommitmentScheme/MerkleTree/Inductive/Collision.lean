/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.MerkleTree.Inductive.Defs

/-!
# Merkle Tree Oracle Collision

Defines predicate for oracle collisions in the query log
and provides a birthday-bound.

-/

open scoped NNReal

namespace InductiveMerkleTree

open OracleSpec OracleComp List

variable {α : Type}

-- Does this exist in vcvio somewhere?
def collisionIn {α : Type} [DecidableEq α]
    (log : (spec α).QueryLog) : Prop :=
  ∃ q1 q2, (q1 ≠ q2) ∧
    q1 ∈ log ∧ q2 ∈ log ∧
    q1.2 == q2.2

/-!
### Step 1: Reformulation

Two entries `q1 ≠ q2` with `q1.2 = q2.2` necessarily have distinct inputs `q1.1 ≠ q2.1`
(because if `q1.1 = q2.1` and `q1.2 = q2.2` then `q1 = q2` as sigma types).
-/

lemma collisionIn_inputs_ne {α : Type} [DecidableEq α]
    {log : (spec α).QueryLog}
    (h : collisionIn log) :
    ∃ q1 q2, (q1.1 ≠ q2.1) ∧ q1 ∈ log ∧ q2 ∈ log ∧ q1.2 == q2.2 := by
  obtain ⟨q1, q2, hne, hm1, hm2, hresp⟩ := h
  refine ⟨q1, q2, ?_, hm1, hm2, hresp⟩
  intro heq
  -- If q1.1 = q2.1 and q1.2 = q2.2, then q1 = q2 as sigma types
  apply hne
  rcases q1 with ⟨i1, v1⟩; rcases q2 with ⟨i2, v2⟩
  simp only [Sigma.mk.inj_iff] at *
  exact ⟨heq, by subst heq; exact heq_of_eq (eq_of_beq hresp)⟩


/--
Birthday bound for oracle collisions: the probability that a computation's combined query log
contains a collision (two distinct queries that received the same hash response) is at most
`1/2 * (n - 1) * n / Fintype.card α`, where `n` is the per-index query bound.

## Proof Strategy

```
Pr[collision in log]
  ≤  ∑_{i<j<n} Pr[log[i].2 = log[j].2]          -- union bound (Step 2)
  ≤  C(n, 2) * (1/|α|)                            -- per-pair bound (Step 3)
  =  1/2 * (n-1) * n / |α|                        -- arithmetic
```

**Current status**: The individual steps are identified above but require VCVio infrastructure
(eager random oracle independence, total query count bounds) that is not yet fully formalised.
See the module docstring for details.
-/
theorem collision_probability_bound
    {β : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [OracleSpec.Fintype (spec α)] [(spec α).Inhabited]
    (oa : OracleComp (spec α) β) (n : ℕ)
    (h : IsPerIndexQueryBound oa (fun _ => n)) :
    Pr[fun z => collisionIn z.2 | oa.withQueryLog] ≤
      1 / 2 * ((n : ENNReal) - 1) * n / Fintype.card α := by
  /- Proof outline:
     1. Pr[collisionIn z.2 | oa]
          ≤  ∑_{i < j < n} Pr[log[i] and log[j] collide | oa]
        by `probEvent_or_le` (union bound) over all C(n,2) pairs
     2. Each Pr[log[i].2 = log[j].2 ∧ log[i].1 ≠ log[j].1 | oa] ≤ 1/|α|
        by `pr_pair_collision_le` (oracle independence in evalDist model)
     3. Number of pairs = C(n, 2) = 1/2 * (n-1) * n
        from `log_length_le_of_query_bound` (requires total query bound)
     4. Multiply: C(n,2)/|α| = 1/2 * (n-1) * n / |α|  ✓  -/
  sorry

end InductiveMerkleTree
