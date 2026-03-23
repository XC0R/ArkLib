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

section ToMathlib

lemma foo (k d : ℕ) (hkd : d ∣ k) : (((k / d) : ℕ) : ENNReal) = (k : ENNReal) / (d : ENNReal) := by
  obtain ⟨m, hm⟩ := hkd; subst hm
  cases d with
  | zero => simp
  | succ d =>
    rw [Nat.mul_div_cancel_left m (Nat.succ_pos d)]
    simp only [Nat.cast_mul, Nat.cast_succ]
    have hd : (d : ENNReal) + 1 ≠ 0 := by positivity
    have hdtop : (d : ENNReal) + 1 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top d, ENNReal.one_ne_top⟩
    rw [mul_comm, ENNReal.mul_div_cancel_right hd hdtop]

end ToMathlib

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
If there is a per-index query bound `n`, then every execution's query log has length at most `n`.
-/
theorem queryLog_length_le_of_isPerIndexQueryBound {α β : Type} [DecidableEq α]
    (oa : OracleComp (spec α) β) (n : ℕ)
    (hoa : oa.IsPerIndexQueryBound fun x ↦ n) : ∀ z ∈ support oa.withQueryLog, length z.2 ≤ n := by
  sorry

theorem prob_single_collision {α β : Type} [inst : DecidableEq α]
    [inst_1 : Fintype α] [inst_2 : (spec α).Fintype] [inst_3 : (spec α).Inhabited]
    (oa : OracleComp (spec α) β) (n : ℕ)
    (hlen : ∀ z ∈ support oa.withQueryLog, length z.2 ≤ n) (i j : Fin n) (hij : i < j) :
    Pr[fun z ↦ ∃ q1 q2, z.2[↑i]? = some q1 ∧ z.2[↑j]? = some q2 ∧
        q1.fst ≠ q2.fst ∧ (q1.snd == q2.snd) = true |
        oa.withQueryLog] ≤
      1 / ↑(Fintype.card α) := by
  sorry

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
  /- Step 1 (requires VCVio infrastructure):
     From `IsPerIndexQueryBound oa (fun _ => n)`, every execution's query log has
     length at most n. This needs a lemma relating per-index query bounds to total
     query log length (e.g., via `counting_bounded` + a count-to-length bridge). -/
  have hlog_len : ∀ z ∈ support oa.withQueryLog, z.2.length ≤ n := by
    exact fun z a ↦ queryLog_length_le_of_isPerIndexQueryBound oa n h z a
  -- Abbreviate the log entry type: entries have the form ⟨input : α × α, response : α⟩.
  let E : Type := (t : (spec α).Domain) × (spec α).Range t
  /- Step 2 (requires VCVio infrastructure):
     Per-pair collision bound via oracle independence in the random oracle model.
     Two entries at distinct positions in the log with distinct inputs receive
     independent uniform responses from α, so the probability of equal responses
     is at most 1/|α|. Needs: eager random oracle independence lemma. -/
  have hpair : ∀ (i j : Fin n), i.val < j.val →
      Pr[fun z : β × (spec α).QueryLog =>
          ∃ q1 q2 : E, z.2[i.val]? = some q1 ∧ z.2[j.val]? = some q2 ∧
                   q1.1 ≠ q2.1 ∧ q1.2 == q2.2 | oa.withQueryLog] ≤
        1 / (Fintype.card α : ENNReal) := by
    exact fun i j a ↦
      prob_single_collision oa n hlog_len i j a
  calc Pr[fun z => collisionIn z.2 | oa.withQueryLog]
      /- Reduction: a collision in the log of length ≤ n implies some pair (i, j)
         of positions with i < j < n has colliding entries. -/
      ≤ Pr[fun z : β × (spec α).QueryLog =>
              ∃ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
                      (fun p => p.1.val < p.2.val),
              ∃ q1 q2 : E, z.2[p.1.val]? = some q1 ∧ z.2[p.2.val]? = some q2 ∧
                       q1.1 ≠ q2.1 ∧ q1.2 == q2.2 | oa.withQueryLog] := by
        apply probEvent_mono
        intro z hmem hcoll
        obtain ⟨q1, q2, hne, hm1, hm2, hresp⟩ := collisionIn_inputs_ne hcoll
        have hlen := hlog_len z hmem
        -- q1 and q2 are in z.2 (length ≤ n), so they sit at positions i, j < n;
        -- since q1.1 ≠ q2.1, their positions are distinct; take WLOG i < j.
        rw [List.mem_iff_getElem] at hm1 hm2
        obtain ⟨i1, hi1, hget1⟩ := hm1
        obtain ⟨i2, hi2, hget2⟩ := hm2
        have hi1n : i1 < n := lt_of_lt_of_le hi1 hlen
        have hi2n : i2 < n := lt_of_lt_of_le hi2 hlen
        have hget1? : z.2[i1]? = some q1 := by
          rw [List.getElem?_eq_getElem hi1]; exact congr_arg some hget1
        have hget2? : z.2[i2]? = some q2 := by
          rw [List.getElem?_eq_getElem hi2]; exact congr_arg some hget2
        have hne_idx : i1 ≠ i2 := by
          intro heq
          apply hne
          have h : z.2[i1]? = z.2[i2]? := congr_arg (z.2[·]?) heq
          simp only [hget1?, hget2?, Option.some.injEq] at h
          exact congr_arg Sigma.fst h
        rcases Nat.lt_or_gt_of_ne hne_idx with h | h
        · exact ⟨(⟨i1, hi1n⟩, ⟨i2, hi2n⟩), by simp [h], q1, q2, hget1?, hget2?, hne, hresp⟩
        · exact ⟨(⟨i2, hi2n⟩, ⟨i1, hi1n⟩), by simp [h], q2, q1, hget2?, hget1?, hne.symm,
            by rw [beq_iff_eq]; exact (eq_of_beq hresp).symm⟩
      /- Union bound: Pr[∃ p ∈ S, E p] ≤ ∑ p ∈ S, Pr[E p]. -/
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
                  (fun p => p.1.val < p.2.val),
            Pr[fun z : β × (spec α).QueryLog =>
                ∃ q1 q2 : E, z.2[p.1.val]? = some q1 ∧ z.2[p.2.val]? = some q2 ∧
                         q1.1 ≠ q2.1 ∧ q1.2 == q2.2 | oa.withQueryLog] :=
          probEvent_exists_finset_le_sum _ _ _
      /- Per-pair bound: each pair event has probability ≤ 1/|α|. -/
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
                  (fun p => p.1.val < p.2.val),
            (1 : ENNReal) / Fintype.card α := by
          apply Finset.sum_le_sum
          intro ⟨i, j⟩ hmem
          exact hpair i j (Finset.mem_filter.mp hmem).2
      /- Arithmetic: |{(i,j) : Fin n × Fin n | i < j}| = C(n,2) = n*(n-1)/2. -/
      _ = 1 / 2 * ((n : ENNReal) - 1) * n / Fintype.card α := by
          simp only [Fin.val_fin_lt, Finset.sum_const, nsmul_eq_mul]
          have : Finset.card {p : Fin n × Fin n | p.1 < p.2} = (n * (n - 1)) / 2 := by
            have heq : ({p : Fin n × Fin n | p.1 < p.2} : Finset _).card =
                (Finset.univ.sigma (fun i : Fin n => Finset.Ioi i)).card := by
              apply Finset.card_bij (fun p _ => (⟨p.1, p.2⟩ : Σ i : Fin n, Fin n))
              · intro p hp; simp [Finset.mem_sigma, Finset.mem_Ioi]; simpa using hp
              · intro ⟨a, b⟩ h₁ ⟨c, d⟩ h₂ heq
                simp only [Sigma.mk.inj_iff, heq_iff_eq] at heq
                exact Prod.ext heq.1 heq.2
              · intro ⟨i, j⟩ hj
                simp only [Finset.mem_sigma, Finset.mem_Ioi, Finset.mem_univ, true_and] at hj
                exact ⟨⟨i, j⟩, by simpa using hj, rfl⟩
            rw [heq, Finset.card_sigma]
            simp only [Fin.card_Ioi, Fin.sum_univ_eq_sum_range]
            calc ∑ i ∈ Finset.range n, (n - 1 - i)
                = ∑ i ∈ Finset.range n, id (n - 1 - i) := by simp [id]
              _ = ∑ i ∈ Finset.range n, id i := Finset.sum_range_reflect id n
              _ = n * (n - 1) / 2 := by simp [id, Finset.sum_range_id]
          rw [this] ; clear this
          have key : (↑(n * (n - 1) / 2) : ENNReal) = 1 / 2 * (↑n - 1) * ↑n := by
            cases n with
            | zero => simp
            | succ k =>
              simp only [Nat.succ_sub_one, Nat.cast_succ]
              simp only [ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top,
                not_false_eq_true, AddLECancellable.add_tsub_cancel_right]
              have hdvd : 2 ∣ k * (k + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
              rw [show (k + 1) * k = k * (k + 1) from by ring]
              -- grind -- should work here
              apply (ENNReal.mul_right_inj (by norm_num : (2:ENNReal) ≠ 0) (by norm_num)).mp
              -- rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
              rw [foo (k * (k + 1)) 2 hdvd]
              push_cast [hdvd]
              -- grind -- should work here
              congr
              rw [div_eq_mul_inv]
              simp
              grind
          rw [key]
          congr
          simp

end InductiveMerkleTree
