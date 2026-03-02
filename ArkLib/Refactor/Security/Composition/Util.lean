/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.StateFunction
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import VCVio.EvalDist.Fintype
import VCVio.EvalDist.Monad.Map

/-!
# Composition Utilities

Helper lemmas and definitions used by the composition theorems for completeness,
soundness, and knowledge soundness.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal BigOperators

namespace ProtocolSpec

/-! ## RBR error-map combinators -/

namespace ChallengeIndex

/-- Combine two per-challenge error maps over appended protocols. -/
def errorAppend
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (ε₁ : ChallengeIndex pSpec₁ → ℝ≥0)
    (ε₂ : ChallengeIndex pSpec₂ → ℝ≥0) :
    ChallengeIndex (pSpec₁ ++ pSpec₂) → ℝ≥0 :=
  fun i =>
    match ChallengeIndex.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i with
    | .inl j => ε₁ j
    | .inr j => ε₂ j

@[simp] lemma errorAppend_appendLeft
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (ε₁ : ChallengeIndex pSpec₁ → ℝ≥0)
    (ε₂ : ChallengeIndex pSpec₂ → ℝ≥0)
    (i : ChallengeIndex pSpec₁) :
    errorAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) ε₁ ε₂
      (ChallengeIndex.appendLeft (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i) = ε₁ i := by
  simp [errorAppend]

@[simp] lemma errorAppend_appendRight
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (ε₁ : ChallengeIndex pSpec₁ → ℝ≥0)
    (ε₂ : ChallengeIndex pSpec₂ → ℝ≥0)
    (i : ChallengeIndex pSpec₂) :
    errorAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) ε₁ ε₂
      (ChallengeIndex.appendRight (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i) = ε₂ i := by
  simp [errorAppend]

/-- Replicate a base per-challenge error map over `pSpec.replicate n`. -/
def errorReplicate
    {pSpec : ProtocolSpec}
    (ε : ChallengeIndex pSpec → ℝ≥0) :
    (n : Nat) → ChallengeIndex (pSpec.replicate n) → ℝ≥0
  | 0, i => False.elim (Fin.elim0 i.1)
  | n + 1, i =>
      match ChallengeIndex.splitReplicate (pSpec := pSpec) n i with
      | .inl j => ε j
      | .inr j => errorReplicate ε n j

@[simp] lemma errorReplicate_succ_inl
    {pSpec : ProtocolSpec}
    (ε : ChallengeIndex pSpec → ℝ≥0) (n : Nat)
    (i : ChallengeIndex pSpec) :
    errorReplicate (pSpec := pSpec) ε (n + 1)
      (ChallengeIndex.appendLeft (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n) i) = ε i := by
  simp [errorReplicate]

@[simp] lemma errorReplicate_succ_inr
    {pSpec : ProtocolSpec}
    (ε : ChallengeIndex pSpec → ℝ≥0) (n : Nat)
    (i : ChallengeIndex (pSpec.replicate n)) :
    errorReplicate (pSpec := pSpec) ε (n + 1)
      (ChallengeIndex.appendRight (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n) i) =
        errorReplicate (pSpec := pSpec) ε n i := by
  simp [errorReplicate]

end ChallengeIndex

/-! ## Oracle-aware composition boundary relation -/

/-- `FirstStageVerifierStep` captures one concrete first-stage verifier transition:
starting from verifier-boundary state `σv`, stage 1 can output `mid` and end in
state `σmid` with nonzero probability. -/
def FirstStageVerifierStep
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {S₁ S₂ : Type} {pSpec₁ : ProtocolSpec}
    (v₁ : Verifier (OracleComp oSpec) S₁ S₂ pSpec₁)
    (stmt : S₁) (tr₁ : Transcript pSpec₁)
    (σv σmid : σ) (mid : S₂) : Prop :=
  (some mid, σmid) ∈ support ((simulateQ impl (v₁ stmt tr₁).run) σv)

namespace Verifier

/-- `OracleFree v` means `v` does not query the shared oracle: its underlying `OracleComp`
computation is `pure` (hence independent of oracle state and query history). -/
def OracleFree {ι : Type} {oSpec : OracleSpec ι} {SIn SOut : Type} {pSpec : ProtocolSpec}
    (v : Verifier (OracleComp oSpec) SIn SOut pSpec) : Prop :=
  ∃ g : SIn → Transcript pSpec → Option SOut,
    ∀ stmt tr, (v stmt tr).run = pure (g stmt tr)

/-- `StatePreserving impl v` means that, after simulating the verifier under `impl`,
running it never changes the shared oracle state. -/
def StatePreserving {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) {SIn SOut : Type} {pSpec : ProtocolSpec}
    (v : Verifier (OracleComp oSpec) SIn SOut pSpec) : Prop :=
  ∀ stmt tr, StateT.StatePreserving (simulateQ impl (v stmt tr).run)

/-- `OutputIndependent impl Inv v` means the simulated verifier's output distribution
does not depend on the initial oracle state, as long as it satisfies `Inv`. -/
def OutputIndependent {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (Inv : σ → Prop)
    {SIn SOut : Type} {pSpec : ProtocolSpec}
    (v : Verifier (OracleComp oSpec) SIn SOut pSpec) : Prop :=
  ∀ stmt tr, StateT.OutputIndependent (simulateQ impl (v stmt tr).run) Inv

lemma oracleFree_statePreserving {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {SIn SOut : Type} {pSpec : ProtocolSpec}
    {v : Verifier (OracleComp oSpec) SIn SOut pSpec}
    (h : OracleFree v) :
    StatePreserving impl v := by
  rcases h with ⟨g, hg⟩
  intro stmt tr
  -- rewrite to `pure`
  simp [hg]

lemma oracleFree_outputIndependent {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (Inv : σ → Prop)
    {SIn SOut : Type} {pSpec : ProtocolSpec}
    {v : Verifier (OracleComp oSpec) SIn SOut pSpec}
    (h : OracleFree v) :
    OutputIndependent impl Inv v := by
  rcases h with ⟨g, hg⟩
  intro stmt tr
  -- rewrite to `pure`
  simp [hg]

/-!
### Why this hypothesis appears

In `Reduction.run` for a sequentially composed reduction `r₁.comp r₂`, we run the *full* composed
prover first (which executes `r₁`'s prover and then `r₂`'s prover), and only afterwards run the
composed verifier (which runs `r₁`'s verifier and then `r₂`'s verifier).

When the two stages share a stateful oracle implementation
`impl : QueryImpl oSpec (StateT σ ProbComp)`,
`r₂`'s prover may query the oracle and mutate the shared state *before* `r₁`'s verifier runs.
Thus, the usual textbook completeness composition argument is not valid without an additional
non-interference hypothesis. The minimal such hypothesis in the current model is that `r₁.verifier`
is oracle-free; we use `OracleFree` as a convenient sufficient condition.
-/

lemma oracleFree_comp {ι : Type} {oSpec : OracleSpec ι}
    {S₁ S₂ S₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    {v₁ : Verifier (OracleComp oSpec) S₁ S₂ pSpec₁}
    {v₂ : Verifier (OracleComp oSpec) S₂ S₃ pSpec₂}
    (hV₁ : OracleFree v₁) (hV₂ : OracleFree v₂) :
    OracleFree (Verifier.comp v₁ v₂) := by
  rcases hV₁ with ⟨g₁, hg₁⟩
  rcases hV₂ with ⟨g₂, hg₂⟩
  have hv₁ : ∀ stmt tr, v₁ stmt tr = OptionT.mk (pure (g₁ stmt tr)) := by
    intro stmt tr; ext; simpa using hg₁ stmt tr
  have hv₂ : ∀ stmt tr, v₂ stmt tr = OptionT.mk (pure (g₂ stmt tr)) := by
    intro stmt tr; ext; simpa using hg₂ stmt tr
  refine ⟨fun stmt tr =>
    let (tr₁, tr₂) := Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) tr
    (g₁ stmt tr₁).bind (fun mid => g₂ mid tr₂), fun stmt tr => ?_⟩
  simp only [Verifier.comp, hv₁, hv₂, OptionT.instMonad, OptionT.bind, OptionT.mk,
    OptionT.run, pure_bind]
  cases g₁ stmt (Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) tr).1 <;> simp

end Verifier

namespace Reduction

lemma oracleFree_compNth_verifier {ι : Type} {oSpec : OracleSpec ι}
    {S W : Type} {pSpec : ProtocolSpec}
    {r : Reduction (OracleComp oSpec) S W S W pSpec}
    (hV : Verifier.OracleFree r.verifier) :
    (n : Nat) → Verifier.OracleFree (r.compNth n).verifier
  | 0 => ⟨fun stmt _ => some stmt, fun _ _ => rfl⟩
  | n + 1 => Verifier.oracleFree_comp hV (oracleFree_compNth_verifier hV n)

end Reduction

/-! ## Shared utility lemmas for soundness/knowledge soundness proofs -/

lemma probEvent_exists_finset_le_sum
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {α : Type} {ι : Type} (s : Finset ι) (mx : m α) (E : ι → α → Prop)
    :
    Pr[(fun x => ∃ i ∈ s, E i x) | mx] ≤ Finset.sum s (fun i => Pr[E i | mx]) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hE :
        (fun x => ∃ i ∈ insert a s, E i x) = fun x => E a x ∨ ∃ i ∈ s, E i x := by
      funext x
      apply propext
      constructor
      · rintro ⟨i, hi, hix⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact Or.inl hix
        · exact Or.inr ⟨i, hi', hix⟩
      · intro hx
        cases hx with
        | inl hax => exact ⟨a, Finset.mem_insert_self _ _, hax⟩
        | inr hx' =>
            rcases hx' with ⟨i, hi, hix⟩
            exact ⟨i, Finset.mem_insert_of_mem hi, hix⟩
    have hor :
        Pr[(fun x => E a x ∨ ∃ i ∈ s, E i x) | mx]
          ≤ Pr[E a | mx] + Pr[(fun x => ∃ i ∈ s, E i x) | mx] := by
      rw [probEvent_eq_tsum_ite (mx := mx) (p := fun x => E a x ∨ ∃ i ∈ s, E i x)]
      rw [probEvent_eq_tsum_ite (mx := mx) (p := E a)]
      rw [probEvent_eq_tsum_ite (mx := mx) (p := fun x => ∃ i ∈ s, E i x)]
      have hle :
          (∑' y : α, if (E a y ∨ ∃ i ∈ s, E i y) then Pr[= y | mx] else 0)
            ≤ (∑' y : α, ((if E a y then Pr[= y | mx] else 0)
                + (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0))) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases ha' : E a y <;> by_cases hs' : (∃ i ∈ s, E i y) <;>
          simp [ha', hs']
      have hspl :
          (∑' y : α, ((if E a y then Pr[= y | mx] else 0)
              + (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)))
            =
          (∑' y : α, (if E a y then Pr[= y | mx] else 0))
            + (∑' y : α, (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)) := by
        simpa using (ENNReal.tsum_add
          (f := fun y : α => (if E a y then Pr[= y | mx] else 0))
          (g := fun y : α => (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)))
      exact le_trans hle (le_of_eq hspl)
    have hsum :
        Pr[E a | mx] + Pr[(fun x => ∃ i ∈ s, E i x) | mx]
          ≤ Pr[E a | mx] + Finset.sum s (fun i => Pr[E i | mx]) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih (Pr[E a | mx])
    have :
        Pr[(fun x => E a x ∨ ∃ i ∈ s, E i x) | mx]
          ≤ Pr[E a | mx] + Finset.sum s (fun i => Pr[E i | mx]) :=
      le_trans hor hsum
    simpa [hE, Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using this

end ProtocolSpec
