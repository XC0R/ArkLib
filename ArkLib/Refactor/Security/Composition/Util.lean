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

TODO: split these further and put into the right places (e.g. HVector lemmas into
HVector file, Prover/Transcript lemmas into their respective files, etc.).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal BigOperators

namespace HVector

lemma splitAt_append {α : Type*} {A : α → Type*}
    (l₁ l₂ : List α) (v₁ : HVector A l₁) (v₂ : HVector A l₂) :
    HVector.splitAt (A := A) l₁ (HVector.append v₁ v₂) = (v₁, v₂) := by
  induction l₁ with
  | nil =>
      simp [HVector.splitAt, HVector.append]
  | cons _ tl ih =>
      cases v₁ with
      | mk hd tlv =>
          simp [HVector.splitAt, HVector.append, ih (v₁ := tlv)]

@[simp] lemma cons_append {α : Type*} {A : α → Type*}
    {hd : α} {tl₁ tl₂ : List α}
    (x : A hd) (v₁ : HVector A tl₁) (v₂ : HVector A tl₂) :
    HVector.cons x (HVector.append v₁ v₂) = HVector.append (HVector.cons x v₁) v₂ := rfl

end HVector

namespace ProtocolSpec

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

namespace Transcript

lemma split_join {pSpec₁ pSpec₂ : ProtocolSpec}
    (tr₁ : Transcript pSpec₁) (tr₂ : Transcript pSpec₂) :
    Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (Transcript.join tr₁ tr₂) =
      (tr₁, tr₂) := by
  simp [Transcript.split, Transcript.join, HVector.splitAt_append]

end Transcript

namespace Prover

open ProtocolSpec.Prover

lemma run_comp_join {m : Type → Type} [Monad m] [LawfulMonad m]
    {Mid Output : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : Prover m Mid pSpec₁)
    (f : Mid → m (Prover m Output pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    (do
      let prover ← Prover.comp (m := m) (Mid := Mid) (Output := Output) (pSpec₂ := pSpec₂)
        pSpec₁ prover₁ f
      Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
        (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂)) =
      (do
        let (tr₁, mid) ← Prover.run (m := m) (Output := Mid) pSpec₁ prover₁ ch₁
        let prover₂ ← f mid
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ prover₂ ch₂
        return (Transcript.join tr₁ tr₂, out)) := by
  -- Induction on `pSpec₁`, mirroring the definitions of `Prover.comp` and `Prover.run`.
  revert prover₁ ch₁
  induction pSpec₁ with
  | nil =>
      intro prover₁ ch₁
      simp [Prover.comp, Prover.run, Challenges.join, Transcript.join, HVector.append]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover₁ ch₁
          rcases prover₁ with ⟨msg, cont⟩
          -- `P_to_V` consumes no challenges.
          -- Both sides are `cont >>= fun next => ...`; apply the IH pointwise.
          simp only [List.cons_append, comp, List.append_eq, Challenges.join, run, bind_pure_comp,
            pure_bind, bind_assoc, Transcript.join, bind_map_left]
          refine congrArg (fun k => cont >>= k) ?_
          funext next
          simpa [Prover.comp, Prover.run, Challenges.join, Transcript.join] using
            congrArg (fun z =>
              (fun a : Transcript (tl ++ pSpec₂) × Output =>
                (Transcript.cons (r := .P_to_V T oi) msg a.1, a.2)) <$> z)
              (ih (prover₁ := next) (ch₁ := ch₁))
      | V_to_P T =>
          intro prover₁ ch₁
          -- `V_to_P` consumes one challenge from `ch₁`.
          cases ch₁ with
          | mk chal chTail =>
              simp only [List.cons_append, comp, List.append_eq, Challenges.join, id_eq, run,
                HVector.head_cons, HVector.tail_cons, bind_pure_comp, pure_bind, bind_assoc,
                Transcript.join, bind_map_left]
              refine congrArg (fun k => prover₁ chal >>= k) ?_
              funext next
              simpa [Prover.comp, Prover.run, Challenges.join, Transcript.join] using
                congrArg (fun z =>
                  (fun a : Transcript (tl ++ pSpec₂) × Output =>
                    (Transcript.cons (r := .V_to_P T) chal a.1, a.2)) <$> z)
                  (ih (prover₁ := next) (ch₁ := chTail))

/-- Variant of `run_comp_join` with an extra continuation `k` after the run. -/
lemma run_comp_join_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    {Mid Output α : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : Prover m Mid pSpec₁)
    (f : Mid → m (Prover m Output pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂)
    (k : Transcript (pSpec₁ ++ pSpec₂) × Output → m α) :
    (do
      let prover ← Prover.comp (m := m) (Mid := Mid) (Output := Output) (pSpec₂ := pSpec₂)
        pSpec₁ prover₁ f
      let z ← Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
        (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂)
      k z) =
      (do
        let (tr₁, mid) ← Prover.run (m := m) (Output := Mid) pSpec₁ prover₁ ch₁
        let prover₂ ← f mid
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ prover₂ ch₂
        k (Transcript.join tr₁ tr₂, out)) := by
  -- Apply `>>= k` to both sides of `run_comp_join`.
  simpa [bind_assoc] using congrArg (fun z => z >>= k) (run_comp_join (m := m)
    (prover₁ := prover₁) (f := f) (ch₁ := ch₁) (ch₂ := ch₂))

/-- Extract the first-stage prover from a prover over `pSpec₁ ++ pSpec₂`.
Running the extracted prover over `pSpec₁` returns the residual prover for `pSpec₂`. -/
def splitPrefix {m : Type → Type} [Monad m] {Output : Type} :
    (pSpec₁ : ProtocolSpec) → {pSpec₂ : ProtocolSpec} →
    Prover m Output (pSpec₁ ++ pSpec₂) → Prover m (Prover m Output pSpec₂) pSpec₁
  | [], _, prover => prover
  | (.P_to_V _ _) :: tl, _, prover =>
      let (msg, cont) := prover
      (msg, do
        let next ← cont
        return splitPrefix tl next)
  | (.V_to_P _) :: tl, _, prover =>
      fun chal => do
        let next ← prover chal
        return splitPrefix tl next

/-- Running a prover over `pSpec₁ ++ pSpec₂` can be decomposed into:
1) run the prefix prover `splitPrefix pSpec₁ prover` on `pSpec₁`,
2) run the returned suffix prover on `pSpec₂`. -/
lemma run_splitPrefix_join
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {Output : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover : Prover m Output (pSpec₁ ++ pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
      (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂) =
      (do
        let (tr₁, p₂) ← Prover.run (m := m)
          (Output := Prover m Output pSpec₂) pSpec₁
          (splitPrefix (m := m) (Output := Output) pSpec₁ prover) ch₁
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ p₂ ch₂
        return (Transcript.join tr₁ tr₂, out)) := by
  revert prover ch₁
  induction pSpec₁ with
  | nil =>
      intro prover ch₁
      have hnil :
          (fun a : Transcript pSpec₂ × Output => (HVector.append HVector.nil a.1, a.2)) = id := by
        funext a
        cases a
        rfl
      simp [splitPrefix, Prover.run, Challenges.join, Transcript.join, hnil]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover ch₁
          rcases prover with ⟨msg, cont⟩
          simp [splitPrefix, Prover.run, Challenges.join, Transcript.join, ih, bind_assoc]
      | V_to_P T =>
          intro prover ch₁
          cases ch₁ with
          | mk chal tlCh =>
              simp [splitPrefix, Prover.run, Challenges.join, Transcript.join, ih, bind_assoc]

end Prover

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

lemma cast_cons_hvector {r : Round} {l₁ l₂ : List Round}
    (h : l₁ = l₂) (hd : r.type) (tltr : HVector Round.type l₁) :
    (hd, cast (congrArg (fun l => HVector Round.type l) h) tltr) =
      cast (congrArg (fun l => HVector Round.type (r :: l)) h) (hd, tltr) := by
  cases h
  rfl

lemma hvector_take_length_eq {pSpec : ProtocolSpec} (tr : Transcript pSpec) :
    HVector.take pSpec.length pSpec tr = PartialTranscript.ofTranscript tr := by
  induction pSpec with
  | nil =>
      cases tr
      simp [HVector.take, PartialTranscript.ofTranscript]
  | cons r tl ih =>
      cases tr with
      | mk hd tltr =>
          simpa [HVector.take, PartialTranscript.ofTranscript, ih tltr, List.take_length]
            using cast_cons_hvector (h := (List.take_length (l := tl)).symm) hd tltr

lemma hvector_take_succ_eq_concat {pSpec : ProtocolSpec}
    (k : Nat) (hk : k < pSpec.length) (tr : Transcript pSpec) :
    HVector.take (k + 1) pSpec tr =
      PartialTranscript.concat pSpec hk (HVector.take k pSpec tr)
        (HVector.get pSpec tr ⟨k, hk⟩) := by
  induction pSpec generalizing k with
  | nil =>
      cases hk
  | cons r tl ih =>
      cases k with
      | zero =>
          cases tr
          simp [HVector.take, PartialTranscript.concat, HVector.get, HVector.cons]
      | succ k =>
          cases tr with
          | mk hd tltr =>
              have hk' : k < tl.length := by simpa using hk
              simpa [HVector.take, PartialTranscript.concat, HVector.get, HVector.cons,
                HVector.head, HVector.tail] using
                congrArg (fun t => (hd, t)) (ih k hk' tltr)

end ProtocolSpec
