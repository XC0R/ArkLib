import ArkLib.Refactor.Telescope.Reduction
import ArkLib.Data.Probability.Instances

/-!
# Telescope Security Definitions

The telescope-native bridge from structural claim trees to verifier soundness:

- `ClaimTree.IsSound.bound_terminalProb` bounds the probability that a bad root
  claim reaches a good terminal claim under any adversarial prover.
- `Verifier.soundness_of_isSound` upgrades that terminal bound to statement-indexed
  verifier soundness once acceptance implies the terminal claim predicate.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace ProtocolCtx

namespace ClaimTree

private theorem probEvent_bind_le_const
    {α β : Type} (mx : ProbComp α) (my : α → ProbComp β) (bad : β → Prop)
    (ε : ℝ≥0∞) (hPoint : ∀ x, Pr[bad | my x] ≤ ε) :
    Pr[bad | mx >>= my] ≤ ε := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc
    ∑' x, Pr[= x | mx] * Pr[bad | my x]
        ≤ ∑' x, Pr[= x | mx] * ε := by
          refine ENNReal.tsum_le_tsum ?_
          intro x
          exact mul_le_mul' le_rfl (hPoint x)
    _ = (∑' x, Pr[= x | mx]) * ε := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ε := by
      exact mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = ε := by simp

private theorem probEvent_bind_le_of_cond
    {α β : Type} (mx : ProbComp α) (my : α → ProbComp β) (bad : β → Prop)
    (cond : α → Prop) [DecidablePred cond] (δ : ℝ≥0∞)
    (hPoint : ∀ x, Pr[bad | my x] ≤ if cond x then 1 else δ) :
    Pr[bad | mx >>= my] ≤ Pr[cond | mx] + δ := by
  rw [probEvent_bind_eq_tsum]
  calc
    ∑' x, Pr[= x | mx] * Pr[bad | my x]
        ≤ ∑' x, Pr[= x | mx] * (if cond x then 1 else δ) := by
          refine ENNReal.tsum_le_tsum ?_
          intro x
          exact mul_le_mul' le_rfl (hPoint x)
    _ ≤ ∑' x, (if cond x then Pr[= x | mx] else 0) + ∑' x, Pr[= x | mx] * δ := by
          rw [← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum ?_
          intro x
          by_cases hcond : cond x <;> simp [hcond]
    _ = Pr[cond | mx] + ∑' x, Pr[= x | mx] * δ := by
          rw [probEvent_eq_tsum_ite]
    _ ≤ Pr[cond | mx] + δ := by
          calc
            Pr[cond | mx] + ∑' x, Pr[= x | mx] * δ
                = Pr[cond | mx] + (∑' x, Pr[= x | mx]) * δ := by
                    rw [ENNReal.tsum_mul_right]
            _ ≤ Pr[cond | mx] + 1 * δ := by
                    let pCond : ENNReal := Pr[cond | mx]
                    have hMul : (∑' x, Pr[= x | mx]) * δ ≤ 1 * δ :=
                      mul_le_mul' tsum_probOutput_le_one le_rfl
                    have hAdd : pCond + (∑' x, Pr[= x | mx]) * δ ≤ pCond + 1 * δ := by
                      exact add_le_add_right hMul pCond
                    exact hAdd
            _ = Pr[cond | mx] + δ := by simp

/-- A sound claim tree bounds the probability of reaching a good terminal claim
when started from a bad root claim. -/
theorem IsSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T) :
    {ctx : ProtocolCtx} → {Claim : Type} →
    (tree : ClaimTree ctx Claim) →
    tree.IsSound sample →
    {Output : Transcript ctx → Type} →
    (prover : Prover ProbComp ctx Output) →
    ∀ {claim : Claim}, ¬ tree.good claim →
      Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
        | Prover.run ctx prover (randomChallenger sample ctx)] ≤ tree.maxPathError
  | .nil, _, .nil good, _, Output, output, claim, hFalse => by
      simpa [Prover.run, ClaimTree.follow, ClaimTree.terminalGood,
        ClaimTree.maxPathError, ClaimTree.good] using hFalse
  | .P_to_V T oi rest, _, .message good NextClaim next advance, hValid, Output,
      ⟨msg, contP⟩, claim, hFalse => by
      rcases hValid with ⟨hStep, hChildren⟩
      let tree : ClaimTree (.P_to_V T oi rest) _ := ClaimTree.message good NextClaim next advance
      let my :
          Prover ProbComp (rest msg) (fun trRest => Output ⟨msg, trRest⟩) →
            ProbComp ((tr : Transcript (.P_to_V T oi rest)) × Output tr) :=
        fun nextProver => do
          let ⟨tr, out⟩ ← Prover.run (rest msg) nextProver (randomChallenger sample (rest msg))
          return ⟨⟨msg, tr⟩, out⟩
      let wrap :
          ((trRest : Transcript (rest msg)) × Output ⟨msg, trRest⟩) →
            ((tr : Transcript (.P_to_V T oi rest)) × Output tr) :=
        fun z => ⟨⟨msg, z.1⟩, z.2⟩
      have hFalse' : ¬ (next msg).good (advance claim msg) := hStep claim hFalse msg
      have hPoint :
          ∀ nextProver : Prover ProbComp (rest msg) (fun trRest => Output ⟨msg, trRest⟩),
            Pr[fun z =>
                tree.terminalGood z.1 (tree.follow z.1 claim)
              | my nextProver] ≤
              (next msg).maxPathError := by
        intro nextProver
        have hMap :
            my nextProver =
              wrap <$>
                Prover.run (rest msg) nextProver (randomChallenger sample (rest msg)) := by
          simp [my, wrap, map_eq_bind_pure_comp]
        calc
          Pr[fun z =>
              tree.terminalGood z.1 (tree.follow z.1 claim)
            | my nextProver]
              =
            Pr[fun z =>
                tree.terminalGood z.1 (tree.follow z.1 claim)
              | wrap <$>
                  Prover.run (rest msg) nextProver (randomChallenger sample (rest msg))] := by
                rw [hMap]
          _ =
            Pr[fun z =>
                (next msg).terminalGood z.1 ((next msg).follow z.1 (advance claim msg))
              | Prover.run (rest msg) nextProver (randomChallenger sample (rest msg))] := by
                rw [probEvent_map (f := wrap)]
                congr 2
          _ ≤ (next msg).maxPathError :=
            IsSound.bound_terminalProb sample (tree := next msg) (hChildren msg) nextProver hFalse'
      have hBind :
          Pr[fun z =>
              tree.terminalGood z.1 (tree.follow z.1 claim)
            | contP >>= my] ≤
            (next msg).maxPathError := by
        exact probEvent_bind_le_const contP my
          (fun z => tree.terminalGood z.1 (tree.follow z.1 claim))
          ((next msg).maxPathError) hPoint
      calc
        Pr[fun z =>
            tree.terminalGood z.1 (tree.follow z.1 claim)
          | Prover.run (.P_to_V T oi rest)
              ((⟨msg, contP⟩ : Prover ProbComp (.P_to_V T oi rest) Output))
              (randomChallenger sample (.P_to_V T oi rest))]
            =
          Pr[fun z =>
              tree.terminalGood z.1 (tree.follow z.1 claim)
            | contP >>= my] := by
            simp [tree, my, Prover.run, randomChallenger]
        _ ≤ (next msg).maxPathError := hBind
        _ ≤ tree.maxPathError := by
            simpa [tree, ClaimTree.maxPathError] using
              (le_iSup (f := fun t : T => (next t).maxPathError) msg)
  | .V_to_P T rest, _, .challenge good error NextClaim next advance, hValid, Output,
      recv, claim, hFalse => by
      classical
      rcases hValid with ⟨hFlip, hChildren⟩
      let tree : ClaimTree (.V_to_P T rest) _ :=
        ClaimTree.challenge good error NextClaim next advance
      let cond : T → Prop := fun challenge => (next challenge).good (advance claim challenge)
      let supErr : ℝ≥0∞ := ⨆ challenge : T, (next challenge).maxPathError
      let my : T → ProbComp ((tr : Transcript (.V_to_P T rest)) × Output tr) :=
        fun challenge => do
          let nextProver ← recv challenge
          let ⟨tr, out⟩ ← Prover.run (rest challenge) nextProver
            (randomChallenger sample (rest challenge))
          return ⟨⟨challenge, tr⟩, out⟩
      have hPoint :
          ∀ challenge,
            Pr[fun z =>
                tree.terminalGood z.1 (tree.follow z.1 claim)
              | my challenge] ≤
              if cond challenge then 1 else supErr := by
        intro challenge
        by_cases hcond : cond challenge
        · have : Pr[fun z =>
              tree.terminalGood z.1 (tree.follow z.1 claim)
              | my challenge] ≤ 1 := probEvent_le_one
          rw [if_pos hcond]
          exact this
        · let myNext :
              Prover ProbComp (rest challenge) (fun trRest => Output ⟨challenge, trRest⟩) →
                ProbComp ((tr : Transcript (.V_to_P T rest)) × Output tr) :=
            fun nextProver => do
              let ⟨tr, out⟩ ← Prover.run (rest challenge) nextProver
                (randomChallenger sample (rest challenge))
              return ⟨⟨challenge, tr⟩, out⟩
          let wrap :
              ((trRest : Transcript (rest challenge)) × Output ⟨challenge, trRest⟩) →
                ((tr : Transcript (.V_to_P T rest)) × Output tr) :=
            fun z => ⟨⟨challenge, z.1⟩, z.2⟩
          have hPointNext :
              ∀ nextProver :
                  Prover ProbComp (rest challenge) (fun trRest => Output ⟨challenge, trRest⟩),
                Pr[fun z =>
                    tree.terminalGood z.1 (tree.follow z.1 claim)
                  | myNext nextProver] ≤
                  (next challenge).maxPathError := by
            intro nextProver
            have hMap :
                myNext nextProver =
                  wrap <$>
                    Prover.run (rest challenge) nextProver
                      (randomChallenger sample (rest challenge)) := by
              simp [myNext, wrap, map_eq_bind_pure_comp]
            calc
              Pr[fun z =>
                  tree.terminalGood z.1 (tree.follow z.1 claim)
                | myNext nextProver]
                  =
                Pr[fun z =>
                    tree.terminalGood z.1 (tree.follow z.1 claim)
                  | wrap <$>
                      Prover.run (rest challenge) nextProver
                        (randomChallenger sample (rest challenge))] := by
                    rw [hMap]
              _ =
                Pr[fun z =>
                    (next challenge).terminalGood z.1
                      ((next challenge).follow z.1 (advance claim challenge))
                  | Prover.run (rest challenge) nextProver
                      (randomChallenger sample (rest challenge))] := by
                    rw [probEvent_map (f := wrap)]
                    congr 2
              _ ≤ (next challenge).maxPathError :=
                IsSound.bound_terminalProb sample (tree := next challenge)
                  (hChildren challenge) nextProver hcond
          have hBindConst :
              Pr[fun z =>
                  tree.terminalGood z.1 (tree.follow z.1 claim)
                | recv challenge >>= myNext] ≤
                (next challenge).maxPathError := by
            exact probEvent_bind_le_const (recv challenge) myNext
              (fun z => tree.terminalGood z.1 (tree.follow z.1 claim))
              ((next challenge).maxPathError) hPointNext
          have hSup : (next challenge).maxPathError ≤ supErr :=
            le_iSup (f := fun t => (next t).maxPathError) challenge
          exact le_trans (by simpa [my, myNext] using hBindConst)
            (by simpa [cond, hcond] using hSup)
      have hBind :
          Pr[fun z =>
              tree.terminalGood z.1 (tree.follow z.1 claim)
            | sample T >>= my] ≤
            Pr[cond | sample T] + supErr := by
        exact probEvent_bind_le_of_cond (sample T) my
          (fun z => tree.terminalGood z.1 (tree.follow z.1 claim))
          cond supErr hPoint
      calc
        Pr[fun z =>
            tree.terminalGood z.1 (tree.follow z.1 claim)
          | Prover.run (.V_to_P T rest) recv
              (randomChallenger sample (.V_to_P T rest))]
            =
          Pr[fun z =>
              tree.terminalGood z.1 (tree.follow z.1 claim)
            | sample T >>= my] := by
            simp [tree, my, Prover.run, randomChallenger]
        _ ≤ Pr[cond | sample T] + supErr := hBind
        _ ≤ error + supErr := by
            simpa [cond, add_comm] using add_le_add_right (hFlip claim hFalse) supErr
        _ = tree.maxPathError := by
            simp [tree, supErr, ClaimTree.maxPathError]

end ClaimTree

namespace Verifier

/-- Deterministic verifier soundness for telescope protocols. The protocol context,
semantic claim, verifier output, and accepted outputs may all depend on the input
statement. The probability is only over the adversarial prover's randomness and the
interactive challenge sampler. -/
def soundness
    {Statement : Type}
    (sample : (T : Type) → ProbComp T)
    (Input : Set Statement)
    (Context : Statement → ProtocolCtx)
    (Output : (statement : Statement) → Transcript (Context statement) → Type)
    (Accepts : (statement : Statement) →
      (tr : Transcript (Context statement)) → Set (Output statement tr))
    (verifier : (statement : Statement) →
      (tr : Transcript (Context statement)) → OptionT Id (Output statement tr))
    (error : Statement → ℝ≥0∞) : Prop :=
  ∀ {AdversaryOutput : (statement : Statement) → Transcript (Context statement) → Type},
  ∀ prover : (statement : Statement) →
      Prover ProbComp (Context statement) (AdversaryOutput statement),
  ∀ statement ∉ Input,
    Pr[fun z => ∃ s ∈ Accepts statement z.1, (verifier statement z.1).run = some s
      | Prover.run (Context statement) (prover statement)
          (randomChallenger sample (Context statement))] ≤ error statement

/-- Bridge a pointwise family of sound claim trees to statement-indexed verifier
soundness. -/
theorem soundness_of_isSound
    {Statement : Type}
    (sample : (T : Type) → ProbComp T)
    (Input : Set Statement)
    (Context : Statement → ProtocolCtx)
    (Claim : Statement → Type)
    (tree : (statement : Statement) → ClaimTree (Context statement) (Claim statement))
    (root : (statement : Statement) → Claim statement)
    (hValid : ∀ statement, (tree statement).IsSound sample)
    (Output : (statement : Statement) → Transcript (Context statement) → Type)
    (Accepts : (statement : Statement) →
      (tr : Transcript (Context statement)) → Set (Output statement tr))
    (verifier : (statement : Statement) →
      (tr : Transcript (Context statement)) → OptionT Id (Output statement tr))
    (hStart :
      ∀ statement, statement ∉ Input → ¬ (tree statement).good (root statement))
    (hAccept :
      ∀ statement tr s,
        (verifier statement tr).run = some s →
        s ∈ Accepts statement tr →
        (tree statement).terminalGood tr ((tree statement).follow tr (root statement))) :
    soundness sample Input Context Output Accepts verifier
      (fun statement => (tree statement).maxPathError) := by
  intro AdversaryOutput prover statement hNotIn
  have hTerminal :
      Pr[fun z => (tree statement).terminalGood z.1
            ((tree statement).follow z.1 (root statement))
        | Prover.run (Context statement) (prover statement)
            (randomChallenger sample (Context statement))] ≤
        (tree statement).maxPathError :=
    ClaimTree.IsSound.bound_terminalProb sample (tree := tree statement)
      (hValid statement) (prover statement) (hStart statement hNotIn)
  have hMono :
      Pr[fun z => ∃ s ∈ Accepts statement z.1, (verifier statement z.1).run = some s
          | Prover.run (Context statement) (prover statement)
              (randomChallenger sample (Context statement))]
        ≤
      Pr[fun z => (tree statement).terminalGood z.1
            ((tree statement).follow z.1 (root statement))
          | Prover.run (Context statement) (prover statement)
              (randomChallenger sample (Context statement))] := by
    refine probEvent_mono ?_
    intro z _ hAcc
    rcases hAcc with ⟨s, hsAccepts, hVer⟩
    exact hAccept statement z.1 s hVer hsAccepts
  exact le_trans hMono hTerminal

end Verifier

end ProtocolCtx
