import ArkLib.Refactor.Telescope.Security.Defs

/-!
# Telescope Soundness Composition

Composition theorems for telescope-native claim trees.

This layer is built around `ClaimTree.comp`, the typed sequential composition operator
from `Telescope/Basic`. The main results are:

- `ClaimTree.IsSound.comp`: structural soundness is closed under arbitrary staged
  composition.
- `ClaimTree.bound_terminalProb_comp`: the composed terminal-good event is bounded by
  the first-stage error plus the worst second-stage error.
- `Verifier.soundness_of_comp_isSound`: statement-indexed verifier soundness for a
  composed protocol follows by composing claim trees and then applying
  `Verifier.soundness_of_isSound`.
-/

noncomputable section

open scoped ENNReal

namespace ProtocolCtx

namespace ClaimTree

/-- Structural soundness is closed under arbitrary staged composition. -/
theorem IsSound.comp
    (sample : (T : Type) → ProbComp T) :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {Claim₁ : Type} → {Claim₂ : (tr₁ : Transcript ctx₁) → Type} →
    (tree₁ : ClaimTree ctx₁ Claim₁) →
    (tree₂ : (tr₁ : Transcript ctx₁) → ClaimTree (ctx₂ tr₁) (Claim₂ tr₁)) →
    (lift : (tr₁ : Transcript ctx₁) → tree₁.Terminal tr₁ → Claim₂ tr₁) →
    (∀ tr₁ terminalClaim,
      ¬ tree₁.terminalGood tr₁ terminalClaim →
      ¬ (tree₂ tr₁).good (lift tr₁ terminalClaim)) →
    tree₁.IsSound sample →
    (∀ tr₁, (tree₂ tr₁).IsSound sample) →
    (ClaimTree.comp ctx₁ ctx₂ tree₁ tree₂ lift).IsSound sample
  | .nil, _, Claim₁, _, .nil _, tree₂, lift, _, _, h₂ => by
      simpa [ClaimTree.comp] using
        pullback_isSound (tree := tree₂ PUnit.unit) sample (h₂ PUnit.unit)
          (Root := Claim₁) (lift := fun claim => lift PUnit.unit claim)
  | .P_to_V _ _ rest, ctx₂, _, _, .message _ _ next advance, tree₂, lift, hLift, h₁, h₂ => by
      rcases h₁ with ⟨hStep, hChildren⟩
      refine ⟨?_, ?_⟩
      · intro claim hBad msg
        exact ClaimTree.comp_not_good_of_not_good
          (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩)
          (next msg) (fun trRest => tree₂ ⟨msg, trRest⟩)
          (fun trRest => lift ⟨msg, trRest⟩)
          (fun trRest terminalClaim => hLift ⟨msg, trRest⟩ terminalClaim)
          (advance claim msg) (hStep claim hBad msg)
      · intro msg
        exact IsSound.comp sample (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩)
          (next msg) (fun trRest => tree₂ ⟨msg, trRest⟩)
          (fun trRest => lift ⟨msg, trRest⟩)
          (fun trRest terminalClaim => hLift ⟨msg, trRest⟩ terminalClaim)
          (hChildren msg) (fun trRest => h₂ ⟨msg, trRest⟩)
  | .V_to_P T rest, ctx₂, _, _, .challenge _ error _ next advance, tree₂, lift, hLift, h₁, h₂ => by
      classical
      rcases h₁ with ⟨hStep, hChildren⟩
      refine ⟨?_, ?_⟩
      · intro claim hBad
        refine le_trans ?_ (hStep claim hBad)
        refine probEvent_mono ?_
        intro challenge _ hGood
        by_contra hBadNext
        exact ClaimTree.comp_not_good_of_not_good
          (rest challenge) (fun trRest => ctx₂ ⟨challenge, trRest⟩)
          (next challenge) (fun trRest => tree₂ ⟨challenge, trRest⟩)
          (fun trRest => lift ⟨challenge, trRest⟩)
          (fun trRest terminalClaim => hLift ⟨challenge, trRest⟩ terminalClaim)
          (advance claim challenge) hBadNext hGood
      · intro challenge
        exact IsSound.comp sample (rest challenge) (fun trRest => ctx₂ ⟨challenge, trRest⟩)
          (next challenge) (fun trRest => tree₂ ⟨challenge, trRest⟩)
          (fun trRest => lift ⟨challenge, trRest⟩)
          (fun trRest terminalClaim => hLift ⟨challenge, trRest⟩ terminalClaim)
          (hChildren challenge) (fun trRest => h₂ ⟨challenge, trRest⟩)

/-- A direct terminal-probability bound for an arbitrary staged composition. -/
theorem bound_terminalProb_comp
    (sample : (T : Type) → ProbComp T)
    (ctx₁ : ProtocolCtx) (ctx₂ : Transcript ctx₁ → ProtocolCtx)
    {Claim₁ : Type} {Claim₂ : (tr₁ : Transcript ctx₁) → Type}
    (tree₁ : ClaimTree ctx₁ Claim₁)
    (tree₂ : (tr₁ : Transcript ctx₁) → ClaimTree (ctx₂ tr₁) (Claim₂ tr₁))
    (lift : (tr₁ : Transcript ctx₁) → tree₁.Terminal tr₁ → Claim₂ tr₁)
    (hSound₁ : tree₁.IsSound sample)
    (hSound₂ : ∀ tr₁, (tree₂ tr₁).IsSound sample)
    (hLift : ∀ tr₁ terminalClaim,
      ¬ tree₁.terminalGood tr₁ terminalClaim →
      ¬ (tree₂ tr₁).good (lift tr₁ terminalClaim))
    {Output : Transcript (ctx₁.append ctx₂) → Type}
    (prover : Prover ProbComp (ctx₁.append ctx₂) Output)
    {claim : Claim₁} (hBad : ¬ tree₁.good claim) :
    Pr[fun z =>
        (ClaimTree.comp ctx₁ ctx₂ tree₁ tree₂ lift).terminalGood z.1
          ((ClaimTree.comp ctx₁ ctx₂ tree₁ tree₂ lift).follow z.1 claim)
      | Prover.run (ctx₁.append ctx₂) prover
          (randomChallenger sample (ctx₁.append ctx₂))] ≤
      tree₁.maxPathError + ⨆ tr₁, (tree₂ tr₁).maxPathError := by
  let tree := ClaimTree.comp ctx₁ ctx₂ tree₁ tree₂ lift
  have hSound : tree.IsSound sample := by
    simpa [tree] using
      IsSound.comp sample ctx₁ ctx₂ tree₁ tree₂ lift hLift hSound₁ hSound₂
  have hBadTree : ¬ tree.good claim := by
    simpa [tree] using
      ClaimTree.comp_not_good_of_not_good ctx₁ ctx₂ tree₁ tree₂ lift hLift claim hBad
  calc
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | Prover.run (ctx₁.append ctx₂) prover
          (randomChallenger sample (ctx₁.append ctx₂))] ≤ tree.maxPathError := by
        exact IsSound.bound_terminalProb sample (tree := tree) hSound prover hBadTree
    _ ≤ tree₁.maxPathError + ⨆ tr₁, (tree₂ tr₁).maxPathError := by
        simpa [tree] using ClaimTree.maxPathError_comp ctx₁ ctx₂ tree₁ tree₂ lift

end ClaimTree

namespace Verifier

/-- Soundness is monotone in the error budget. -/
theorem soundness_mono
    {Statement : Type}
    {sample : (T : Type) → ProbComp T}
    {Input : Set Statement}
    {Context : Statement → ProtocolCtx}
    {Output : (statement : Statement) → Transcript (Context statement) → Type}
    {Accepts : (statement : Statement) →
      (tr : Transcript (Context statement)) → Set (Output statement tr)}
    {verifier : (statement : Statement) →
      (tr : Transcript (Context statement)) → OptionT Id (Output statement tr)}
    {error error' : Statement → ℝ≥0∞}
    (hSound : soundness sample Input Context Output Accepts verifier error)
    (hLe : ∀ statement, error statement ≤ error' statement) :
    soundness sample Input Context Output Accepts verifier error' := by
  intro AdversaryOutput prover statement hNotIn
  exact le_trans (hSound prover statement hNotIn) (hLe statement)

/-- Statement-indexed verifier soundness for an arbitrarily staged claim-tree
composition. -/
theorem soundness_of_comp_isSound
    {Statement : Type}
    (sample : (T : Type) → ProbComp T)
    (Input : Set Statement)
    (Context₁ : Statement → ProtocolCtx)
    (Context₂ : (statement : Statement) → Transcript (Context₁ statement) → ProtocolCtx)
    (Claim₁ : Statement → Type)
    (Claim₂ : (statement : Statement) → (tr₁ : Transcript (Context₁ statement)) → Type)
    (tree₁ : (statement : Statement) → ClaimTree (Context₁ statement) (Claim₁ statement))
    (tree₂ : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) →
      ClaimTree (Context₂ statement tr₁) (Claim₂ statement tr₁))
    (lift : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) →
      (tree₁ statement).Terminal tr₁ → Claim₂ statement tr₁)
    (root : (statement : Statement) → Claim₁ statement)
    (hSound₁ : ∀ statement, (tree₁ statement).IsSound sample)
    (hSound₂ : ∀ statement tr₁, (tree₂ statement tr₁).IsSound sample)
    (hLift : ∀ statement tr₁ terminalClaim,
      ¬ (tree₁ statement).terminalGood tr₁ terminalClaim →
      ¬ (tree₂ statement tr₁).good (lift statement tr₁ terminalClaim))
    (Output : (statement : Statement) →
      Transcript ((Context₁ statement).append (Context₂ statement)) → Type)
    (Accepts : (statement : Statement) →
      (tr : Transcript ((Context₁ statement).append (Context₂ statement))) →
      Set (Output statement tr))
    (verifier : (statement : Statement) →
      (tr : Transcript ((Context₁ statement).append (Context₂ statement))) →
      OptionT Id (Output statement tr))
    (hStart : ∀ statement, statement ∉ Input → ¬ (tree₁ statement).good (root statement))
    (hAccept : ∀ statement tr s,
      (verifier statement tr).run = some s →
      s ∈ Accepts statement tr →
      (ClaimTree.comp (Context₁ statement) (Context₂ statement)
        (tree₁ statement) (tree₂ statement) (lift statement)).terminalGood tr
          ((ClaimTree.comp (Context₁ statement) (Context₂ statement)
            (tree₁ statement) (tree₂ statement) (lift statement)).follow tr
              (root statement))) :
    soundness sample Input
      (fun statement => (Context₁ statement).append (Context₂ statement))
      Output Accepts verifier
      (fun statement =>
        (tree₁ statement).maxPathError + ⨆ tr₁, (tree₂ statement tr₁).maxPathError) := by
  let compTree := fun statement =>
    ClaimTree.comp (Context₁ statement) (Context₂ statement)
      (tree₁ statement) (tree₂ statement) (lift statement)
  have hCompSound : ∀ statement, (compTree statement).IsSound sample := by
    intro statement
    exact ClaimTree.IsSound.comp sample
      (Context₁ statement) (Context₂ statement)
      (tree₁ statement) (tree₂ statement) (lift statement)
      (fun tr₁ terminalClaim => hLift statement tr₁ terminalClaim)
      (hSound₁ statement) (fun tr₁ => hSound₂ statement tr₁)
  have hCompStart :
      ∀ statement, statement ∉ Input → ¬ (compTree statement).good (root statement) := by
    intro statement hNotIn
    exact ClaimTree.comp_not_good_of_not_good
      (Context₁ statement) (Context₂ statement)
      (tree₁ statement) (tree₂ statement) (lift statement)
      (fun tr₁ terminalClaim => hLift statement tr₁ terminalClaim)
      (root statement) (hStart statement hNotIn)
  have hBase :
      soundness sample Input
        (fun statement => (Context₁ statement).append (Context₂ statement))
        Output Accepts verifier
        (fun statement => (compTree statement).maxPathError) := by
    exact soundness_of_isSound sample Input
      (fun statement => (Context₁ statement).append (Context₂ statement))
      Claim₁ compTree root hCompSound Output Accepts verifier hCompStart
      (fun statement tr s hRun hMem => by
        simpa [compTree] using hAccept statement tr s hRun hMem)
  intro AdversaryOutput prover statement hNotIn
  refine le_trans (hBase (AdversaryOutput := AdversaryOutput) prover statement hNotIn) ?_
  simpa [compTree] using
    ClaimTree.maxPathError_comp
      (Context₁ statement) (Context₂ statement)
      (tree₁ statement) (tree₂ statement) (lift statement)

end Verifier

end ProtocolCtx
