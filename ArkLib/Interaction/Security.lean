/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
import VCVio

/-!
# Security Definitions for Interactive Reductions

Security notions for interactive protocols built on `Spec` + `RoleDecoration`.
All definitions use a generic monad `m` with `[HasEvalSPMF m]` for probability
semantics, except `randomChallenger` which explicitly uses `ProbComp`.

## Definitions

- **Random challenger**: builds a `Counterpart ProbComp` that samples at
  receiver nodes, using a generic sampler `sample : (T : Type) → ProbComp T`.
- **Completeness**: honest execution on valid input yields valid output with
  high probability.
- **Soundness**: any prover on invalid input has low acceptance probability.
  Uses an `Accepts` set to specify which verifier outputs are considered valid.
- **Knowledge soundness**: like soundness, but an extractor must recover a
  valid input witness from any accepting execution.
- **Claim tree**: recursive soundness witness for round-by-round analysis.
- **Knowledge claim tree**: augmented claim tree with backward extraction for
  round-by-round knowledge soundness.

The claim tree approach (adapted from the `iop-refactor` branch) provides a
structural induction principle for proving soundness of multi-round protocols.
At prover-message (sender) nodes, bad claims must stay bad. At verifier-challenge
(receiver) nodes, a bad claim may flip to good with probability at most `error`.
The main theorem `ClaimTree.IsSound.bound_terminalProb` bounds the probability
of reaching a good terminal claim from a bad root.
-/

set_option autoImplicit false

noncomputable section

open OracleComp
open scoped NNReal ENNReal

namespace Interaction

/-! ## Random challenger -/

/-- Build a `Counterpart` that samples challenges uniformly at receiver nodes.
At sender nodes, the counterpart simply observes. The `sample` function provides
the probability distribution for each type. Returns `PUnit` output at `.done`. -/
def randomChallenger (sample : (T : Type) → ProbComp T) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Spec.Counterpart ProbComp spec roles (fun _ => PUnit)
  | .done, _ => ⟨⟩
  | .node _X rest, ⟨.sender, rRest⟩ =>
      fun x => randomChallenger sample (rest x) (rRest x)
  | .node X rest, ⟨.receiver, rRest⟩ => do
      let x ← sample X
      return ⟨x, randomChallenger sample (rest x) (rRest x)⟩

/-! ## Completeness -/

/-- A reduction satisfies **completeness** with error `ε` if for all valid
inputs, honest execution produces a valid output with probability at least
`1 - ε`. The `relOut` predicate on the full output (prover + verifier)
specifies what counts as a successful execution. -/
def Reduction.completeness
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {StatementIn WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : Reduction m StatementIn WitnessIn Context Roles StatementOut WitnessOut)
    (relIn : Set (StatementIn × WitnessIn))
    (relOut : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      WitnessOut s tr → StatementOut s tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (s : StatementIn) (w : WitnessIn), (s, w) ∈ relIn →
    1 - ε ≤ Pr[fun z => relOut s z.1 z.2.1 z.2.2 | reduction.execute s w]

/-- Perfect completeness: completeness with error `0`. -/
def Reduction.perfectCompleteness
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {StatementIn WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : Reduction m StatementIn WitnessIn Context Roles StatementOut WitnessOut)
    (relIn : Set (StatementIn × WitnessIn))
    (relOut : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      WitnessOut s tr → StatementOut s tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-! ## Soundness -/

/-- A verifier satisfies **soundness** with error `ε` if for all malicious
provers and invalid inputs, the probability that the verifier produces an
accepted output is at most `ε`. The `Accepts` set specifies which verifier
outputs are considered acceptance.

Soundness is a property of the verifier alone — no honest prover appears.
The prover can use any output type and any strategy. -/
def soundness
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {StatementIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (verifier : Verifier m StatementIn Context Roles StatementOut)
    (langIn : Set StatementIn)
    (Accepts : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      Set (StatementOut s tr))
    (ε : ℝ≥0∞) : Prop :=
  ∀ {OutputP : (s : StatementIn) → Spec.Transcript (Context s) → Type},
  ∀ (prover : (s : StatementIn) → Spec.Strategy.withRoles m (Context s) (Roles s) (OutputP s)),
  ∀ (s : StatementIn), s ∉ langIn →
    Pr[fun z => z.2.2 ∈ Accepts s z.1
      | Verifier.run verifier s (prover s)] ≤ ε

/-! ## Knowledge soundness -/

/-- A verifier satisfies **knowledge soundness** with error `ε` if there exists
an extractor that, given the transcript and both outputs, recovers a valid input
witness whenever the output is in `relOut`. The bound says: the probability that
the output is in `relOut` but the extracted input witness is not in `relIn` is
at most `ε`. -/
def knowledgeSoundness
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {StatementIn WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (verifier : Verifier m StatementIn Context Roles StatementOut)
    (relIn : Set (StatementIn × WitnessIn))
    (relOut : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      Set (StatementOut s tr × WitnessOut s tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ (extractor : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      StatementOut s tr → WitnessOut s tr → WitnessIn),
  ∀ (prover : (s : StatementIn) →
    Spec.Strategy.withRoles m (Context s) (Roles s) (WitnessOut s)),
  ∀ (s : StatementIn),
    Pr[fun z =>
      (z.2.2, z.2.1) ∈ relOut s z.1 ∧
      (s, extractor s z.1 z.2.2 z.2.1) ∉ relIn
      | Verifier.run verifier s (prover s)] ≤ ε

/-- Knowledge soundness implies soundness: if an extractor exists, then the
verifier is also sound (ignoring the witness). -/
theorem knowledgeSoundness_implies_soundness
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {StatementIn WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {verifier : Verifier m StatementIn Context Roles StatementOut}
    {relIn : Set (StatementIn × WitnessIn)}
    {relOut : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      Set (StatementOut s tr × WitnessOut s tr)}
    {ε : ℝ≥0∞}
    (hKS : knowledgeSoundness verifier relIn relOut ε)
    (langIn : Set StatementIn)
    (hLang : ∀ s, s ∉ langIn → ∀ w, (s, w) ∉ relIn)
    (Accepts : ∀ (s : StatementIn) (tr : Spec.Transcript (Context s)),
      Set (StatementOut s tr))
    (hAccepts : ∀ s tr sOut,
      sOut ∈ Accepts s tr → ∃ wOut, (sOut, wOut) ∈ relOut s tr) :
    soundness verifier langIn Accepts ε := by
  sorry

/-! ## Claim tree

A `ClaimTree` is a recursive soundness witness defined by structural recursion
on `Spec` + `RoleDecoration`. Each node carries:
- `good : Claim → Prop`, the "good claim" predicate at this point
- At sender nodes: `advance` maps a claim through the prover's message
- At receiver nodes: `error` bounds the probability of a bad claim becoming good

The key invariant (`IsSound`):
- Sender nodes: bad claims MUST stay bad regardless of the prover's message
- Receiver nodes: bad claims may become good with probability at most `error`

This gives a round-by-round soundness analysis. -/

/-- A recursive claim tree annotating each node of a `Spec` with a soundness
witness. The `Claim` type may change at each node via `NextClaim`. -/
inductive ClaimTree : (spec : Spec) → (roles : RoleDecoration spec) →
    (Claim : Type) → Type 1 where
  /-- Base case: leaf with a good predicate. -/
  | done {Claim : Type} (good : Claim → Prop) :
      ClaimTree .done ⟨⟩ Claim
  /-- Sender (prover message) node: the prover's choice cannot improve a bad
  claim. `advance` maps the current claim through the message. -/
  | sender
      {Claim : Type} {X : Type} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (NextClaim : X → Type)
      (next : (x : X) → ClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x) :
      ClaimTree (.node X rest) ⟨.sender, rRest⟩ Claim
  /-- Receiver (verifier challenge) node: a bad claim may flip to good
  with probability at most `error`. -/
  | receiver
      {Claim : Type} {X : Type} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : X → Type)
      (next : (x : X) → ClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x) :
      ClaimTree (.node X rest) ⟨.receiver, rRest⟩ Claim

namespace ClaimTree

/-- The root "good" predicate. -/
def good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim) : Claim → Prop :=
  match tree with
  | .done g => g
  | .sender g _ _ _ => g
  | .receiver g _ _ _ _ => g

/-- The claim type at the terminal (leaf) of a transcript path. -/
def Terminal {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim) (tr : Spec.Transcript spec) : Type :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => Claim
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _, ⟨x, trRest⟩ =>
      (next x).Terminal trRest
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _, ⟨x, trRest⟩ =>
      (next x).Terminal trRest

/-- Transport a root claim along a transcript to the terminal claim. -/
def follow {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (claim : Claim) : tree.Terminal tr :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => claim
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next advance, ⟨x, trRest⟩ =>
      (next x).follow trRest (advance claim x)
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next advance, ⟨x, trRest⟩ =>
      (next x).follow trRest (advance claim x)

/-- The "good" predicate at the terminal claim reached by a transcript. -/
def terminalGood {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr) : Prop :=
  match spec, roles, tree, tr with
  | .done, _, .done g, _ => g terminal
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _, ⟨x, trRest⟩ =>
      (next x).terminalGood trRest terminal
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _, ⟨x, trRest⟩ =>
      (next x).terminalGood trRest terminal

/-- Worst-case cumulative error along any root-to-leaf path. Sender nodes
contribute `0` error; receiver nodes contribute their `error` bound plus the
sup over children. -/
def maxPathError {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim) : ℝ≥0∞ :=
  match tree with
  | .done _ => 0
  | .sender _ _ next _ => ⨆ x, (next x).maxPathError
  | .receiver _ error _ next _ =>
      error + ⨆ x, (next x).maxPathError

/-- Structural soundness of a claim tree. At sender nodes, bad claims must
stay bad for all messages. At receiver nodes, bad claims flip to good with
probability at most `error`. All children must be sound recursively. -/
def IsSound {m : Type → Type} [Monad m] [HasEvalSPMF m]
    (sample : (T : Type) → m T) {spec : Spec}
    {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim) : Prop :=
  match tree with
  | .done _ => True
  | .sender good _ next advance =>
      (∀ claim, ¬ good claim → ∀ x, ¬ (next x).good (advance claim x)) ∧
      (∀ x, (next x).IsSound sample)
  | .receiver good error _ next advance =>
      (∀ claim, ¬ good claim →
        Pr[fun x => (next x).good (advance claim x) | sample _] ≤ error) ∧
      (∀ x, (next x).IsSound sample)

/-- The main round-by-round soundness theorem. If a claim tree is sound and
the root claim is bad, then the probability of reaching a good terminal claim
under any adversarial prover (playing against a random challenger built from
the same sampler) is at most `maxPathError`. -/
theorem IsSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T)
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim)
    (hSound : tree.IsSound sample)
    {OutputP : Spec.Transcript spec → Type}
    (prover : Spec.Strategy.withRoles ProbComp spec roles OutputP)
    {claim : Claim} (hBad : ¬ tree.good claim) :
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | Spec.Strategy.runWithRoles spec roles prover
          (randomChallenger sample spec roles)] ≤ tree.maxPathError := by
  sorry

end ClaimTree

/-! ## Round-by-round soundness via claim trees

Round-by-round soundness existentially quantifies over a `ClaimTree` (the state
function) with per-round error bounds. This matches core ArkLib's
`Verifier.StateFunction`-based definition, where the `ClaimTree` serves as the
structural equivalent:
- `ClaimTree.good` = state function predicate at each round
- `.sender` nodes: bad claims stay bad (= `toFun_next`)
- `.receiver` nodes: per-round error bound (= per-challenge error)
- `ClaimTree.maxPathError` = worst-case total error -/

/-- **Round-by-round soundness**: there exists a claim tree (state function)
such that:
1. The tree is sound per-round (`IsSound`): bad claims stay bad at sender nodes,
   and flip to good with probability at most `error` at receiver nodes.
2. The root claim is bad for all invalid statements.
3. The worst-case cumulative error is at most `ε`.
4. Acceptance implies terminal goodness (bridges the tree to the verifier). -/
def rbrSoundness
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {StatementIn : Type}
    (sample : (T : Type) → ProbComp T)
    (langIn : Set StatementIn)
    (Accepts : (s : StatementIn) → Spec.Transcript pSpec → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∃ (Claim : StatementIn → Type)
    (tree : (s : StatementIn) → ClaimTree pSpec roles (Claim s))
    (root : (s : StatementIn) → Claim s),
  (∀ s, (tree s).IsSound sample) ∧
  (∀ s, s ∉ langIn → ¬ (tree s).good (root s)) ∧
  (∀ s, (tree s).maxPathError ≤ ε) ∧
  (∀ s tr, Accepts s tr →
    (tree s).terminalGood tr ((tree s).follow tr (root s)))

/-- Round-by-round soundness implies overall soundness: if `rbrSoundness` holds
with error `ε`, then for any prover and any invalid statement, the probability
of acceptance is at most `ε`. Uses `bound_terminalProb` internally. -/
theorem soundness_of_rbrSoundness
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {StatementIn : Type}
    {sample : (T : Type) → ProbComp T}
    {langIn : Set StatementIn}
    {Accepts : (s : StatementIn) → Spec.Transcript pSpec → Prop}
    {ε : ℝ≥0∞}
    (h : rbrSoundness (roles := roles) sample langIn Accepts ε) :
    ∀ {OutputP : Spec.Transcript pSpec → Type}
      (prover : Spec.Strategy.withRoles ProbComp pSpec roles OutputP),
    ∀ s, s ∉ langIn →
      Pr[fun z => Accepts s z.1
        | Spec.Strategy.runWithRoles pSpec roles prover
            (randomChallenger sample pSpec roles)] ≤ ε := by
  sorry

/-! ## Knowledge claim tree

A `KnowledgeClaimTree` augments `ClaimTree` with a backward `extractMid`
function at each node. This enables round-by-round *knowledge* soundness:
- At sender nodes, if the child claim is good, extracting back yields a good
  parent claim (backward condition).
- At receiver nodes, a bad parent claim leads to a good child claim with
  probability at most `error` (forward probabilistic bound).
-/

/-- A recursive claim tree with backward extraction, annotating each node of
a `Spec` with a knowledge-soundness witness. -/
inductive KnowledgeClaimTree : (spec : Spec) → (roles : RoleDecoration spec) →
    (Claim : Type) → Type 1 where
  | done {Claim : Type} (good : Claim → Prop) :
      KnowledgeClaimTree .done ⟨⟩ Claim
  | sender
      {Claim : Type} {X : Type} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (NextClaim : X → Type)
      (next : (x : X) → KnowledgeClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x)
      (extractMid : (x : X) → NextClaim x → Claim) :
      KnowledgeClaimTree (.node X rest) ⟨.sender, rRest⟩ Claim
  | receiver
      {Claim : Type} {X : Type} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : X → Type)
      (next : (x : X) → KnowledgeClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x)
      (extractMid : (x : X) → NextClaim x → Claim) :
      KnowledgeClaimTree (.node X rest) ⟨.receiver, rRest⟩ Claim

namespace KnowledgeClaimTree

/-- The root "good" predicate. -/
def good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim) : Claim → Prop :=
  match tree with
  | .done g => g
  | .sender g _ _ _ _ => g
  | .receiver g _ _ _ _ _ => g

/-- Forget the extraction data to get a plain `ClaimTree`. -/
def toClaimTree {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim) : ClaimTree spec roles Claim :=
  match tree with
  | .done g => .done g
  | .sender g nc next adv _ =>
      .sender g nc (fun x => (next x).toClaimTree) adv
  | .receiver g err nc next adv _ =>
      .receiver g err nc (fun x => (next x).toClaimTree) adv

/-- The claim type at the terminal of a transcript path (via `toClaimTree`). -/
def Terminal {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim) (tr : Spec.Transcript spec) : Type :=
  tree.toClaimTree.Terminal tr

/-- Transport a root claim along a transcript (via `toClaimTree`). -/
def follow {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (claim : Claim) : tree.Terminal tr :=
  tree.toClaimTree.follow tr claim

/-- The "good" predicate at the terminal claim (via `toClaimTree`). -/
def terminalGood {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr) : Prop :=
  tree.toClaimTree.terminalGood tr terminal

/-- Worst-case cumulative error (via `toClaimTree`). -/
def maxPathError {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim) : ℝ≥0∞ :=
  tree.toClaimTree.maxPathError

/-- Knowledge-soundness condition. At sender nodes: backward — if the child
claim is good, then extracting back gives a good parent claim. At receiver
nodes: forward — a bad parent claim leads to a good child with probability
at most `error`. -/
def IsKnowledgeSound {m : Type → Type} [Monad m] [HasEvalSPMF m]
    (sample : (T : Type) → m T) {spec : Spec}
    {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim) : Prop :=
  match tree with
  | .done _ => True
  | .sender good _ next _advance extractMid =>
      (∀ x (nc : _), (next x).good nc → good (extractMid x nc)) ∧
      (∀ x, (next x).IsKnowledgeSound sample)
  | .receiver good error _ next advance _extractMid =>
      (∀ claim, ¬ good claim →
        Pr[fun x => (next x).good (advance claim x) | sample _] ≤ error) ∧
      (∀ x, (next x).IsKnowledgeSound sample)

/-- A knowledge-sound tree yields a sound `ClaimTree`. The backward sender
condition implies the forward "bad stays bad" condition by contrapositive. -/
theorem isKnowledgeSound_implies_isSound
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {sample : (T : Type) → m T}
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    {tree : KnowledgeClaimTree spec roles Claim}
    (h : tree.IsKnowledgeSound sample) :
    tree.toClaimTree.IsSound sample := by
  sorry

/-- Bound on the terminal probability for knowledge claim trees, via the
underlying `ClaimTree.IsSound.bound_terminalProb`. -/
theorem IsKnowledgeSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T)
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim)
    (hSound : tree.IsKnowledgeSound sample)
    {OutputP : Spec.Transcript spec → Type}
    (prover : Spec.Strategy.withRoles ProbComp spec roles OutputP)
    {claim : Claim} (hBad : ¬ tree.good claim) :
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | Spec.Strategy.runWithRoles spec roles prover
          (randomChallenger sample spec roles)] ≤ tree.maxPathError := by
  sorry

end KnowledgeClaimTree

/-! ## Round-by-round knowledge soundness

Round-by-round knowledge soundness existentially quantifies over a
`KnowledgeClaimTree` with per-round error bounds and boundary conditions
connecting the claim tree to `relIn` and `relOut`. -/

/-- **Round-by-round knowledge soundness**: there exists a knowledge claim tree
such that:
1. The tree satisfies `IsKnowledgeSound` per-round.
2. The worst-case cumulative error is at most `ε s`.
3. Root boundary: good root claim is equivalent to the extracted witness being
   in `relIn`.
4. Terminal boundary: valid output in `relOut` implies terminal goodness. -/
def rbrKnowledgeSoundness
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {StatementIn WitnessIn : Type}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript pSpec → Type}
    (sample : (T : Type) → ProbComp T)
    (relIn : Set (StatementIn × WitnessIn))
    (relOut : ∀ (s : StatementIn) (tr : Spec.Transcript pSpec),
      Set (StatementOut s tr × WitnessOut s tr))
    (ε : StatementIn → ℝ≥0∞) : Prop :=
  ∃ (Claim : StatementIn → Type)
    (tree : (s : StatementIn) → KnowledgeClaimTree pSpec roles (Claim s))
    (root : (s : StatementIn) → Claim s)
    (extract : (s : StatementIn) → Claim s → WitnessIn),
  (∀ s, (tree s).IsKnowledgeSound sample) ∧
  (∀ s, (tree s).maxPathError ≤ ε s) ∧
  (∀ s c, (tree s).good c ↔ (s, extract s c) ∈ relIn) ∧
  (∀ s tr pOut, pOut ∈ relOut s tr →
    (tree s).terminalGood tr ((tree s).follow tr (root s)))

/-- Round-by-round knowledge soundness implies round-by-round soundness. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {StatementIn WitnessIn : Type}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript pSpec → Type}
    {sample : (T : Type) → ProbComp T}
    {relIn : Set (StatementIn × WitnessIn)}
    {relOut : ∀ (s : StatementIn) (tr : Spec.Transcript pSpec),
      Set (StatementOut s tr × WitnessOut s tr)}
    {ε : StatementIn → ℝ≥0∞}
    (h : rbrKnowledgeSoundness (roles := roles) sample relIn relOut ε)
    (langIn : Set StatementIn)
    (hLang : ∀ s, s ∉ langIn → ∀ w, (s, w) ∉ relIn)
    (Accepts : (s : StatementIn) → Spec.Transcript pSpec → Prop)
    (hAccepts : ∀ s tr, Accepts s tr → ∃ pOut, pOut ∈ relOut s tr)
    {εMax : ℝ≥0∞} (hε : ∀ s, ε s ≤ εMax) :
    rbrSoundness (roles := roles) sample langIn Accepts εMax := by
  sorry

/-- Round-by-round knowledge soundness implies plain knowledge soundness
(for a fixed protocol spec). -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {StatementIn WitnessIn : Type}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript pSpec → Type}
    {sample : (T : Type) → ProbComp T}
    {relIn : Set (StatementIn × WitnessIn)}
    {relOut : ∀ (s : StatementIn) (tr : Spec.Transcript pSpec),
      Set (StatementOut s tr × WitnessOut s tr)}
    {ε : StatementIn → ℝ≥0∞}
    (h : rbrKnowledgeSoundness (pSpec := pSpec) (roles := roles)
      sample relIn relOut ε)
    (verifier : Verifier ProbComp StatementIn (fun _ => pSpec) (fun _ => roles) StatementOut)
    {εMax : ℝ≥0∞} (hε : ∀ s, ε s ≤ εMax) :
    knowledgeSoundness verifier relIn relOut εMax := by
  sorry

end Interaction

end
