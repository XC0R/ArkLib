/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Basic.Strategy
import ArkLib.Interaction.Basic.Syntax
import ArkLib.Interaction.Basic.Interaction
import ArkLib.Interaction.Basic.MonadDecoration
import ArkLib.Interaction.TwoParty.Decoration

/-!
# Role-dependent strategies and counterparts

`Spec.Strategy.withRoles` is the prover / focal party: Σ at own nodes, Π at the
other's. `Spec.Counterpart` is the dual type. `withRolesAndMonads` and
`runWithRolesAndMonads` extend this with per-node `BundledMonad` data from
`MonadDecoration`.

This module also contains the public-coin specialization needed for
verifier-side Fiat-Shamir. The ordinary `Counterpart` type is the right shape
for execution, but at receiver nodes it hides the continuation behind an
opaque monadic sample. `Spec.PublicCoinCounterpart` refines that node shape to
expose:

- `sample : m X` — how the next public challenge is chosen
- `next : (x : X) → ...` — how the rest of the verifier depends on that challenge

This makes transcript replay definable without changing the core two-party
interaction model.
-/

universe u

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

private inductive ParticipantBase where
  | focal
  | counterpart

private structure Participant : Type u where
  tag : ParticipantBase
  lift : ULift.{u, 0} PUnit := ⟨PUnit.unit⟩

private def Participant.focal : Participant := ⟨.focal, ⟨PUnit.unit⟩⟩

private def Participant.counterpart : Participant := ⟨.counterpart, ⟨PUnit.unit⟩⟩

private def strategySyntax (m : Type u → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) where
  Node _ (X : Type u) (role : Role) (Cont : X → Type u) := role.Action m X Cont

private def SyntaxOver.forAgent {Agent : Type u} {Γ : Node.Context}
    (syn : SyntaxOver Agent Γ) (agent : Agent) :
    SyntaxOver PUnit Γ where
  Node _ X γ Cont := syn.Node agent X γ Cont

private theorem SyntaxOver.family_forAgent {Agent : Type u} {Γ : Node.Context}
    (syn : SyntaxOver Agent Γ) (agent : Agent) :
    {spec : Spec} → {ctxs : Decoration Γ spec} → {Out : Transcript spec → Type u} →
    SyntaxOver.Family (syn.forAgent agent) PUnit.unit spec ctxs Out =
      SyntaxOver.Family syn agent spec ctxs Out
  | .done, _, _ => rfl
  | .node _ next, ⟨γ, ctxs⟩, Out => by
      simp [SyntaxOver.Family, SyntaxOver.forAgent]
      congr 1
      funext x
      exact SyntaxOver.family_forAgent syn agent (spec := next x) (ctxs := ctxs x)
        (Out := fun tr => Out ⟨x, tr⟩)

private theorem SyntaxOver.family_node {Agent : Type u} {Γ : Node.Context}
    (syn : SyntaxOver Agent Γ)
    {agent : Agent} {X : Type u} {next : X → Spec}
    {γ : Γ X} {ctxs : (x : X) → Decoration Γ (next x)}
    {Out : Transcript (Spec.node X next) → Type u} :
    SyntaxOver.Family syn agent (Spec.node X next) ⟨γ, ctxs⟩ Out =
      syn.Node agent X γ (fun x =>
        SyntaxOver.Family syn agent (next x) (ctxs x) (fun tr => Out ⟨x, tr⟩)) := rfl

private def counterpartFamilySyntax
    (Receiver : (X : Type u) → (X → Type u) → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) where
  Node _ (X : Type u) (role : Role) (Cont : X → Type u) :=
    match role with
    | .sender => (x : X) → Cont x
    | .receiver => Receiver X Cont

private def pairedSyntax (m : Type u → Type u) :
    SyntaxOver.{u, u, u, 0} Participant (fun _ => Role) where
  Node agent X role Cont :=
    match agent.tag, role with
    | .focal, role => role.Action m X Cont
    | .counterpart, .sender => (x : X) → Cont x
    | .counterpart, .receiver => m ((x : X) × Cont x)

private def pairedInteraction (m : Type u → Type u) [Monad m] :
    InteractionOver Participant (fun _ => Role) (pairedSyntax m) m where
  interact := fun {X} {γ : Role} {Cont} {Result} profile k =>
    match γ with
    | .sender => do
        let ⟨x, pContM⟩ := profile Participant.focal
        let pCont ← pContM
        k x (fun
          | ⟨.focal, _⟩ => pCont
          | ⟨.counterpart, _⟩ => profile Participant.counterpart x)
    | .receiver => do
        let ⟨x, cCont⟩ ← profile Participant.counterpart
        let pCont ← profile Participant.focal x
        k x (fun
          | ⟨.focal, _⟩ => pCont
          | ⟨.counterpart, _⟩ => cCont)

private def strategyMonadicSyntax :
    SyntaxOver.{u, 0, u, u + 1} PUnit RoleMonadContext where
  Node _ (X : Type u) γ (Cont : X → Type u) :=
    match γ with
    | ⟨role, bm⟩ => role.Action bm.M X Cont

private def counterpartMonadicSyntax :
    SyntaxOver.{u, 0, u, u + 1} PUnit RoleMonadContext where
  Node _ (X : Type u) γ (Cont : X → Type u) :=
    match γ with
    | ⟨.sender, bm⟩ => (x : X) → bm.M (Cont x)
    | ⟨.receiver, bm⟩ => bm.M ((x : X) × Cont x)

private def pairedMonadicSyntax :
    SyntaxOver.{u, u, u, u + 1} Participant RolePairedMonadContext where
  Node agent X γ Cont :=
    match agent.tag, γ with
    | .focal, ⟨role, ⟨bmP, _⟩⟩ => role.Action bmP.M X Cont
    | .counterpart, ⟨.sender, ⟨_, bmC⟩⟩ => (x : X) → bmC.M (Cont x)
    | .counterpart, ⟨.receiver, ⟨_, bmC⟩⟩ => bmC.M ((x : X) × Cont x)


/-- Focal strategy: `Role.Action` at each decorated node (choose vs. respond). -/
abbrev Strategy.withRoles (m : Type u → Type u)
    (spec : Spec) (roles : RoleDecoration spec) (Output : Transcript spec → Type u) :=
  SyntaxOver.Family (pairedSyntax m) Participant.focal spec roles Output

/-- Non-dependent-output variant of `withRoles`. -/
abbrev Strategy.withRoles' (m : Type u → Type u) (spec : Spec)
    (roles : RoleDecoration spec) (α : Type u) :=
  Strategy.withRoles m spec roles (fun _ => α)

/-- A generic counterpart family parameterized by the representation of receiver
nodes.

Sender nodes are always plain observations: the environment learns the sender's
move and continues in the corresponding subtree. Receiver nodes are represented
by the supplied `Receiver` family.

Both ordinary `Counterpart` and replayable `PublicCoinCounterpart` are
specializations of this single recursion. -/
abbrev CounterpartFamily
    (Receiver : (X : Type u) → (X → Type u) → Type u)
    (spec : Spec) (roles : RoleDecoration spec) (Output : Transcript spec → Type u) :=
  SyntaxOver.Family (counterpartFamilySyntax Receiver) PUnit.unit spec roles Output

/-- Functorial output map for a generic counterpart family. The sender-side
observation structure is unchanged; only the continuation outputs are mapped. -/
private def counterpartFamilyShape
    (Receiver : (X : Type u) → (X → Type u) → Type u)
    (mapReceiver :
      {X : Type u} → {A B : X → Type u} →
      (∀ x, A x → B x) → Receiver X A → Receiver X B) :
    ShapeOver PUnit (fun _ => Role) where
  toSyntaxOver := counterpartFamilySyntax Receiver
  map := fun {agent} {X} {γ} {A} {B} f node =>
    match γ with
    | .sender =>
        fun x => f x (node x)
    | .receiver =>
        mapReceiver f node

def CounterpartFamily.mapOutput
    (Receiver : (X : Type u) → (X → Type u) → Type u)
    (mapReceiver :
      {X : Type u} → {A B : X → Type u} →
      (∀ x, A x → B x) → Receiver X A → Receiver X B) :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) →
    CounterpartFamily Receiver spec roles A →
    CounterpartFamily Receiver spec roles B :=
  fun {spec} {roles} {A} {B} f =>
    ShapeOver.mapOutput
      (counterpartFamilyShape Receiver mapReceiver)
      (agent := PUnit.unit) (spec := spec) roles
      (A := A) (B := B) f

/-- Counterpart / environment type with transcript-dependent output: dual actions at
each node, producing `Output ⟨⟩` at `.done`. For a no-output counterpart (the old
behavior), use `Counterpart m spec roles (fun _ => PUnit)`. -/
abbrev Counterpart (m : Type u → Type u)
    (spec : Spec) (roles : RoleDecoration spec) (Output : Transcript spec → Type u) :=
  SyntaxOver.Family (pairedSyntax m) Participant.counterpart spec roles Output

private def Counterpart.mapReceiver {m : Type u → Type u} [Functor m] :
    {X : Type u} → {A B : X → Type u} →
    (∀ x, A x → B x) → m ((x : X) × A x) → m ((x : X) × B x)
  | _, _, _, f, sample => (fun ⟨x, c⟩ => ⟨x, f x c⟩) <$> sample

/-- Functorial output map for role-dependent strategies. -/
def Strategy.mapOutputWithRoles {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) → Strategy.withRoles m spec roles A → Strategy.withRoles m spec roles B
  | .done, _, _, _, f, a => f ⟨⟩ a
  | .node _ _, ⟨.sender, _⟩, _, _, f, ⟨x, cont⟩ =>
      ⟨x, (mapOutputWithRoles (fun p => f ⟨x, p⟩) ·) <$> cont⟩
  | .node _ _, ⟨.receiver, _⟩, _, _, f, respond =>
      fun x => (mapOutputWithRoles (fun p => f ⟨x, p⟩) ·) <$> respond x

/-- Pointwise identity on outputs is the identity on role-dependent strategies. -/
@[simp]
theorem Strategy.mapOutputWithRoles_id {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : Transcript spec → Type u}
    (σ : Strategy.withRoles m spec roles A) :
    Strategy.mapOutputWithRoles (fun _ x => x) σ = σ := by
  match spec, roles with
  | .done, roles =>
      cases roles
      rfl
  | .node _ rest, ⟨.sender, rRest⟩ =>
      rcases σ with ⟨x, cont⟩
      simp only [Strategy.mapOutputWithRoles]
      congr 1
      have hid :
          (mapOutputWithRoles (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) :
              Strategy.withRoles m (rest x) (rRest x) (fun p => A ⟨x, p⟩) →
                Strategy.withRoles m (rest x) (rRest x) (fun p => A ⟨x, p⟩)) =
            id := by
        funext s
        exact @mapOutputWithRoles_id m _ _ (rest x) (rRest x) (fun p => A ⟨x, p⟩) s
      rw [hid]
      exact LawfulFunctor.id_map cont
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      funext x
      have hid :
          (mapOutputWithRoles (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) :
              Strategy.withRoles m (rest x) (rRest x) (fun p => A ⟨x, p⟩) →
                Strategy.withRoles m (rest x) (rRest x) (fun p => A ⟨x, p⟩)) =
            id := by
        funext s
        exact @mapOutputWithRoles_id m _ _ (rest x) (rRest x) (fun p => A ⟨x, p⟩) s
      simp only [Strategy.mapOutputWithRoles, hid]
      exact LawfulFunctor.id_map (σ x)

/-- Functorial output map for counterparts. -/
def Counterpart.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) → Counterpart m spec roles A → Counterpart m spec roles B
  | .done, _, _, _, f, a => f ⟨⟩ a
  | .node _ _, ⟨.sender, _⟩, _, _, f, observe =>
      fun x => mapOutput (fun p => f ⟨x, p⟩) (observe x)
  | .node _ _, ⟨.receiver, _⟩, _, _, f, receive =>
      Counterpart.mapReceiver (fun x => mapOutput (fun p => f ⟨x, p⟩)) receive

/-- A verifier counterpart with replayable public-coin receiver nodes.

An ordinary `Counterpart m` represents a receiver node as an opaque monadic
action returning both the sampled challenge and the continuation. That is the
right shape for execution, but it is too weak for verifier-side Fiat-Shamir:
given a prescribed challenge `x`, there is no way to recover the continuation
for `x` unless that continuation is exposed separately.

`PublicCoinCounterpart` factors each receiver node into:
- `sample : m X` — how the verifier samples the next public challenge
- `next : (x : X) → ...` — how the rest of the verifier depends on that challenge

This is exactly the extra structure needed to replay a prescribed transcript
through the verifier. -/
abbrev PublicCoinCounterpart (m : Type u → Type u) :=
  CounterpartFamily (fun X Cont => m X × ((x : X) → Cont x))

namespace PublicCoinCounterpart

private def mapReceiver {m : Type u → Type u} :
    {X : Type u} → {A B : X → Type u} →
    (∀ x, A x → B x) → (m X × ((x : X) → A x)) → (m X × ((x : X) → B x))
  | _, _, _, f, ⟨sample, next⟩ => ⟨sample, fun x => f x (next x)⟩

/-- Functorial output map for public-coin counterparts. The challenge samplers
are unchanged; only the terminal output carried by continuations is mapped. -/
def mapOutput {m : Type u → Type u} :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) →
    PublicCoinCounterpart m spec roles A →
    PublicCoinCounterpart m spec roles B :=
  CounterpartFamily.mapOutput _ mapReceiver

/-- Forget the public-coin factorization and recover the ordinary executable
counterpart. -/
def toCounterpart {m : Type u → Type u} [Monad m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {Output : Transcript spec → Type u} →
    PublicCoinCounterpart m spec roles Output → Counterpart m spec roles Output
  | .done, _, _, c => c
  | .node _ _, ⟨.sender, _⟩, _, observe =>
      fun x => toCounterpart (observe x)
  | .node _ _, ⟨.receiver, _⟩, _, ⟨sample, next⟩ => do
      let x ← sample
      pure ⟨x, toCounterpart (next x)⟩

/-- Replay a prescribed transcript through a public-coin counterpart. Sender
messages are read from the transcript; receiver samplers are ignored and the
stored continuation family is followed at the recorded challenge. -/
def replay {m : Type u → Type u} :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {Output : Transcript spec → Type u} →
    PublicCoinCounterpart m spec roles Output →
    (tr : Transcript spec) → Output tr
  | .done, _, _, c, _ => c
  | .node _ _, ⟨.sender, _⟩, _, observe, ⟨x, tr⟩ =>
      replay (observe x) tr
  | .node _ _, ⟨.receiver, _⟩, _, ⟨_, next⟩, ⟨x, tr⟩ =>
      replay (next x) tr

end PublicCoinCounterpart

/-- Pointwise identity on outputs is the identity on counterparts. -/
@[simp]
theorem Counterpart.mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : Transcript spec → Type u}
    (c : Counterpart m spec roles A) :
    Counterpart.mapOutput (fun _ x => x) c = c := by
  match spec, roles with
  | .done, roles =>
      cases roles
      simp [Counterpart.mapOutput]
  | .node _ rest, ⟨.sender, rRest⟩ =>
      funext x
      exact @Counterpart.mapOutput_id m _ _ (rest x) (rRest x) (fun p => A ⟨x, p⟩) (c x)
  | .node X rest, ⟨.receiver, rRest⟩ =>
      let F : ((x : X) × Counterpart m (rest x) (rRest x) (fun p => A ⟨x, p⟩)) →
          ((x : X) × Counterpart m (rest x) (rRest x) (fun p => A ⟨x, p⟩)) :=
        fun xc => ⟨xc.1,
          Counterpart.mapOutput
            (fun (p : Transcript (rest xc.1)) (y : A ⟨xc.1, p⟩) => y) xc.2⟩
      have hpair :
          F = id := by
        funext xc
        cases xc with
        | mk x c' =>
            simp only [F]
            rw [Counterpart.mapOutput_id]
            rfl
      rw [Counterpart.mapOutput, Counterpart.mapReceiver]
      change F <$> c = c
      rw [hpair]
      exact LawfulFunctor.id_map c

/-- Lift a deterministic counterpart (`Counterpart Id`) into any monad.

At sender nodes the observational branch structure is unchanged. At receiver
nodes the chosen move and continuation are simply wrapped in `pure`. This is a
generic utility for reusing deterministic environments inside monadic execution
machinery such as `runWithRoles`. -/
def Counterpart.liftId {m : Type u → Type u} [Monad m] :
    {spec : Spec} → {roles : RoleDecoration spec} →
    {Output : Transcript spec → Type u} →
    Counterpart Id spec roles Output → Counterpart m spec roles Output
  | .done, _, _, c => c
  | .node _ _, ⟨.sender, _⟩, _, observe =>
      fun x => liftId (observe x)
  | .node _ _, ⟨.receiver, _⟩, _, ⟨x, c⟩ =>
      pure ⟨x, liftId c⟩

private def Strategy.runWithRolesAux {m : Type u → Type u} [Monad m]
    (spec : Spec) (roles : RoleDecoration spec)
    (OutputP : Transcript spec → Type u)
    (OutputC : Transcript spec → Type u)
    (strat : Strategy.withRoles m spec roles OutputP)
    (cpt : Counterpart m spec roles OutputC) :
    m ((tr : Transcript spec) × OutputP tr × OutputC tr) :=
  match spec, roles with
  | .done, _ => pure ⟨⟨⟩, strat, cpt⟩
  | .node _ rest, ⟨role, rRest⟩ =>
      (pairedInteraction m).interact (γ := role)
        (Cont := fun agent x =>
          match agent.tag with
          | .focal =>
              Strategy.withRoles m (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)
          | .counterpart =>
              Counterpart m (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))
        (fun
          | ⟨.focal, _⟩ => strat
          | ⟨.counterpart, _⟩ => cpt)
        (fun x conts => do
          let ⟨tail, outP, outC⟩ ←
            Strategy.runWithRolesAux
              (rest x) (rRest x)
              (fun tr => OutputP ⟨x, tr⟩)
              (fun tr => OutputC ⟨x, tr⟩)
              (conts Participant.focal)
              (conts Participant.counterpart)
          pure ⟨⟨x, tail⟩, outP, outC⟩)

/-- Execute `withRoles` against a `Counterpart`, producing transcript, prover output,
and counterpart output. -/
def Strategy.runWithRoles {m : Type u → Type u} [Monad m] :
    (spec : Spec) → (roles : RoleDecoration spec) →
    {OutputP : Transcript spec → Type u} →
    {OutputC : Transcript spec → Type u} →
    Strategy.withRoles m spec roles OutputP →
    Counterpart m spec roles OutputC →
    m ((tr : Transcript spec) × OutputP tr × OutputC tr)
  | spec, roles, OutputP, OutputC, strat, cpt =>
      Strategy.runWithRolesAux spec roles OutputP OutputC strat cpt

@[simp]
theorem Strategy.runWithRoles_done {m : Type u → Type u} [Monad m]
    {OutputP OutputC : Transcript Spec.done → Type u}
    (outP : OutputP ⟨⟩) (outC : OutputC ⟨⟩) :
    Strategy.runWithRoles .done PUnit.unit outP outC =
      (pure ⟨⟨⟩, outP, outC⟩ :
        m ((tr : Transcript Spec.done) × OutputP tr × OutputC tr)) := by
  rfl

@[simp]
theorem Strategy.runWithRoles_sender {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : Transcript (Spec.node X rest) → Type u}
    (x : X)
    (cont : m (Strategy.withRoles m (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualFn : (x : X) → Counterpart m (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩)) :
    Strategy.runWithRoles (Spec.node X rest) ⟨.sender, rRest⟩ ⟨x, cont⟩ dualFn = (do
      let next ← cont
      let ⟨tail, outP, outC⟩ ← Strategy.runWithRoles (rest x) (rRest x) next (dualFn x)
      pure ⟨⟨x, tail⟩, outP, outC⟩) := by
  simp [Strategy.runWithRoles, Strategy.runWithRolesAux, pairedInteraction,
    Participant.focal, Participant.counterpart]

@[simp]
theorem Strategy.runWithRoles_receiver {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : Transcript (Spec.node X rest) → Type u}
    (respond : (x : X) → m (Strategy.withRoles m (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualSample :
      m ((x : X) × Counterpart m (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    Strategy.runWithRoles (Spec.node X rest) ⟨.receiver, rRest⟩ respond dualSample = (do
      let ⟨x, dualRest⟩ ← dualSample
      let next ← respond x
      let ⟨tail, outP, outC⟩ ← Strategy.runWithRoles (rest x) (rRest x) next dualRest
      pure ⟨⟨x, tail⟩, outP, outC⟩) := by
  simp [Strategy.runWithRoles, Strategy.runWithRolesAux, pairedInteraction,
    Participant.focal, Participant.counterpart]

/-- Running `runWithRoles` after mapping both participant outputs is the same as
running first and mapping the final triple. -/
theorem Strategy.runWithRoles_mapOutputWithRoles_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputP' OutputC OutputC' : Transcript spec → Type u}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : Strategy.withRoles m spec roles OutputP)
    (cpt : Counterpart m spec roles OutputC) :
    Strategy.runWithRoles spec roles (Strategy.mapOutputWithRoles fP strat)
      (Counterpart.mapOutput fC cpt) =
      (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
        Strategy.runWithRoles spec roles strat cpt := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec)
      {OutputP OutputP' OutputC OutputC' : Transcript spec → Type u}
      (fP : ∀ tr, OutputP tr → OutputP' tr)
      (fC : ∀ tr, OutputC tr → OutputC' tr)
      (strat : Strategy.withRoles m spec roles OutputP)
      (cpt : Counterpart m spec roles OutputC) :
      Strategy.runWithRoles spec roles (Strategy.mapOutputWithRoles fP strat)
        (Counterpart.mapOutput fC cpt) =
        (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
          Strategy.runWithRoles spec roles strat cpt := by
    match spec, roles with
    | .done, roles =>
        cases roles
        simp [Strategy.mapOutputWithRoles, Counterpart.mapOutput, Strategy.runWithRoles_done]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        cases strat with
        | mk x cont =>
            simp only [Strategy.mapOutputWithRoles, Counterpart.mapOutput]
            simp [Strategy.runWithRoles, Strategy.runWithRolesAux, pairedInteraction,
              Participant.focal, Participant.counterpart]
            refine congrArg (fun k => cont >>= k) ?_
            funext next
            let addPrefix :
                ((tr : Transcript (rest x)) × (fun tr => OutputP' ⟨x, tr⟩) tr ×
                  (fun tr => OutputC' ⟨x, tr⟩) tr) →
                ((tr : Transcript (Spec.node _ rest)) × OutputP' tr × OutputC' tr) :=
              fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
            simpa [bind_assoc, addPrefix] using
              congrArg (fun z => addPrefix <$> z)
                (go (rest x) (rRest x) (fun tr => fP ⟨x, tr⟩) (fun tr => fC ⟨x, tr⟩)
                  next (cpt x))
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [Strategy.mapOutputWithRoles, Counterpart.mapOutput,
          Counterpart.mapReceiver]
        simp [Strategy.runWithRoles, Strategy.runWithRolesAux, pairedInteraction,
          Participant.focal, Participant.counterpart]
        refine congrArg (fun k => cpt >>= k) ?_
        funext xc
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Transcript (rest xc.1)) × (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Transcript (Spec.node _ rest)) × OutputP' tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (fun tr => fP ⟨xc.1, tr⟩) (fun tr => fC ⟨xc.1, tr⟩)
              next xc.2)
  exact go spec roles fP fC strat cpt

/-- `withRoles` using the monad attached at each node (from `MonadDecoration`).
See `Counterpart.withMonads` for the dual. -/
abbrev Strategy.withRolesAndMonads
    (spec : Spec.{u}) (roles : RoleDecoration spec) (md : MonadDecoration spec)
    (Output : Transcript spec → Type u) :=
  SyntaxOver.Family strategyMonadicSyntax PUnit.unit spec
    (RoleDecoration.withMonads roles md) Output

/-- Counterpart with per-node monads and transcript-dependent output.

This is the primary type for oracle verifiers: `OracleCounterpart` (in
`Oracle/Core.lean`) is defined as `Counterpart.withMonads` with a
`MonadDecoration` computed from the oracle decoration via `toMonadDecoration`.
At sender nodes the monad is `Id` (pure observation); at receiver nodes it is
`OracleComp` with the accumulated oracle access. All generic
`Counterpart.withMonads` composition combinators (e.g., `withMonads.append`,
`withMonads.stateChainComp`) therefore apply directly to oracle counterparts. -/
abbrev Counterpart.withMonads
    (spec : Spec.{u}) (roles : RoleDecoration spec) (md : MonadDecoration spec)
    (Output : Transcript spec → Type u) :=
  SyntaxOver.Family counterpartMonadicSyntax PUnit.unit spec
    (RoleDecoration.withMonads roles md) Output

private theorem pairedMonadicSyntax_forAgent_focal :
    pairedMonadicSyntax.forAgent Participant.focal =
      strategyMonadicSyntax.comap RolePairedMonadContext.fst := by
  apply congrArg SyntaxOver.mk
  funext _ X γ Cont
  cases γ with
  | mk role bms =>
      cases role <;> rfl

private theorem pairedMonadicSyntax_forAgent_counterpart :
    pairedMonadicSyntax.forAgent Participant.counterpart =
      counterpartMonadicSyntax.comap RolePairedMonadContext.snd := by
  apply congrArg SyntaxOver.mk
  funext _ X γ Cont
  cases γ with
  | mk role bms =>
      cases role <;> rfl

private theorem pairedMonadicSyntax_family_focal :
    {spec : Spec} → {roles : RoleDecoration spec} →
    {stratDeco cptDeco : MonadDecoration spec} →
    {Output : Transcript spec → Type u} →
    SyntaxOver.Family pairedMonadicSyntax Participant.focal spec
      (RoleDecoration.withPairedMonads roles stratDeco cptDeco) Output =
      Strategy.withRolesAndMonads spec roles stratDeco Output
  | spec, roles, stratDeco, cptDeco, Output => by
      rw [← SyntaxOver.family_forAgent pairedMonadicSyntax Participant.focal
        (spec := spec)
        (ctxs := RoleDecoration.withPairedMonads roles stratDeco cptDeco)
        (Out := Output)]
      rw [pairedMonadicSyntax_forAgent_focal]
      rw [SyntaxOver.family_comap strategyMonadicSyntax RolePairedMonadContext.fst
        (agent := PUnit.unit)
        (ctxs := RoleDecoration.withPairedMonads roles stratDeco cptDeco)
        (Out := Output)]
      simpa [Strategy.withRolesAndMonads] using
        (RoleDecoration.withPairedMonads_map_fst
          (spec := spec) (roles := roles)
          (stratDeco := stratDeco) (cptDeco := cptDeco))

private theorem pairedMonadicSyntax_family_counterpart :
    {spec : Spec} → {roles : RoleDecoration spec} →
    {stratDeco cptDeco : MonadDecoration spec} →
    {Output : Transcript spec → Type u} →
    SyntaxOver.Family pairedMonadicSyntax Participant.counterpart spec
      (RoleDecoration.withPairedMonads roles stratDeco cptDeco) Output =
      Counterpart.withMonads spec roles cptDeco Output
  | spec, roles, stratDeco, cptDeco, Output => by
      rw [← SyntaxOver.family_forAgent pairedMonadicSyntax Participant.counterpart
        (spec := spec)
        (ctxs := RoleDecoration.withPairedMonads roles stratDeco cptDeco)
        (Out := Output)]
      rw [pairedMonadicSyntax_forAgent_counterpart]
      rw [SyntaxOver.family_comap counterpartMonadicSyntax RolePairedMonadContext.snd
        (agent := PUnit.unit)
        (ctxs := RoleDecoration.withPairedMonads roles stratDeco cptDeco)
        (Out := Output)]
      simpa [Counterpart.withMonads] using
        (RoleDecoration.withPairedMonads_map_snd
          (spec := spec) (roles := roles)
          (stratDeco := stratDeco) (cptDeco := cptDeco))

private def pairedMonadicProfile {spec : Spec} {roles : RoleDecoration spec}
    {stratDeco cptDeco : MonadDecoration spec}
    {OutputP OutputC : Transcript spec → Type u}
    (strat : Strategy.withRolesAndMonads spec roles stratDeco OutputP)
    (cpt : Counterpart.withMonads spec roles cptDeco OutputC) :
    (agent : Participant) →
      SyntaxOver.Family pairedMonadicSyntax agent spec
        (RoleDecoration.withPairedMonads roles stratDeco cptDeco)
        (match agent.tag with
          | .focal => OutputP
          | .counterpart => OutputC)
  | ⟨.focal, _⟩ => by
      exact cast
        (pairedMonadicSyntax_family_focal (spec := spec) (roles := roles)
          (stratDeco := stratDeco) (cptDeco := cptDeco) (Output := OutputP)).symm
        strat
  | ⟨.counterpart, _⟩ => by
      exact cast
        (pairedMonadicSyntax_family_counterpart (spec := spec) (roles := roles)
          (stratDeco := stratDeco) (cptDeco := cptDeco) (Output := OutputC)).symm
        cpt

/-- Run `withRolesAndMonads` vs. `Counterpart.withMonads`, lifting both sides into
one monad `m`. Returns transcript, prover output, and counterpart output. -/
private def pairedMonadicInteraction {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α) :
    InteractionOver Participant RolePairedMonadContext pairedMonadicSyntax m where
  interact := fun {X} {γ : RolePairedMonadContext X} {Cont} {Result} profile k =>
    match γ with
    | ⟨.sender, ⟨bmP, bmC⟩⟩ => do
        let ⟨x, pContM⟩ := profile Participant.focal
        let pCont ← liftStrat bmP pContM
        let cCont ← liftCpt bmC ((profile Participant.counterpart) x)
        k x (fun
          | ⟨.focal, _⟩ => pCont
          | ⟨.counterpart, _⟩ => cCont)
    | ⟨.receiver, ⟨bmP, bmC⟩⟩ => do
        let ⟨x, cCont⟩ ← liftCpt bmC (profile Participant.counterpart)
        let pCont ← liftStrat bmP ((profile Participant.focal) x)
        k x (fun
          | ⟨.focal, _⟩ => pCont
          | ⟨.counterpart, _⟩ => cCont)

private def Strategy.runWithRolesAndMonadsAux {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α)
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    (stratDeco : MonadDecoration spec) (cptDeco : MonadDecoration spec)
    (OutputP : Transcript spec → Type u)
    (OutputC : Transcript spec → Type u)
    (strat : Strategy.withRolesAndMonads spec roles stratDeco OutputP)
    (cpt : Counterpart.withMonads spec roles cptDeco OutputC) :
    m ((tr : Transcript spec) × OutputP tr × OutputC tr) :=
  match spec, roles, stratDeco, cptDeco with
  | .done, _, _, _ => pure ⟨⟨⟩, strat, cpt⟩
  | .node _ rest, ⟨role, rRest⟩, ⟨bmP, mRestS⟩, ⟨bmC, mRestC⟩ =>
      (pairedMonadicInteraction liftStrat liftCpt).interact
        (γ := ⟨role, (bmP, bmC)⟩)
        (Cont := fun agent x =>
          match agent.tag with
          | .focal =>
              SyntaxOver.Family pairedMonadicSyntax Participant.focal (rest x)
                (RoleDecoration.withPairedMonads (rRest x) (mRestS x) (mRestC x))
                (fun tr => OutputP ⟨x, tr⟩)
          | .counterpart =>
              SyntaxOver.Family pairedMonadicSyntax Participant.counterpart (rest x)
                (RoleDecoration.withPairedMonads (rRest x) (mRestS x) (mRestC x))
                (fun tr => OutputC ⟨x, tr⟩))
        (fun
          | ⟨.focal, _⟩ => by
              have h :
                  pairedMonadicSyntax.Family Participant.focal (.node _ rest)
                    (RoleDecoration.withPairedMonads ⟨role, rRest⟩ ⟨bmP, mRestS⟩ ⟨bmC, mRestC⟩)
                    OutputP :=
                pairedMonadicProfile
                  (spec := .node _ rest) (roles := ⟨role, rRest⟩)
                  (stratDeco := ⟨bmP, mRestS⟩) (cptDeco := ⟨bmC, mRestC⟩)
                  (OutputP := OutputP) (OutputC := OutputC)
                  strat cpt Participant.focal
              have hFamily :
                  pairedMonadicSyntax.Family Participant.focal (.node _ rest)
                    (RoleDecoration.withPairedMonads ⟨role, rRest⟩ ⟨bmP, mRestS⟩ ⟨bmC, mRestC⟩)
                    OutputP =
                  pairedMonadicSyntax.Node Participant.focal _ ⟨role, (bmP, bmC)⟩
                    (fun x =>
                      pairedMonadicSyntax.Family Participant.focal (rest x)
                        (RoleDecoration.withPairedMonads (rRest x) (mRestS x) (mRestC x))
                        (fun tr => OutputP ⟨x, tr⟩)) := by
                simpa [RoleDecoration.withPairedMonads, RoleDecoration.pairedMonadsOver] using
                  (SyntaxOver.family_node pairedMonadicSyntax
                    (agent := Participant.focal)
                    (γ := ⟨role, (bmP, bmC)⟩)
                    (ctxs := fun x => RoleDecoration.withPairedMonads
                      (rRest x) (mRestS x) (mRestC x))
                    (Out := OutputP))
              exact cast hFamily.symm h
          | ⟨.counterpart, _⟩ => by
              have h :
                  pairedMonadicSyntax.Family Participant.counterpart (.node _ rest)
                    (RoleDecoration.withPairedMonads ⟨role, rRest⟩ ⟨bmP, mRestS⟩ ⟨bmC, mRestC⟩)
                    OutputC :=
                pairedMonadicProfile
                  (spec := .node _ rest) (roles := ⟨role, rRest⟩)
                  (stratDeco := ⟨bmP, mRestS⟩) (cptDeco := ⟨bmC, mRestC⟩)
                  (OutputP := OutputP) (OutputC := OutputC)
                  strat cpt Participant.counterpart
              have hFamily :
                  pairedMonadicSyntax.Family Participant.counterpart (.node _ rest)
                    (RoleDecoration.withPairedMonads ⟨role, rRest⟩ ⟨bmP, mRestS⟩ ⟨bmC, mRestC⟩)
                    OutputC =
                  pairedMonadicSyntax.Node Participant.counterpart _ ⟨role, (bmP, bmC)⟩
                    (fun x =>
                      pairedMonadicSyntax.Family Participant.counterpart (rest x)
                        (RoleDecoration.withPairedMonads (rRest x) (mRestS x) (mRestC x))
                        (fun tr => OutputC ⟨x, tr⟩)) := by
                simpa [RoleDecoration.withPairedMonads, RoleDecoration.pairedMonadsOver] using
                  (SyntaxOver.family_node pairedMonadicSyntax
                    (agent := Participant.counterpart)
                    (γ := ⟨role, (bmP, bmC)⟩)
                    (ctxs := fun x => RoleDecoration.withPairedMonads
                      (rRest x) (mRestS x) (mRestC x))
                    (Out := OutputC))
              exact cast hFamily.symm h)
        (fun x conts => do
          let strat' :
              Strategy.withRolesAndMonads (rest x) (rRest x) (mRestS x)
                (fun tr => OutputP ⟨x, tr⟩) :=
            cast
              (pairedMonadicSyntax_family_focal
                (spec := rest x) (roles := rRest x)
                (stratDeco := mRestS x) (cptDeco := mRestC x)
                (Output := fun tr => OutputP ⟨x, tr⟩))
              (conts Participant.focal)
          let cpt' :
              Counterpart.withMonads (rest x) (rRest x) (mRestC x)
                (fun tr => OutputC ⟨x, tr⟩) :=
            cast
              (pairedMonadicSyntax_family_counterpart
                (spec := rest x) (roles := rRest x)
                (stratDeco := mRestS x) (cptDeco := mRestC x)
                (Output := fun tr => OutputC ⟨x, tr⟩))
              (conts Participant.counterpart)
          let ⟨tail, outP, outC⟩ ←
            Strategy.runWithRolesAndMonadsAux
              liftStrat liftCpt
              (rest x) (rRest x) (mRestS x) (mRestC x)
              (fun tr => OutputP ⟨x, tr⟩)
              (fun tr => OutputC ⟨x, tr⟩)
              strat' cpt'
          pure ⟨⟨x, tail⟩, outP, outC⟩)

def Strategy.runWithRolesAndMonads {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α) :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (stratDeco : MonadDecoration spec) → (cptDeco : MonadDecoration spec) →
    {OutputP : Transcript spec → Type u} →
    {OutputC : Transcript spec → Type u} →
    Strategy.withRolesAndMonads spec roles stratDeco OutputP →
    Counterpart.withMonads spec roles cptDeco OutputC →
    m ((tr : Transcript spec) × OutputP tr × OutputC tr)
  | spec, roles, stratDeco, cptDeco, OutputP, OutputC, strat, cpt =>
      Strategy.runWithRolesAndMonadsAux
        liftStrat liftCpt spec roles stratDeco cptDeco OutputP OutputC strat cpt

end Spec
end Interaction
