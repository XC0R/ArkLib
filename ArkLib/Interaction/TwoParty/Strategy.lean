/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Basic.Strategy
import ArkLib.Interaction.Basic.Syntax
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

private def strategySyntax (m : Type u → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) where
  Node _ (X : Type u) (role : Role) (Cont : X → Type u) := role.Action m X Cont

private def counterpartFamilySyntax
    (Receiver : (X : Type u) → (X → Type u) → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) where
  Node _ (X : Type u) (role : Role) (Cont : X → Type u) :=
    match role with
    | .sender => (x : X) → Cont x
    | .receiver => Receiver X Cont

private def roleMonadContext :=
  Node.Context.extend (fun _ => Role) (fun (_ : Type u) (_ : Role) => BundledMonad.{u, u})

private def strategyMonadicSyntax :
    SyntaxOver.{u, 0, u, u + 1} PUnit roleMonadContext where
  Node _ (X : Type u) γ (Cont : X → Type u) :=
    match γ with
    | ⟨role, bm⟩ => role.Action bm.M X Cont

private def counterpartMonadicSyntax :
    SyntaxOver.{u, 0, u, u + 1} PUnit roleMonadContext where
  Node _ (X : Type u) γ (Cont : X → Type u) :=
    match γ with
    | ⟨.sender, bm⟩ => (x : X) → bm.M (Cont x)
    | ⟨.receiver, bm⟩ => bm.M ((x : X) × Cont x)

private def monadDecorationOver :
    (spec : Spec) → (roles : RoleDecoration spec) → (md : MonadDecoration spec) →
    Decoration.Over (fun _ _ => BundledMonad) spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨_, rRest⟩, ⟨bm, mRest⟩ =>
      ⟨bm, fun x => monadDecorationOver (rest x) (rRest x) (mRest x)⟩

private def packedRoleMonads {spec : Spec}
    (roles : RoleDecoration spec) (md : MonadDecoration spec) :
    Decoration roleMonadContext spec :=
  Decoration.ofOver (fun _ _ => BundledMonad) spec roles (monadDecorationOver spec roles md)

/-- Focal strategy: `Role.Action` at each decorated node (choose vs. respond). -/
abbrev Strategy.withRoles (m : Type u → Type u)
    (spec : Spec) (roles : RoleDecoration spec) (Output : Transcript spec → Type u) :=
  SyntaxOver.Family (strategySyntax m) PUnit.unit spec roles Output

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
def CounterpartFamily.mapOutput
    (Receiver : (X : Type u) → (X → Type u) → Type u)
    (mapReceiver :
      {X : Type u} → {A B : X → Type u} →
      (∀ x, A x → B x) → Receiver X A → Receiver X B) :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) →
    CounterpartFamily Receiver spec roles A →
    CounterpartFamily Receiver spec roles B
  | .done, _, _, _, f, a => f ⟨⟩ a
  | .node _ _, ⟨.sender, _⟩, _, _, f, observe =>
      fun x => mapOutput Receiver mapReceiver (fun p => f ⟨x, p⟩) (observe x)
  | .node _ _, ⟨.receiver, _⟩, _, _, f, receive =>
      mapReceiver
        (fun x => mapOutput Receiver mapReceiver (fun p => f ⟨x, p⟩))
        receive

/-- Counterpart / environment type with transcript-dependent output: dual actions at
each node, producing `Output ⟨⟩` at `.done`. For a no-output counterpart (the old
behavior), use `Counterpart m spec roles (fun _ => PUnit)`. -/
abbrev Counterpart (m : Type u → Type u) :=
  CounterpartFamily (fun X Cont => m ((x : X) × Cont x))

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
    (∀ tr, A tr → B tr) → Counterpart m spec roles A → Counterpart m spec roles B :=
  CounterpartFamily.mapOutput _ Counterpart.mapReceiver

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
      simp [Counterpart.mapOutput, CounterpartFamily.mapOutput]
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
            simp only [F, Counterpart.mapOutput_id]
            rfl
      rw [Counterpart.mapOutput, CounterpartFamily.mapOutput, Counterpart.mapReceiver]
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

/-- Execute `withRoles` against a `Counterpart`, producing transcript, prover output,
and counterpart output. -/
def Strategy.runWithRoles {m : Type u → Type u} [Monad m] :
    (spec : Spec) → (roles : RoleDecoration spec) →
    {OutputP : Transcript spec → Type u} →
    {OutputC : Transcript spec → Type u} →
    Strategy.withRoles m spec roles OutputP →
    Counterpart m spec roles OutputC →
    m ((tr : Transcript spec) × OutputP tr × OutputC tr)
  | .done, _, _, _, output, cOutput => pure ⟨⟨⟩, output, cOutput⟩
  | .node _ rest, ⟨.sender, dRest⟩, _, _, ⟨x, cont⟩, dualFn => do
      let next ← cont
      let ⟨tail, outP, outC⟩ ← runWithRoles (rest x) (dRest x) next (dualFn x)
      return ⟨⟨x, tail⟩, outP, outC⟩
  | .node _ rest, ⟨.receiver, dRest⟩, _, _, respond, dualSample => do
      let ⟨x, dualRest⟩ ← dualSample
      let next ← respond x
      let ⟨tail, outP, outC⟩ ← runWithRoles (rest x) (dRest x) next dualRest
      return ⟨⟨x, tail⟩, outP, outC⟩

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
        simp [Strategy.mapOutputWithRoles, Counterpart.mapOutput, CounterpartFamily.mapOutput,
          Strategy.runWithRoles.eq_1]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        cases strat with
        | mk x cont =>
            simp only [mapOutputWithRoles, Counterpart.mapOutput, CounterpartFamily.mapOutput]
            rw [Strategy.runWithRoles.eq_2, Strategy.runWithRoles.eq_2]
            simp only [bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
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
        simp only [mapOutputWithRoles, Counterpart.mapOutput, CounterpartFamily.mapOutput,
          Counterpart.mapReceiver]
        rw [Strategy.runWithRoles.eq_3, Strategy.runWithRoles.eq_3]
        simp only [bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
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
  SyntaxOver.Family strategyMonadicSyntax PUnit.unit spec (packedRoleMonads roles md) Output

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
  SyntaxOver.Family counterpartMonadicSyntax PUnit.unit spec (packedRoleMonads roles md) Output

/-- Run `withRolesAndMonads` vs. `Counterpart.withMonads`, lifting both sides into
one monad `m`. Returns transcript, prover output, and counterpart output. -/
def Strategy.runWithRolesAndMonads {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad) {α : Type u}, bm.M α → m α) :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (stratDeco : MonadDecoration spec) → (cptDeco : MonadDecoration spec) →
    {OutputP : Transcript spec → Type u} →
    {OutputC : Transcript spec → Type u} →
    Strategy.withRolesAndMonads spec roles stratDeco OutputP →
    Counterpart.withMonads spec roles cptDeco OutputC →
    m ((tr : Transcript spec) × OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, output, cOutput => pure ⟨⟨⟩, output, cOutput⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩, _, _,
      ⟨x, cont⟩, dualFn => do
      let next ← liftStrat bmS cont
      let cptNext ← liftCpt bmC (dualFn x)
      let ⟨tail, outP, outC⟩ ← runWithRolesAndMonads liftStrat liftCpt
        (rest x) (rRest x) (mRestS x) (mRestC x) next cptNext
      return ⟨⟨x, tail⟩, outP, outC⟩
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩, _, _,
      respond, dualSample => do
      let ⟨x, dualRest⟩ ← liftCpt bmC dualSample
      let next ← liftStrat bmS (respond x)
      let ⟨tail, outP, outC⟩ ← runWithRolesAndMonads liftStrat liftCpt
        (rest x) (rRest x) (mRestS x) (mRestC x) next dualRest
      return ⟨⟨x, tail⟩, outP, outC⟩

end Spec
end Interaction
