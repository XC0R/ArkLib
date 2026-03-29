/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Basic.Strategy
import ArkLib.Interaction.Basic.MonadDecoration
import ArkLib.Interaction.TwoParty.Decoration

/-!
# Role-dependent strategies and counterparts

`Spec.Strategy.withRoles` is the prover / focal party: Σ at own nodes, Π at the other's.
`Spec.Counterpart` is the dual type. `withRolesAndMonads` and `runWithRolesAndMonads` extend this
with per-node `BundledMonad` data from `MonadDecoration`.
-/

universe u

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

/-- Focal strategy: `Role.Action` at each decorated node (choose vs. respond). -/
def Strategy.withRoles (m : Type u → Type u) :
    (spec : Spec) → RoleDecoration spec → (Transcript spec → Type u) → Type u
  | .done, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, dRest⟩, Output =>
      role.Action m X (fun x => withRoles m (rest x) (dRest x)
        (fun p => Output ⟨x, p⟩))

/-- Non-dependent-output variant of `withRoles`. -/
abbrev Strategy.withRoles' (m : Type u → Type u) (spec : Spec)
    (roles : RoleDecoration spec) (α : Type u) :=
  Strategy.withRoles m spec roles (fun _ => α)

/-- Counterpart / environment type with transcript-dependent output: dual actions at
each node, producing `Output ⟨⟩` at `.done`. For a no-output counterpart (the old
behavior), use `Counterpart m spec roles (fun _ => PUnit)`. -/
def Counterpart (m : Type u → Type u) :
    (spec : Spec) → RoleDecoration spec → (Transcript spec → Type u) → Type u
  | .done, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, dRest⟩, Output =>
      role.Dual m X (fun x => Counterpart m (rest x) (dRest x)
        (fun p => Output ⟨x, p⟩))

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

/-- Functorial output map for counterparts. -/
def Counterpart.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) → Counterpart m spec roles A → Counterpart m spec roles B
  | .done, _, _, _, f, a => f ⟨⟩ a
  | .node _ _, ⟨.sender, _⟩, _, _, f, observe =>
      fun x => mapOutput (fun p => f ⟨x, p⟩) (observe x)
  | .node _ _, ⟨.receiver, _⟩, _, _, f, sample =>
      (fun ⟨x, c⟩ => ⟨x, mapOutput (fun p => f ⟨x, p⟩) c⟩) <$> sample

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

/-- `withRoles` using the monad attached at each node (from `MonadDecoration`). -/
def Strategy.withRolesAndMonads :
    (spec : Spec.{u}) → RoleDecoration spec → MonadDecoration spec →
    (Transcript spec → Type u) → Type u
  | .done, _, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, rRest⟩, ⟨bm, mRest⟩, Output =>
      role.Action bm.M X
        (fun x => withRolesAndMonads (rest x) (rRest x) (mRest x)
          (fun p => Output ⟨x, p⟩))

/-- Counterpart with per-node monads and transcript-dependent output. -/
def Counterpart.withMonads :
    (spec : Spec.{u}) → RoleDecoration spec → MonadDecoration spec →
    (Transcript spec → Type u) → Type u
  | .done, _, _, Output => Output ⟨⟩
  | .node X rest, ⟨.sender, rRest⟩, ⟨bm, mRest⟩, Output =>
      (x : X) → bm.M (withMonads (rest x) (rRest x) (mRest x)
        (fun p => Output ⟨x, p⟩))
  | .node X rest, ⟨.receiver, rRest⟩, ⟨bm, mRest⟩, Output =>
      bm.M ((x : X) × withMonads (rest x) (rRest x) (mRest x)
        (fun p => Output ⟨x, p⟩))

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
