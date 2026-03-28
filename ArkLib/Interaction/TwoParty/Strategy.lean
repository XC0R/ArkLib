/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

set_option autoImplicit false

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

/-- Counterpart / environment type: dual actions at each node. -/
def Counterpart (m : Type u → Type u) :
    (spec : Spec) → RoleDecoration spec → Type u
  | .done, _ => PUnit
  | .node X rest, ⟨role, dRest⟩ =>
      role.Dual m X (fun x => Counterpart m (rest x) (dRest x))

/-- Execute `withRoles` against a `Counterpart`, producing transcript and output. -/
def Strategy.runWithRoles {m : Type u → Type u} [Monad m] :
    (spec : Spec) → (roles : RoleDecoration spec) →
    {Output : Transcript spec → Type u} →
    Strategy.withRoles m spec roles Output → Counterpart m spec roles →
    m ((tr : Transcript spec) × Output tr)
  | .done, _, _, output, _ => pure ⟨⟨⟩, output⟩
  | .node _ rest, ⟨.sender, dRest⟩, _, ⟨x, cont⟩, dualFn => do
      let next ← cont
      let ⟨tail, out⟩ ← runWithRoles (rest x) (dRest x) next (dualFn x)
      return ⟨⟨x, tail⟩, out⟩
  | .node _ rest, ⟨.receiver, dRest⟩, _, respond, dualSample => do
      let ⟨x, dualRest⟩ ← dualSample
      let next ← respond x
      let ⟨tail, out⟩ ← runWithRoles (rest x) (dRest x) next dualRest
      return ⟨⟨x, tail⟩, out⟩

/-- `withRoles` using the monad attached at each node (from `MonadDecoration`). -/
def Strategy.withRolesAndMonads :
    (spec : Spec.{u}) → RoleDecoration spec → MonadDecoration spec →
    (Transcript spec → Type u) → Type u
  | .done, _, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, rRest⟩, ⟨bm, mRest⟩, Output =>
      role.Action bm.M X
        (fun x => withRolesAndMonads (rest x) (rRest x) (mRest x)
          (fun p => Output ⟨x, p⟩))

/-- Counterpart where each node uses its bundled monad (both roles). -/
def Counterpart.withMonads :
    (spec : Spec.{u}) → RoleDecoration spec → MonadDecoration spec → Type u
  | .done, _, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩, ⟨bm, mRest⟩ =>
      (x : X) → bm.M (withMonads (rest x) (rRest x) (mRest x))
  | .node X rest, ⟨.receiver, rRest⟩, ⟨bm, mRest⟩ =>
      bm.M ((x : X) × withMonads (rest x) (rRest x) (mRest x))

/-- Run `withRolesAndMonads` vs. `Counterpart.withMonads`, lifting both sides into one monad `m`. -/
def Strategy.runWithRolesAndMonads {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad) {α : Type u}, bm.M α → m α) :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (stratDeco : MonadDecoration spec) → (cptDeco : MonadDecoration spec) →
    {Output : Transcript spec → Type u} →
    Strategy.withRolesAndMonads spec roles stratDeco Output →
    Counterpart.withMonads spec roles cptDeco →
    m ((tr : Transcript spec) × Output tr)
  | .done, _, _, _, _, output, _ => pure ⟨⟨⟩, output⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩, _,
      ⟨x, cont⟩, dualFn => do
      let next ← liftStrat bmS cont
      let cptNext ← liftCpt bmC (dualFn x)
      let ⟨tail, out⟩ ← runWithRolesAndMonads liftStrat liftCpt
        (rest x) (rRest x) (mRestS x) (mRestC x) next cptNext
      return ⟨⟨x, tail⟩, out⟩
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩, _,
      respond, dualSample => do
      let ⟨x, dualRest⟩ ← liftCpt bmC dualSample
      let next ← liftStrat bmS (respond x)
      let ⟨tail, out⟩ ← runWithRolesAndMonads liftStrat liftCpt
        (rest x) (rRest x) (mRestS x) (mRestC x) next dualRest
      return ⟨⟨x, tail⟩, out⟩

end Spec
end Interaction
