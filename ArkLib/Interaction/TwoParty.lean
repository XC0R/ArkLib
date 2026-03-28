import ArkLib.Interaction.Basic

/-!
# Two-Party Role-Based Interactions

Role-based interactions built on `Spec`. Each node is annotated with a `Role`
(via a `RoleDecoration`) indicating which side acts. This gives rise to:

- `Strategy.withRoles` — the focal party's strategy (Sigma at own nodes, Pi at
  the counterpart's nodes)
- `Counterpart` — the other party's strategy (Pi at own nodes, Sigma at the
  counterpart's nodes)

Roles are stored as a `Spec.Decoration`, not baked into a separate inductive.
This means `Transcript`, `Decoration`, `MonadDecoration`, `append`, etc. are
all inherited from `Spec` with zero duplication.

## Main definitions

- `Role` — sender / receiver marker
- `Role.Action` — role-dependent action type (Sigma or Pi)
- `Role.Dual` — dual of `Action` (Pi or Sigma)
- `Role.interact` — execute one round of two-party interaction
- `RoleDecoration` — per-node role assignment on a `Spec`
- `Spec.Strategy.withRoles` / `Spec.Counterpart` — role-dependent strategy types
- `Spec.Strategy.runWithRoles` — execute a strategy against a counterpart
-/

set_option autoImplicit false

namespace Interaction

/-- Role marker for two-party interactions. -/
inductive Role where
  | sender
  | receiver

namespace Role

def swap : Role → Role
  | .sender => .receiver
  | .receiver => .sender

/-- Role-dependent action at an interaction node with dependent continuation.
- `sender`: choose a move (Sigma)
- `receiver`: respond to any move (Pi) -/
def Action (role : Role) (m : Type → Type) (X : Type) (Cont : X → Type) : Type :=
  match role with
  | .sender => (x : X) × m (Cont x)
  | .receiver => (x : X) → m (Cont x)

/-- Dual of `Action`:
- `sender`: observe any move (Pi, pure)
- `receiver`: produce a move (Sigma, monadic) -/
def Dual (role : Role) (m : Type → Type) (X : Type) (Cont : X → Type) : Type :=
  match role with
  | .sender => (x : X) → Cont x
  | .receiver => m ((x : X) × Cont x)

/-- Execute one round of interaction between a role-action and its dual.
Extracts the chosen move `x`, the action's continuation, and the dual's
continuation, then passes all three to the callback `k`. -/
def interact {m : Type → Type} [Monad m] {X : Type}
    {ACont DCont : X → Type} {Result : Type} :
    (role : Role) → role.Action m X ACont → role.Dual m X DCont →
    ((x : X) → ACont x → DCont x → m Result) → m Result
  | .sender, ⟨x, mCont⟩, dualFn, k => do
      let cont ← mCont
      k x cont (dualFn x)
  | .receiver, recvFn, mDual, k => do
      let ⟨x, dualCont⟩ ← mDual
      let cont ← recvFn x
      k x cont dualCont

end Role

/-! ## Role decoration -/

/-- A role decoration assigns a `Role` (sender/receiver) to each internal node
of an interaction spec. This is what used to be the `TwoParty` inductive —
now it's just data on `Spec`. -/
abbrev RoleDecoration := Spec.Decoration (fun _ => Role)

/-- Swap all roles in a decoration (sender ↔ receiver). -/
abbrev RoleDecoration.swap {spec : Spec} (roles : RoleDecoration spec) :
    RoleDecoration spec :=
  Spec.Decoration.map (fun _ => Role.swap) spec roles

namespace Spec

/-! ## Role-dependent strategy

`Strategy.withRoles m spec roles Output` is the focal party's strategy over
a role-decorated spec. At sender nodes the player chooses (Sigma), at receiver
nodes the player responds to any move (Pi). -/

/-- Role-dependent strategy. Generalizes the old `TwoParty.Strategy`. -/
def Strategy.withRoles (m : Type → Type) :
    (spec : Spec) → RoleDecoration spec → (Transcript spec → Type) → Type
  | .done, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, dRest⟩, Output =>
      role.Action m X (fun x => withRoles m (rest x) (dRest x)
        (fun p => Output ⟨x, p⟩))

/-- Non-dependent role-strategy variant. -/
abbrev Strategy.withRoles' (m : Type → Type) (spec : Spec)
    (roles : RoleDecoration spec) (α : Type) :=
  Strategy.withRoles m spec roles (fun _ => α)

/-- Counterpart strategy: Pi at sender nodes, Sigma at receiver nodes
(via `Role.Dual`). -/
def Counterpart (m : Type → Type) :
    (spec : Spec) → RoleDecoration spec → Type
  | .done, _ => PUnit
  | .node X rest, ⟨role, dRest⟩ =>
      role.Dual m X (fun x => Counterpart m (rest x) (dRest x))

/-- Run a role-dependent strategy against a counterpart. -/
def Strategy.runWithRoles {m : Type → Type} [Monad m] :
    (spec : Spec) → (roles : RoleDecoration spec) →
    {Output : Transcript spec → Type} →
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

/-! ## Per-node monad decoration (role-aware)

The single-monad `Strategy.withRoles m` uses the same monad `m` at every node.
For richer models (e.g. different oracle access per round), we support a
per-node monad via `MonadDecoration`. -/

/-- Role-dependent strategy with per-node monads from a decoration. -/
def Strategy.withRolesAndMonads :
    (spec : Spec) → RoleDecoration spec → MonadDecoration spec →
    (Transcript spec → Type) → Type
  | .done, _, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, rRest⟩, ⟨bm, mRest⟩, Output =>
      role.Action bm.M X
        (fun x => withRolesAndMonads (rest x) (rRest x) (mRest x)
          (fun p => Output ⟨x, p⟩))

/-- Counterpart with per-node monads. Unlike the single-monad `Counterpart`
(which is pure at sender nodes via `Dual`), this version is fully monadic:
each node's bundled monad is used regardless of role. -/
def Counterpart.withMonads :
    (spec : Spec) → RoleDecoration spec → MonadDecoration spec → Type
  | .done, _, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩, ⟨bm, mRest⟩ =>
      (x : X) → bm.M (withMonads (rest x) (rRest x) (mRest x))
  | .node X rest, ⟨.receiver, rRest⟩, ⟨bm, mRest⟩ =>
      bm.M ((x : X) × withMonads (rest x) (rRest x) (mRest x))

/-- Run a per-node-monad strategy against a per-node-monad counterpart, lifting
each side's monad into a common base monad `m`. The strategy and counterpart
can use *different* monad decorations. -/
def Strategy.runWithRolesAndMonads {m : Type → Type} [Monad m]
    (liftStrat : ∀ (bm : _root_.BundledMonad) {α}, bm.M α → m α)
    (liftCpt : ∀ (bm : _root_.BundledMonad) {α}, bm.M α → m α) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (stratDeco : MonadDecoration spec) → (cptDeco : MonadDecoration spec) →
    {Output : Transcript spec → Type} →
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

/-! ## Examples -/

section Examples

variable (m : Type → Type) [Monad m]
variable (T U : Type) (α : Type)

private def exSpec := Spec.node T fun _ => .node U fun _ => .done
private def exRoles : RoleDecoration (exSpec T U) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

example : Spec.Strategy.withRoles m (exSpec T U) (exRoles T U) (fun _ => α)
    = ((_ : T) × m ((_ : U) → m α)) := rfl

example : Spec.Counterpart m (exSpec T U) (exRoles T U)
    = ((_ : T) → m ((_ : U) × PUnit)) := rfl

end Examples

end Interaction
