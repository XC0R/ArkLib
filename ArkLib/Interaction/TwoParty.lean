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

universe u v w

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
def Action (role : Role) (m : Type u → Type u) (X : Type u) (Cont : X → Type u) : Type u :=
  match role with
  | .sender => (x : X) × m (Cont x)
  | .receiver => (x : X) → m (Cont x)

/-- Dual of `Action`:
- `sender`: observe any move (Pi, pure)
- `receiver`: produce a move (Sigma, monadic) -/
def Dual (role : Role) (m : Type u → Type u) (X : Type u) (Cont : X → Type u) : Type u :=
  match role with
  | .sender => (x : X) → Cont x
  | .receiver => m ((x : X) × Cont x)

/-- Execute one round of interaction between a role-action and its dual.
Extracts the chosen move `x`, the action's continuation, and the dual's
continuation, then passes all three to the callback `k`. -/
def interact {m : Type u → Type u} [Monad m] {X : Type u}
    {ACont DCont : X → Type u} {Result : Type u} :
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
def Strategy.withRoles (m : Type u → Type u) :
    (spec : Spec) → RoleDecoration spec → (Transcript spec → Type u) → Type u
  | .done, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, dRest⟩, Output =>
      role.Action m X (fun x => withRoles m (rest x) (dRest x)
        (fun p => Output ⟨x, p⟩))

/-- Non-dependent role-strategy variant. -/
abbrev Strategy.withRoles' (m : Type u → Type u) (spec : Spec)
    (roles : RoleDecoration spec) (α : Type u) :=
  Strategy.withRoles m spec roles (fun _ => α)

/-- Counterpart strategy: Pi at sender nodes, Sigma at receiver nodes
(via `Role.Dual`). -/
def Counterpart (m : Type u → Type u) :
    (spec : Spec) → RoleDecoration spec → Type u
  | .done, _ => PUnit
  | .node X rest, ⟨role, dRest⟩ =>
      role.Dual m X (fun x => Counterpart m (rest x) (dRest x))

/-- Run a role-dependent strategy against a counterpart. -/
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

/-! ## Per-node monad decoration (role-aware)

The single-monad `Strategy.withRoles m` uses the same monad `m` at every node.
For richer models (e.g. different oracle access per round), we support a
per-node monad via `MonadDecoration`. -/

/-- Role-dependent strategy with per-node monads from a decoration. -/
def Strategy.withRolesAndMonads :
    (spec : Spec.{u}) → RoleDecoration spec → MonadDecoration spec →
    (Transcript spec → Type u) → Type u
  | .done, _, _, Output => Output ⟨⟩
  | .node X rest, ⟨role, rRest⟩, ⟨bm, mRest⟩, Output =>
      role.Action bm.M X
        (fun x => withRolesAndMonads (rest x) (rRest x) (mRest x)
          (fun p => Output ⟨x, p⟩))

/-- Counterpart with per-node monads. Unlike the single-monad `Counterpart`
(which is pure at sender nodes via `Dual`), this version is fully monadic:
each node's bundled monad is used regardless of role. -/
def Counterpart.withMonads :
    (spec : Spec.{u}) → RoleDecoration spec → MonadDecoration spec → Type u
  | .done, _, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩, ⟨bm, mRest⟩ =>
      (x : X) → bm.M (withMonads (rest x) (rRest x) (mRest x))
  | .node X rest, ⟨.receiver, rRest⟩, ⟨bm, mRest⟩ =>
      bm.M ((x : X) × withMonads (rest x) (rRest x) (mRest x))

/-- Run a per-node-monad strategy against a per-node-monad counterpart, lifting
each side's monad into a common base monad `m`. The strategy and counterpart
can use *different* monad decorations. -/
def Strategy.runWithRolesAndMonads {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : _root_.BundledMonad) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : _root_.BundledMonad) {α : Type u}, bm.M α → m α) :
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

/-! ## Role-aware composition — binary append -/

/-- Compose two role decorations along `Spec.append`. -/
abbrev RoleDecoration.append {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    (r₁ : RoleDecoration s₁)
    (r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)) :
    RoleDecoration (s₁.append s₂) :=
  Spec.Decoration.append r₁ r₂

/-- Compose two role-dependent strategies along `Spec.append`. -/
def Spec.Strategy.compWithRoles {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.join s₁ s₂ tr₁ tr₂)))) :
    m (Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      let ⟨x, cont⟩ := strat₁
      pure ⟨x, do
        let next ← cont
        compWithRoles next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        compWithRoles next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Compose two counterpart strategies along `Spec.append`. -/
def Spec.Counterpart.append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)} :
    Spec.Counterpart m s₁ r₁ →
    ((tr₁ : Spec.Transcript s₁) → Spec.Counterpart m (s₂ tr₁) (r₂ tr₁)) →
    Spec.Counterpart m (s₁.append s₂) (r₁.append r₂) :=
  match s₁, r₁ with
  | .done, _ => fun _ c₂ => c₂ ⟨⟩
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => Counterpart.append (c₁ x) (fun p => c₂ ⟨x, p⟩)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.append cRest (fun p => c₂ ⟨x, p⟩)⟩

/-- Run a composed role-strategy against a composed counterpart over `Spec.append`. -/
def Spec.Strategy.runWithRolesAppend {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat : Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output)
    (cpt : Spec.Counterpart m (s₁.append s₂) (r₁.append r₂)) :
    m ((tr : Spec.Transcript (s₁.append s₂)) × Output tr) :=
  Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat cpt

/-! ## Role-aware composition — N-ary replicate -/

/-- Replicate a role decoration `n` times. -/
abbrev RoleDecoration.replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration (spec.replicate n) :=
  Spec.Decoration.replicate roles n

/-- Swapping roles commutes with `replicate`. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    (roles.replicate n).swap = (roles.swap).replicate n :=
  Spec.Decoration.map_replicate (fun _ => Role.swap) roles n

/-- Iterate a counterpart `n` times over `spec.replicate n`. -/
def Spec.Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} :
    (n : Nat) →
    (Fin n → Spec.Counterpart m spec roles) →
    Spec.Counterpart m (spec.replicate n) (roles.replicate n)
  | 0, _ => ⟨⟩
  | n + 1, cpts =>
      Spec.Counterpart.append (cpts 0) (fun _ => iterate n (fun i => cpts i.succ))

/-- Iterate a uniform counterpart `n` times. -/
def Spec.Counterpart.iterateUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec}
    (n : Nat) (cpt : Spec.Counterpart m spec roles) :
    Spec.Counterpart m (spec.replicate n) (roles.replicate n) :=
  Spec.Counterpart.iterate n (fun _ => cpt)

/-- Iterate a role-dependent strategy `n` times over `spec.replicate n`. -/
def Spec.Strategy.iterateWithRoles {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α →
      m (Strategy.withRoles m spec roles (fun _ => α))) →
    α →
    m (Strategy.withRoles m (spec.replicate n) (roles.replicate n) (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    compWithRoles strat (fun _ mid => iterateWithRoles n (fun i => step i.succ) mid)

/-- Iterate a uniform role-dependent strategy `n` times. -/
def Spec.Strategy.iterateWithRolesUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u}
    (n : Nat) (step : α → m (Strategy.withRoles m spec roles (fun _ => α)))
    (a : α) :
    m (Strategy.withRoles m (spec.replicate n) (roles.replicate n) (fun _ => α)) :=
  Strategy.iterateWithRoles n (fun _ => step) a

/-! ## Role-aware composition — dependent N-ary chain -/

/-- Role decoration along a chain. -/
abbrev RoleDecoration.chain
    {Stage : Nat → Type v} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    (roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s))
    (n : Nat) (i : Nat) (s : Stage i) :
    RoleDecoration (Spec.chain Stage spec advance n i s) :=
  Spec.Decoration.chain roles n i s

/-- Iterate a counterpart family over a chain. -/
def Spec.Counterpart.chainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (step : (i : Nat) → (s : Stage i) → Spec.Counterpart m (spec i s) (roles i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Spec.Counterpart m (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Spec.Counterpart.append (step i s)
        (fun tr => chainComp step n (i + 1) (advance i s tr))

/-- Iterate a role-dependent strategy family over a chain. -/
def Spec.Strategy.chainCompWithRoles {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {α : Type u}
    (step : (i : Nat) → (s : Stage i) → α →
      m (Strategy.withRoles m (spec i s) (roles i s) (fun _ => α))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → α →
    m (Strategy.withRoles m (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s) (fun _ => α))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    compWithRoles strat
      (fun tr mid => chainCompWithRoles step n (i + 1) (advance i s tr) mid)

/-! ## Role-aware: swap properties -/

@[simp, grind =]
theorem Role.swap_swap (r : Role) : r.swap.swap = r := by cases r <;> rfl

@[simp, grind =]
theorem RoleDecoration.swap_swap :
    (spec : Spec) → (roles : RoleDecoration spec) →
    roles.swap.swap = roles
  | .done, _ => rfl
  | .node _ rest, ⟨r, rRest⟩ => by
      simp only [RoleDecoration.swap, Spec.Decoration.map, Role.swap_swap]
      congr 1; funext x
      exact RoleDecoration.swap_swap (rest x) (rRest x)

/-- Swapping roles commutes with `append`. -/
theorem RoleDecoration.swap_append
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    (r₁ : RoleDecoration s₁)
    (r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)) :
    (r₁.append r₂).swap = (r₁.swap).append (fun tr₁ => (r₂ tr₁).swap) :=
  Spec.Decoration.map_append (fun _ => Role.swap) s₁ s₂ r₁ r₂

/-! ## Role-aware refinement

`Role.Refine S` is a role-aware displayed decoration: it carries `S X` data at
sender nodes and recurses directly at receiver nodes (no `PUnit` junk). This is
the preferred interface for sender-specific data in two-party protocols.

Compare with the generic `Decoration.Refine`, which carries `F X l` uniformly
at every node regardless of label. `Role.Refine` exploits the two-element
`Role` inductive to skip receiver nodes entirely. -/

/-- Role-aware refinement: carries `S X` at sender nodes, recurses at receiver
nodes, `PUnit` at done. Defined by recursion on `spec` + `RoleDecoration`.

Marked `@[reducible]` so downstream pattern matching on `spec` + `roles`
automatically reduces the `Role.Refine` type (needed for equation compilation
in definitions like `QueryHandle` that match on both). -/
@[reducible] def Role.Refine (S : Type u → Type v) :
    (spec : Spec.{u}) → RoleDecoration spec → Type (max u v)
  | .done, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩ =>
      S X × (∀ x, Role.Refine S (rest x) (rRest x))
  | .node _X rest, ⟨.receiver, rRest⟩ =>
      ∀ x, Role.Refine S (rest x) (rRest x)

/-- Apply a fiberwise transformation to a `Role.Refine`. -/
def Role.Refine.map {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Role.Refine S spec roles → Role.Refine T spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ =>
      ⟨f _ s, fun x => Refine.map f (rest x) (rRest x) (rr x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, rr =>
      fun x => Refine.map f (rest x) (rRest x) (rr x)

/-- Compose two `Role.Refine`s along `Spec.append`. -/
def Role.Refine.append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)} :
    Role.Refine S s₁ r₁ →
    ((tr₁ : Spec.Transcript s₁) → Role.Refine S (s₂ tr₁) (r₂ tr₁)) →
    Role.Refine S (s₁.append s₂) (r₁.append r₂) :=
  match s₁, r₁ with
  | .done, _ => fun _ sd₂ => sd₂ ⟨⟩
  | .node _ _rest, ⟨.sender, _rRest⟩ => fun ⟨s, rr⟩ sd₂ =>
      ⟨s, fun x => Refine.append (rr x) (fun p => sd₂ ⟨x, p⟩)⟩
  | .node _ _rest, ⟨.receiver, _rRest⟩ => fun rr sd₂ =>
      fun x => Refine.append (rr x) (fun p => sd₂ ⟨x, p⟩)

/-- Replicate a `Role.Refine` along `Spec.replicate`. -/
def Role.Refine.replicate {S : Type u → Type v}
    {spec : Spec} {roles : RoleDecoration spec}
    (sd : Role.Refine S spec roles) : (n : Nat) →
    Role.Refine S (spec.replicate n) (roles.replicate n)
  | 0 => ⟨⟩
  | n + 1 => Refine.append sd (fun _ => Refine.replicate sd n)

/-- Compose a `Role.Refine` family along `Spec.chain`. -/
def Role.Refine.chain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (sdeco : (i : Nat) → (s : Stage i) → Role.Refine S (spec i s) (roles i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Role.Refine S (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Refine.append (sdeco i s)
        (fun tr => Refine.chain sdeco n (i + 1) (advance i s tr))

/-! ### SenderDecoration (abbrev for Role.Refine) -/

/-- `SenderDecoration S` is `Role.Refine S`: carries `S X` at sender nodes,
recurses directly at receiver nodes. -/
abbrev SenderDecoration (S : Type u → Type v) (spec : Spec.{u})
    (roles : RoleDecoration spec) :=
  Role.Refine S spec roles

abbrev SenderDecoration.append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    (sd₁ : SenderDecoration S s₁ r₁)
    (sd₂ : (tr₁ : Spec.Transcript s₁) → SenderDecoration S (s₂ tr₁) (r₂ tr₁)) :
    SenderDecoration S (s₁.append s₂) (r₁.append r₂) :=
  Role.Refine.append sd₁ sd₂

abbrev SenderDecoration.replicate {S : Type u → Type v}
    {spec : Spec} {roles : RoleDecoration spec}
    (sd : SenderDecoration S spec roles) (n : Nat) :
    SenderDecoration S (spec.replicate n) (roles.replicate n) :=
  Role.Refine.replicate sd n

abbrev SenderDecoration.chain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (sdeco : (i : Nat) → (s : Stage i) → SenderDecoration S (spec i s) (roles i s))
    (n : Nat) (i : Nat) (s : Stage i) :
    SenderDecoration S (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s) :=
  Role.Refine.chain sdeco n i s

/-! ### Equivalence with Decoration.Refine -/

/-- Fiber family selecting `S X` at sender nodes and `PUnit` at receiver nodes.
Used only for the equivalence between `Role.Refine` and `Decoration.Refine`. -/
def Role.SenderData (S : Type u → Type v) (X : Type u) : Role → Type v
  | .sender => S X
  | .receiver => PUnit

/-- Convert `Role.Refine` to `Decoration.Refine` by inserting `PUnit` at
receiver nodes. -/
def Role.Refine.toDecorationRefine {S : Type u → Type v} :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Role.Refine S spec roles →
    Spec.Decoration.Refine (fun X r => Role.SenderData S X r) spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ =>
      ⟨s, fun x => toDecorationRefine (rest x) (rRest x) (rr x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, rr =>
      ⟨⟨⟩, fun x => toDecorationRefine (rest x) (rRest x) (rr x)⟩

/-- Convert `Decoration.Refine` to `Role.Refine` by dropping `PUnit` at
receiver nodes. -/
def Role.Refine.ofDecorationRefine {S : Type u → Type v} :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Spec.Decoration.Refine (fun X r => Role.SenderData S X r) spec roles →
    Role.Refine S spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ =>
      ⟨s, fun x => ofDecorationRefine (rest x) (rRest x) (rr x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, rr⟩ =>
      fun x => ofDecorationRefine (rest x) (rRest x) (rr x)

/-! ## Examples -/

section Examples

variable (m : Type u → Type u) [Monad m]
variable (T U : Type u) (α : Type u)

private def exSpec := Spec.node T fun _ => .node U fun _ => .done
private def exRoles : RoleDecoration (exSpec T U) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

example : Spec.Strategy.withRoles m (exSpec T U) (exRoles T U) (fun _ => α)
    = ((_ : T) × m ((_ : U) → m α)) := rfl

example : Spec.Counterpart m (exSpec T U) (exRoles T U)
    = ((_ : T) → m ((_ : U) × PUnit)) := rfl

end Examples

end Interaction
