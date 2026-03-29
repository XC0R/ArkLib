/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Append
import ArkLib.Interaction.Basic.Replicate
import ArkLib.Interaction.Basic.Chain
import ArkLib.Interaction.TwoParty.Decoration
import ArkLib.Interaction.TwoParty.Strategy

/-!
# Composing two-party protocols

Role-aware composition of strategies and counterparts along `Spec.append`, `Spec.replicate`,
and `Spec.chain`. Each combinator dispatches on the role at each node—sending or receiving—to
compose the two-party strategies correctly.

For binary composition, `compWithRoles` and `Counterpart.append` use `Transcript.liftAppend`
for the output type (factored form). The flat variants (`compWithRolesFlat`,
`Counterpart.appendFlat`) take a single output family on the combined transcript.
-/

universe u v

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

/-- Compose role-aware strategies along `Spec.append` with a two-argument output family
lifted through `Transcript.liftAppend`. The continuation receives the first phase's
output and produces a second-phase strategy. -/
def Strategy.compWithRoles {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {F : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁) (F tr₁))) :
    m (Strategy.withRoles m (s₁.append s₂) (r₁.append r₂)
      (Spec.Transcript.liftAppend s₁ s₂ F)) :=
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

/-- Compose role-aware strategies along `Spec.append` with a single output family
on the combined transcript. The continuation indexes via `Transcript.append`. -/
def Strategy.compWithRolesFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))) :
    m (Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      let ⟨x, cont⟩ := strat₁
      pure ⟨x, do
        let next ← cont
        compWithRolesFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        compWithRolesFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Compose counterparts along `Spec.append` with a two-argument output family
lifted through `Transcript.liftAppend`. The continuation maps the first phase's
output to a second-phase counterpart. -/
def Counterpart.append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : Spec.Transcript s₁ → Type u}
    {F : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u} :
    Counterpart m s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    Counterpart m (s₁.append s₂) (r₁.append r₂)
      (Spec.Transcript.liftAppend s₁ s₂ F) :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => Counterpart.append (c₁ x) (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.append cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- Compose counterparts along `Spec.append` with a single output family on the
combined transcript. The continuation indexes via `Transcript.append`. -/
def Counterpart.appendFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : Spec.Transcript s₁ → Type u}
    {Output₂ : Spec.Transcript (s₁.append s₂) → Type u} :
    Counterpart m s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output₂ (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) →
    Counterpart m (s₁.append s₂) (r₁.append r₂) Output₂ :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => Counterpart.appendFlat (c₁ x) (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.appendFlat cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- Run a strategy against a counterpart on a composed interaction. -/
def Strategy.runWithRolesAppend {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {OutputP : Spec.Transcript (s₁.append s₂) → Type u}
    {OutputC : Spec.Transcript (s₁.append s₂) → Type u}
    (strat : Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) OutputP)
    (cpt : Counterpart m (s₁.append s₂) (r₁.append r₂) OutputC) :
    m ((tr : Spec.Transcript (s₁.append s₂)) × OutputP tr × OutputC tr) :=
  Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat cpt

/-- Replicate a role decoration `n` times, mirroring `Spec.replicate`. -/
abbrev RoleDecoration.replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration (spec.replicate n) :=
  Spec.Decoration.replicate roles n

/-- Role swapping commutes with replication. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    (roles.replicate n).swap = (roles.swap).replicate n :=
  Spec.Decoration.map_replicate (fun _ => Role.swap) roles n

/-- `n`-fold counterpart iteration on `spec.replicate n`, threading state `β`
through each round. -/
def Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u} :
    (n : Nat) →
    (Fin n → β → Counterpart m spec roles (fun _ => β)) →
    β →
    Counterpart m (spec.replicate n) (roles.replicate n) (fun _ => β)
  | 0, _, b => b
  | n + 1, step, b =>
      Counterpart.appendFlat (step 0 b) (fun _ b' => iterate n (fun i => step i.succ) b')

/-- Uniform `Counterpart.iterate`: same step function at every round. -/
def Counterpart.iterateUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u}
    (n : Nat) (step : β → Counterpart m spec roles (fun _ => β)) (b : β) :
    Counterpart m (spec.replicate n) (roles.replicate n) (fun _ => β) :=
  Counterpart.iterate n (fun _ => step) b

/-- `n`-fold role-aware strategy iteration on `spec.replicate n`, threading state `α`
through each round. -/
def Strategy.iterateWithRoles {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α →
      m (Strategy.withRoles m spec roles (fun _ => α))) →
    α →
    m (Strategy.withRoles m (spec.replicate n) (roles.replicate n) (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    compWithRolesFlat strat (fun _ mid => iterateWithRoles n (fun i => step i.succ) mid)

/-- Uniform `Strategy.iterateWithRoles`: same step function at every round. -/
def Strategy.iterateWithRolesUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u}
    (n : Nat) (step : α → m (Strategy.withRoles m spec roles (fun _ => α)))
    (a : α) :
    m (Strategy.withRoles m (spec.replicate n) (roles.replicate n) (fun _ => α)) :=
  Strategy.iterateWithRoles n (fun _ => step) a

end Spec

/-- Role decoration along `Spec.chain`: use `roles i s` at each stage. -/
abbrev RoleDecoration.chain
    {Stage : Nat → Type v} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    (roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s))
    (n : Nat) (i : Nat) (s : Stage i) :
    RoleDecoration (Spec.chain Stage spec advance n i s) :=
  Spec.Decoration.chain roles n i s

namespace Spec

/-- Compose counterparts along a chain with stage-dependent output. At each stage,
the step transforms `Family i s` into a counterpart whose output is
`Family (i+1) (advance i s tr)`. The full chain output is
`Transcript.chainFamily Family`. -/
def Counterpart.chainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      Counterpart m (spec i s) (roles i s) (fun tr => Family (i + 1) (advance i s tr))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    Counterpart m (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s) (Spec.Transcript.chainFamily Family n i s)
  | 0, _, _, b => b
  | n + 1, i, s, b =>
      Counterpart.append (step i s b)
        (fun tr b' => chainComp step n (i + 1) (advance i s tr) b')

/-- Uniform `Counterpart.chainComp` with a fixed output type `β` at every stage. -/
def Counterpart.chainCompUniform {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {β : Type u}
    (step : (i : Nat) → (s : Stage i) → β →
      Counterpart m (spec i s) (roles i s) (fun _ => β)) :
    (n : Nat) → (i : Nat) → (s : Stage i) → β →
    Counterpart m (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s) (fun _ => β)
  | 0, _, _, b => b
  | n + 1, i, s, b =>
      Counterpart.appendFlat (step i s b)
        (fun tr b' => chainCompUniform step n (i + 1) (advance i s tr) b')

/-- Compose role-aware strategies along a chain with stage-dependent output.
At each stage, the step transforms `Family i s` into a strategy whose output is
`Family (i+1) (advance i s tr)`. The full chain output is
`Transcript.chainFamily Family`. -/
def Strategy.chainCompWithRoles {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (Strategy.withRoles m (spec i s) (roles i s)
        (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (Strategy.withRoles m (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s) (Spec.Transcript.chainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    compWithRoles strat
      (fun tr mid => chainCompWithRoles step n (i + 1) (advance i s tr) mid)

/-- Uniform `Strategy.chainCompWithRoles` with a fixed output type `α` at every stage. -/
def Strategy.chainCompWithRolesUniform {m : Type u → Type u} [Monad m]
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
    compWithRolesFlat strat
      (fun tr mid => chainCompWithRolesUniform step n (i + 1) (advance i s tr) mid)

end Spec
end Interaction
