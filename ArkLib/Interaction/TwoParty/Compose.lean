/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Interaction.Basic.Append
import ArkLib.Interaction.Basic.Replicate
import ArkLib.Interaction.Basic.Chain
import ArkLib.Interaction.TwoParty.Decoration
import ArkLib.Interaction.TwoParty.Strategy

/-!
# Composing two-party protocols

Binary `Spec.append` for role strategies and counterparts; uniform and dependent `n`-fold iteration
over `replicate` and `chain`.
-/

set_option autoImplicit false

universe u v

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

/-- Kleisli composition of `withRoles` strategies along `Spec.append`. -/
def Strategy.compWithRoles {m : Type u → Type u} [Monad m]
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

/-- Pointwise append of counterparts over `Spec.append`. -/
def Counterpart.append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)} :
    Counterpart m s₁ r₁ →
    ((tr₁ : Spec.Transcript s₁) → Counterpart m (s₂ tr₁) (r₂ tr₁)) →
    Counterpart m (s₁.append s₂) (r₁.append r₂) :=
  match s₁, r₁ with
  | .done, _ => fun _ c₂ => c₂ ⟨⟩
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => Counterpart.append (c₁ x) (fun p => c₂ ⟨x, p⟩)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.append cRest (fun p => c₂ ⟨x, p⟩)⟩

/-- Run a composed strategy against a composed counterpart (definitional wrapper). -/
def Strategy.runWithRolesAppend {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat : Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output)
    (cpt : Counterpart m (s₁.append s₂) (r₁.append r₂)) :
    m ((tr : Spec.Transcript (s₁.append s₂)) × Output tr) :=
  Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat cpt

/-- Replicate a role decoration `n` times along `Spec.replicate`. -/
abbrev RoleDecoration.replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration (spec.replicate n) :=
  Spec.Decoration.replicate roles n

/-- Swapping commutes with `RoleDecoration.replicate`. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration.swap (roles.replicate n) = (RoleDecoration.swap roles).replicate n :=
  Spec.Decoration.map_replicate (fun _ => Role.swap) roles n

/-- `n`-fold counterpart composition on `spec.replicate n`. -/
def Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} :
    (n : Nat) →
    (Fin n → Counterpart m spec roles) →
    Counterpart m (spec.replicate n) (roles.replicate n)
  | 0, _ => ⟨⟩
  | n + 1, cpts =>
      Counterpart.append (cpts 0) (fun _ => iterate n (fun i => cpts i.succ))

/-- Uniform `Counterpart.iterate`. -/
def Counterpart.iterateUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec}
    (n : Nat) (cpt : Counterpart m spec roles) :
    Counterpart m (spec.replicate n) (roles.replicate n) :=
  Counterpart.iterate n (fun _ => cpt)

/-- Iterate a `withRoles` strategy `n` times on `replicate`. -/
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
    compWithRoles strat (fun _ mid => iterateWithRoles n (fun i => step i.succ) mid)

/-- Uniform `iterateWithRoles`. -/
def Strategy.iterateWithRolesUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u}
    (n : Nat) (step : α → m (Strategy.withRoles m spec roles (fun _ => α)))
    (a : α) :
    m (Strategy.withRoles m (spec.replicate n) (roles.replicate n) (fun _ => α)) :=
  Strategy.iterateWithRoles n (fun _ => step) a

end Spec

/-- Role decoration along `Spec.chain` (lives under `Interaction`, not `Spec`). -/
abbrev RoleDecoration.chain
    {Stage : Nat → Type v} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    (roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s))
    (n : Nat) (i : Nat) (s : Stage i) :
    RoleDecoration (Spec.chain Stage spec advance n i s) :=
  Spec.Decoration.chain roles n i s

namespace Spec

/-- Counterpart family composed along a chain. -/
def Counterpart.chainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (step : (i : Nat) → (s : Stage i) → Counterpart m (spec i s) (roles i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Counterpart m (Spec.chain Stage spec advance n i s)
      (RoleDecoration.chain roles n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Counterpart.append (step i s)
        (fun tr => chainComp step n (i + 1) (advance i s tr))

/-- `withRoles` strategy family along a chain. -/
def Strategy.chainCompWithRoles {m : Type u → Type u} [Monad m]
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

end Spec
end Interaction
