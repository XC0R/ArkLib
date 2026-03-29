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

/-- Pointwise append of counterparts over `Spec.append`, threading the `Output` type
through the join of transcripts. -/
def Counterpart.append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : Spec.Transcript s₁ → Type u}
    {Output₂ : Spec.Transcript (s₁.append s₂) → Type u} :
    Counterpart m s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output₂ (Spec.Transcript.join s₁ s₂ tr₁ tr₂))) →
    Counterpart m (s₁.append s₂) (r₁.append r₂) Output₂ :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => Counterpart.append (c₁ x) (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.append cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- Run a composed strategy against a composed counterpart (definitional wrapper). -/
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

/-- Replicate a role decoration `n` times along `Spec.replicate`. -/
abbrev RoleDecoration.replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration (spec.replicate n) :=
  Spec.Decoration.replicate roles n

/-- Swapping commutes with `RoleDecoration.replicate`. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    (roles.replicate n).swap = (roles.swap).replicate n :=
  Spec.Decoration.map_replicate (fun _ => Role.swap) roles n

/-- `n`-fold counterpart composition on `spec.replicate n`, threading state `β`
through each round (mirroring `Strategy.iterateWithRoles`). -/
def Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u} :
    (n : Nat) →
    (Fin n → β → Counterpart m spec roles (fun _ => β)) →
    β →
    Counterpart m (spec.replicate n) (roles.replicate n) (fun _ => β)
  | 0, _, b => b
  | n + 1, step, b =>
      Counterpart.append (step 0 b) (fun _ b' => iterate n (fun i => step i.succ) b')

/-- Uniform `Counterpart.iterate` (same step at every round). -/
def Counterpart.iterateUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u}
    (n : Nat) (step : β → Counterpart m spec roles (fun _ => β)) (b : β) :
    Counterpart m (spec.replicate n) (roles.replicate n) (fun _ => β) :=
  Counterpart.iterate n (fun _ => step) b

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

/-- Counterpart family composed along a chain, threading state `β`
(mirroring `Strategy.chainCompWithRoles`). -/
def Counterpart.chainComp {m : Type u → Type u} [Monad m]
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
      Counterpart.append (step i s b)
        (fun tr b' => chainComp step n (i + 1) (advance i s tr) b')

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
