/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Node

/-!
# Decorations and dependent decorations (`Over`)

`Spec.Decoration Γ spec` is concrete nodewise metadata attached to a fixed
protocol tree `spec`, where `Γ : Spec.Node.Context` is the realized family of
node-local information. If a node of `spec` has move space `X`, then a
decoration provides one value of type `Γ X` at that node, and recursively
decorates every continuation subtree.

This is the basic way to say "the same protocol tree, but with extra data at
each node". Typical examples include:
* `RoleDecoration`, recording who controls a node;
* monad decorations, recording which monad a local action uses at a node;
* oracle decorations, recording what oracle interface is available there.

A context may be written directly, or obtained from a telescope
`Spec.Node.Schema` via `Spec.Node.Schema.toContext`.

`Decoration.Over` is the dependent (displayed) variant:
its fibers may depend on the context value drawn from an existing decoration.

Naming note:
`Decoration.Over` is nested because it is literally a decoration over a fixed
base decoration value. By contrast, `ShapeOver` and `InteractionOver` keep the
suffix form because they are the primary generalized syntax and semantics
layers, not dependent objects over a fixed base `Shape` or `Interaction`.

Functorial `map` / `map_id` / `map_comp` for both layers are in this file.
Composition along `Spec.append` is in `ArkLib.Interaction.Basic.Append`.
-/

universe u v w w₂

namespace Interaction
namespace Spec

/-- `Decoration Γ spec` is concrete nodewise metadata on the fixed protocol
tree `spec`, for a realized node context `Γ`.

If a node of `spec` has move space `X`, then the decoration stores one value of
type `Γ X` at that node, and recursively stores decorations on every subtree.

This is different from `Spec.ShapeOver`:
* a decoration is **data on a tree**;
* a shape is a **specification of local participant objects** that consumes such
  data. -/
def Decoration (Γ : Node.Context.{u, v}) : Spec → Type (max u v)
  | .done => PUnit
  | .node X rest => Γ X × (∀ x, Decoration Γ (rest x))

/-- Natural transformation between per-node decorations, applied recursively. -/
def Decoration.map {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    (f : ∀ X, Γ X → Δ X) :
    (spec : Spec) → Decoration Γ spec → Decoration Δ spec
  | .done, _ => ⟨⟩
  | .node X rest, ⟨s, dRest⟩ => ⟨f X s, fun x => Decoration.map f (rest x) (dRest x)⟩

@[simp, grind =]
theorem Decoration.map_id {Γ : Node.Context.{u, v}} :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.map (fun X (s : Γ X) => s) spec d = d
  | .done, ⟨⟩ => rfl
  | .node _ rest, ⟨s, dRest⟩ => by
      simp only [Decoration.map]; congr 1; funext x; exact map_id (rest x) (dRest x)

theorem Decoration.map_comp
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}} {Λ : Node.Context.{u, w₂}}
    (g : ∀ X, Δ X → Λ X) (f : ∀ X, Γ X → Δ X) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.map g spec (Decoration.map f spec d) =
      Decoration.map (fun X => g X ∘ f X) spec d
  | .done, ⟨⟩ => rfl
  | .node _ rest, ⟨s, dRest⟩ => by
      simp only [Decoration.map]; congr 1; funext x
      exact map_comp g f (rest x) (dRest x)

/-- Dependent decoration over `d : Decoration Γ spec`: at each node, data in
`F X γ` where `γ` is the context value from `d`, plus recursive decorations on
subtrees. -/
def Decoration.Over {Γ : Node.Context.{u, v}} (F : ∀ X, Γ X → Type w) :
    (spec : Spec) → Decoration Γ spec → Type (max u w)
  | .done, _ => PUnit
  | .node X rest, ⟨γ, dRest⟩ =>
      F X γ × (∀ x, Decoration.Over F (rest x) (dRest x))

/-- Fiberwise map between dependent decoration families over the same base
decoration. -/
def Decoration.Over.map {Γ : Node.Context.{u, v}}
    {F : ∀ X, Γ X → Type w} {G : ∀ X, Γ X → Type w}
    (f : ∀ X γ, F X γ → G X γ) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.Over F spec d → Decoration.Over G spec d
  | .done, _, _ => ⟨⟩
  | .node X rest, ⟨γ, dRest⟩, ⟨fData, rRest⟩ =>
      ⟨f X γ fData, fun x => Over.map f (rest x) (dRest x) (rRest x)⟩

@[simp, grind =]
theorem Decoration.Over.map_id {Γ : Node.Context.{u, v}} {F : ∀ X, Γ X → Type w} :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over F spec d) →
    Decoration.Over.map (fun _ _ x => x) spec d r = r
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨fd, rr⟩ => by
      simp only [Decoration.Over.map]; congr 1; funext x
      exact map_id (rest x) (dRest x) (rr x)

theorem Decoration.Over.map_comp {Γ : Node.Context.{u, v}}
    {F G H : ∀ X, Γ X → Type w}
    (g : ∀ X γ, G X γ → H X γ) (f : ∀ X γ, F X γ → G X γ) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over F spec d) →
    Decoration.Over.map g spec d (Decoration.Over.map f spec d r) =
      Decoration.Over.map (fun X γ => g X γ ∘ f X γ) spec d r
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨fd, rr⟩ => by
      simp only [Decoration.Over.map]; congr 1; funext x
      exact map_comp g f (rest x) (dRest x) (rr x)

end Spec
end Interaction
