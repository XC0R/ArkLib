/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Node
import Mathlib.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Basic

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

This file also contains the bridge between the semantic and staged views of
node metadata: decorating a tree by an extended context `Γ.extend A` is
equivalent to giving a base decoration by `Γ` together with one dependent
`Decoration.Over A` layer on top of it.

In particular, if a schema is built as `(Spec.Node.Schema.singleton Γ).extend A`,
then `Decoration.equivOver A spec` is exactly the statement that a decoration
of that schema's realized context is the same as a base decoration by `Γ`
plus one displayed layer over it.
-/

universe u v w w₂

namespace Interaction
namespace Spec

private theorem prod_mk_heq {α : Type u} {β β' : Type v} {a : α} {b : β} {b' : β'}
    (h : b ≍ b') : ((a, b) : α × β) ≍ ((a, b') : α × β') := by
  cases h
  rfl

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

/--
Pack a base decoration and one dependent `Over` layer into a decoration of the
extended context `Γ.extend A`.

This is the tree-level realization of a single schema extension step.
-/
def Decoration.ofOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration Γ spec) → Decoration.Over A spec d →
    Decoration (Node.Context.extend Γ A) spec
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ =>
      ⟨⟨γ, a⟩, fun x => ofOver A (rest x) (dRest x) (rRest x)⟩

/--
Unpack a decoration of the extended context `Γ.extend A` into:
* its base decoration by `Γ`, and
* its displayed `Decoration.Over A` layer above that base.

This is the inverse structural view to `Decoration.ofOver`.
-/
def Decoration.toOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → Decoration (Node.Context.extend Γ A) spec →
    Σ d : Decoration Γ spec, Decoration.Over A spec d
  | .done, _ => ⟨⟨⟩, ⟨⟩⟩
  | .node _ rest, ⟨⟨γ, a⟩, dRest⟩ =>
      let ih := fun x => toOver A (rest x) (dRest x)
      ⟨⟨γ, fun x => (ih x).1⟩, ⟨a, fun x => (ih x).2⟩⟩

@[simp]
theorem Decoration.toOver_ofOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    Decoration.toOver A spec (Decoration.ofOver A spec d r) = ⟨d, r⟩
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      rw [Sigma.ext_iff]
      let baseTail :=
        fun x => (Decoration.toOver A (rest x)
          (Decoration.ofOver A (rest x) (dRest x) (rRest x))).1
      let overTail :=
        fun x => (Decoration.toOver A (rest x)
          (Decoration.ofOver A (rest x) (dRest x) (rRest x))).2
      have hbaseTail : baseTail = dRest := by
        funext x
        exact (Sigma.ext_iff.mp (toOver_ofOver A (rest x) (dRest x) (rRest x))).1
      have hoverTail : HEq overTail rRest := by
        refine Function.hfunext rfl ?_
        intro x y hxy
        cases hxy
        exact (Sigma.ext_iff.mp (toOver_ofOver A (rest x) (dRest x) (rRest x))).2
      have hpair : HEq (a, overTail) (a, rRest) := prod_mk_heq hoverTail
      exact ⟨Prod.ext rfl hbaseTail, hpair⟩

@[simp]
theorem Decoration.ofOver_toOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration (Node.Context.extend Γ A) spec) →
    Decoration.ofOver A spec (Decoration.toOver A spec d).1 (Decoration.toOver A spec d).2 = d
  | .done, ⟨⟩ => rfl
  | .node _ rest, ⟨⟨γ, a⟩, dRest⟩ => by
      simp [Decoration.toOver, Decoration.ofOver, ofOver_toOver A]

/--
Equivalence between:
* decorating a tree by the extended context `Γ.extend A`, and
* decorating it by `Γ` together with one `Decoration.Over A` layer.

This is the main bridge from the semantic "single realized context" view to the
staged schema/dependent-decoration view.

Concrete example:
if a schema is built as `(Spec.Node.Schema.singleton Tag).extend Data`, then
decorations of its realized context `Node.Context.extend Tag Data` are
equivalent to pairs consisting of:
* `tags : Decoration Tag spec`, and
* `datas : Decoration.Over Data spec tags`.
-/
def Decoration.equivOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w)
    (spec : Spec) :
    Equiv (Decoration (Node.Context.extend Γ A) spec)
      (Sigma fun d : Decoration Γ spec => Decoration.Over A spec d) := by
  refine
    { toFun := Decoration.toOver A spec
      invFun := fun ⟨d, r⟩ => Decoration.ofOver A spec d r
      left_inv := Decoration.ofOver_toOver A spec
      right_inv := ?_ }
  intro x
  cases x with
  | mk d r => exact Decoration.toOver_ofOver A spec d r

end Spec
end Interaction
