/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec

/-!
# Decorations and displayed decorations (`Refine`)

A `Spec.Decoration S spec` attaches `S`-structure at each internal node. `Decoration.Refine` is the
dependent (displayed) variant: fibers may depend on the label drawn from an existing decoration.

Functorial `map` / `map_id` / `map_comp` for both layers are in this file. Composition along
`Spec.append` is in `ArkLib.Interaction.Basic.Append`.
-/

set_option autoImplicit false

universe u v w w₂

namespace Interaction
namespace Spec

variable {S : Type u → Type v} {T : Type u → Type w} {L : Type u → Type v}

/-- Decorate each internal node with `S X` at the node labeled by move type `X`. -/
def Decoration (S : Type u → Type v) : Spec → Type (max u v)
  | .done => PUnit
  | .node X rest => S X × (∀ x, Decoration S (rest x))

/-- Natural transformation between per-node decorations, applied recursively. -/
def Decoration.map {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (spec : Spec) → Decoration S spec → Decoration T spec
  | .done, _ => ⟨⟩
  | .node X rest, ⟨s, dRest⟩ => ⟨f X s, fun x => Decoration.map f (rest x) (dRest x)⟩

@[simp, grind =]
theorem Decoration.map_id {S : Type u → Type v} :
    (spec : Spec) → (d : Decoration S spec) →
    Decoration.map (fun X (s : S X) => s) spec d = d
  | .done, _ => rfl
  | .node _ rest, ⟨s, dRest⟩ => by
      simp only [Decoration.map]; congr 1; funext x; exact map_id (rest x) (dRest x)

theorem Decoration.map_comp {S : Type u → Type v} {T : Type u → Type w} {U : Type u → Type w₂}
    (g : ∀ X, T X → U X) (f : ∀ X, S X → T X) :
    (spec : Spec) → (d : Decoration S spec) →
    Decoration.map g spec (Decoration.map f spec d) =
      Decoration.map (fun X => g X ∘ f X) spec d
  | .done, _ => rfl
  | .node _ rest, ⟨s, dRest⟩ => by
      simp only [Decoration.map]; congr 1; funext x
      exact map_comp g f (rest x) (dRest x)

/-- Refined decoration over `d : Decoration L spec`: at each node, data in `F X l` where `l` is
the label from `d`, plus recursive refinements on subtrees. -/
def Decoration.Refine {L : Type u → Type v} (F : ∀ X, L X → Type w) :
    (spec : Spec) → Decoration L spec → Type (max u w)
  | .done, _ => PUnit
  | .node X rest, ⟨l, dRest⟩ =>
      F X l × (∀ x, Decoration.Refine F (rest x) (dRest x))

/-- Fiberwise map between refinement type families over the same base decoration. -/
def Decoration.Refine.map {L : Type u → Type v}
    {F : ∀ X, L X → Type w} {G : ∀ X, L X → Type w}
    (f : ∀ X l, F X l → G X l) :
    (spec : Spec) → (d : Decoration L spec) →
    Decoration.Refine F spec d → Decoration.Refine G spec d
  | .done, _, _ => ⟨⟩
  | .node X rest, ⟨l, dRest⟩, ⟨fData, rRest⟩ =>
      ⟨f X l fData, fun x => Refine.map f (rest x) (dRest x) (rRest x)⟩

@[simp, grind =]
theorem Decoration.Refine.map_id {L : Type u → Type v} {F : ∀ X, L X → Type w} :
    (spec : Spec) → (d : Decoration L spec) → (r : Decoration.Refine F spec d) →
    Decoration.Refine.map (fun _ _ x => x) spec d r = r
  | .done, _, _ => rfl
  | .node _ rest, ⟨l, dRest⟩, ⟨fd, rr⟩ => by
      simp only [Decoration.Refine.map]; congr 1; funext x
      exact map_id (rest x) (dRest x) (rr x)

theorem Decoration.Refine.map_comp {L : Type u → Type v}
    {F G H : ∀ X, L X → Type w}
    (g : ∀ X l, G X l → H X l) (f : ∀ X l, F X l → G X l) :
    (spec : Spec) → (d : Decoration L spec) → (r : Decoration.Refine F spec d) →
    Decoration.Refine.map g spec d (Decoration.Refine.map f spec d r) =
      Decoration.Refine.map (fun X l => g X l ∘ f X l) spec d r
  | .done, _, _ => rfl
  | .node _ rest, ⟨l, dRest⟩, ⟨fd, rr⟩ => by
      simp only [Decoration.Refine.map]; congr 1; funext x
      exact map_comp g f (rest x) (dRest x) (rr x)

end Spec
end Interaction
