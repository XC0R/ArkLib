/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Basic.Strategy

/-!
# Dependent append of specs, transcripts, decorations, and strategies

`Spec.append` concatenates a first interaction with a second that may depend on the transcript of
the first. This file defines `Transcript.join` / `split`, `Strategy.comp`, decoration/refinement
append, and naturality lemmas used throughout `Replicate` and `Chain`.
-/

universe u v w w₂

namespace Interaction
namespace Spec

/-! ## Structural combinators -/

/-- Dependent append: after completing `s₁`, continue with `s₂ tr` where `tr` is the transcript of
`s₁`. -/
def append : (s₁ : Spec) → (Transcript s₁ → Spec) → Spec
  | .done, s₂ => s₂ ⟨⟩
  | .node X rest, s₂ => .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))

/-- Concatenate transcripts for an appended spec. -/
def Transcript.join :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Transcript (s₁.append s₂)
  | .done, _, _, tr₂ => tr₂
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ =>
      ⟨x, Transcript.join (rest x) (fun p => s₂ ⟨x, p⟩) tail₁ tr₂⟩

/-- Split a transcript of `s₁.append s₂` into the `s₁` prefix and the `s₂` continuation. -/
def Transcript.split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    Transcript (s₁.append s₂) → (tr₁ : Transcript s₁) × Transcript (s₂ tr₁)
  | .done, _, tr => ⟨⟨⟩, tr⟩
  | .node _ rest, s₂, ⟨x, tail⟩ =>
      let ⟨tr₁, tr₂⟩ := Transcript.split (rest x) (fun p => s₂ ⟨x, p⟩) tail
      ⟨⟨x, tr₁⟩, tr₂⟩

variable {m : Type u → Type u}

/-- Dependent Kleisli composition of strategies along `append`. -/
def Strategy.comp {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Mid : Transcript s₁ → Type u} →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m s₁ Mid →
    ((tr₁ : Transcript s₁) → Mid tr₁ →
      m (Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.join s₁ s₂ tr₁ tr₂)))) →
    m (Strategy m (s₁.append s₂) Output)
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      comp (rest x) (fun p => s₂ ⟨x, p⟩) next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- First-stage view of a strategy on an appended spec (path-dependent remainder type). -/
def Strategy.splitPrefix {m : Type u → Type u} [Functor m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m (s₁.append s₂) Output →
    Strategy m s₁ (fun tr₁ =>
      Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.join s₁ s₂ tr₁ tr₂)))
  | .done, _, _, p => p
  | .node _ rest, s₂, _, ⟨x, cont⟩ =>
      ⟨x, (splitPrefix (rest x) (fun p => s₂ ⟨x, p⟩) ·) <$> cont⟩

/-- Append label decorations along `Spec.append`. -/
def Decoration.append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    (d₁ : Decoration S s₁)
    (d₂ : (tr₁ : Transcript s₁) → Decoration S (s₂ tr₁)) :
    Decoration S (s₁.append s₂) :=
  match s₁, d₁ with
  | .done, _ => d₂ ⟨⟩
  | .node _ _, ⟨s, dRest⟩ =>
      ⟨s, fun x => Decoration.append (dRest x)
        (fun p => d₂ ⟨x, p⟩)⟩

/-- Append refinements over appended base decorations. -/
def Decoration.Refine.append {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {d₁ : Decoration L s₁}
    {d₂ : (tr₁ : Transcript s₁) → Decoration L (s₂ tr₁)}
    (r₁ : Decoration.Refine F s₁ d₁)
    (r₂ : (tr₁ : Transcript s₁) → Decoration.Refine F (s₂ tr₁) (d₂ tr₁)) :
    Decoration.Refine F (s₁.append s₂) (d₁.append d₂) :=
  match s₁, d₁, r₁ with
  | .done, _, _ => r₂ ⟨⟩
  | .node _ _, ⟨_, _⟩, ⟨fData, rRest⟩ =>
      ⟨fData, fun x => Refine.append (rRest x) (fun p => r₂ ⟨x, p⟩)⟩

/-- `Decoration.Refine.map` commutes with `Refine.append`. -/
theorem Decoration.Refine.map_append {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (d₁ : Decoration L s₁) →
    (d₂ : (tr₁ : Transcript s₁) → Decoration L (s₂ tr₁)) →
    (r₁ : Decoration.Refine F s₁ d₁) →
    (r₂ : (tr₁ : Transcript s₁) → Decoration.Refine F (s₂ tr₁) (d₂ tr₁)) →
    Decoration.Refine.map η (s₁.append s₂) (d₁.append d₂) (Refine.append r₁ r₂) =
      Refine.append (Refine.map η s₁ d₁ r₁)
        (fun tr₁ => Refine.map η (s₂ tr₁) (d₂ tr₁) (r₂ tr₁))
  | .done, _, _, _, r₁, r₂ => rfl
  | .node X rest, s₂, ⟨l, dRest⟩, d₂, ⟨fData, rRest⟩, r₂ => by
      simp only [Spec.append, Decoration.append, Decoration.Refine.append, Decoration.Refine.map]
      congr 1; funext x
      exact map_append η (rest x) (fun p => s₂ ⟨x, p⟩) (dRest x) (fun p => d₂ ⟨x, p⟩)
        (rRest x) (fun p => r₂ ⟨x, p⟩)

/-- `Decoration.map` commutes with `Decoration.append`. -/
theorem Decoration.map_append {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (d₁ : Decoration S s₁) →
    (d₂ : (tr₁ : Transcript s₁) → Decoration S (s₂ tr₁)) →
    Decoration.map f (s₁.append s₂) (d₁.append d₂) =
      (Decoration.map f s₁ d₁).append (fun tr₁ => Decoration.map f (s₂ tr₁) (d₂ tr₁))
  | .done, _, _, _ => rfl
  | .node X rest, s₂, ⟨s, dRest⟩, d₂ => by
      simp only [Spec.append, Decoration.append, Decoration.map]
      congr 1; funext x
      exact map_append f (rest x) (fun p => s₂ ⟨x, p⟩) (dRest x) (fun p => d₂ ⟨x, p⟩)

@[simp, grind =]
theorem Transcript.split_join :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    Transcript.split s₁ s₂ (Transcript.join s₁ s₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩
  | .done, _, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ => by
      simp only [join, split]; rw [split_join]

@[simp]
theorem Transcript.join_split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr : Transcript (s₁.append s₂)) →
    let ⟨tr₁, tr₂⟩ := Transcript.split s₁ s₂ tr
    Transcript.join s₁ s₂ tr₁ tr₂ = tr
  | .done, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail⟩ => by
      simp only [split, join]; rw [join_split]

theorem append_done (s₂ : Transcript Spec.done → Spec) :
    Spec.done.append s₂ = s₂ ⟨⟩ := rfl

theorem append_node (X : Type u) (rest : X → Spec) (s₂ : Transcript (.node X rest) → Spec) :
    (Spec.node X rest).append s₂ =
      .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩)) := rfl

end Spec
end Interaction
