/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Basic.Strategy

/-!
# Dependent append of interaction specs

Given two interactions where the second may depend on the outcome of the first,
`Spec.append` fuses them into a single interaction. The file provides the full
algebra around this operation:

- **Transcript operations**: `Transcript.append` / `split` construct and decompose
  combined transcripts, while `Transcript.liftAppend` lifts a two-argument type family
  to a single-argument family on the combined transcript with definitional computation.
- **Strategy composition**: `Strategy.comp` (factored output via `liftAppend`) and
  `Strategy.compFlat` (flat output via `Transcript.append`).
- **Decoration / refinement append** and their naturality lemmas.
-/

universe u v w w₂

namespace Interaction
namespace Spec

/-! ## Structural combinators -/

/-- Sequential composition of interactions: run `s₁` first, then continue with
`s₂ tr₁` where `tr₁` records what happened in `s₁`. -/
def append : (s₁ : Spec) → (Transcript s₁ → Spec) → Spec
  | .done, s₂ => s₂ ⟨⟩
  | .node X rest, s₂ => .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))

/-- Lift a two-argument type family `F tr₁ tr₂` (indexed by per-phase transcripts)
to a single-argument family on the combined transcript of `s₁.append s₂`.

Crucially, `liftAppend s₁ s₂ F (Transcript.append s₁ s₂ tr₁ tr₂)` reduces
**definitionally** to `F tr₁ tr₂`, which makes this the right combinator for
stage-dependent composition (see `Strategy.comp` and `Transcript.chainFamily`). -/
def Transcript.liftAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    ((tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    Transcript (s₁.append s₂) → Type u
  | .done, _, F, tr => F ⟨⟩ tr
  | .node _ rest, s₂, F, ⟨x, tail⟩ =>
      Transcript.liftAppend (rest x) (fun p => s₂ ⟨x, p⟩)
        (fun tr₁ tr₂ => F ⟨x, tr₁⟩ tr₂) tail

/-- `liftAppend` respects pointwise equality of the family `F`. -/
theorem Transcript.liftAppend_congr :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F G : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (∀ tr₁ tr₂, F tr₁ tr₂ = G tr₁ tr₂) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ F tr = Transcript.liftAppend s₁ s₂ G tr
  | .done, _, _, _, h, tr => h ⟨⟩ tr
  | .node _ rest, s₂, _, _, h, ⟨x, tail⟩ =>
      liftAppend_congr (rest x) (fun p => s₂ ⟨x, p⟩) _ _
        (fun tr₁ tr₂ => h ⟨x, tr₁⟩ tr₂) tail

/-- A constant family is unaffected by `liftAppend`. -/
@[simp]
theorem Transcript.liftAppend_const (α : Type u) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ (fun _ _ => α) tr = α
  | .done, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail⟩ =>
      liftAppend_const α (rest x) (fun p => s₂ ⟨x, p⟩) tail

/-- Combine a first-phase transcript and a second-phase transcript into a transcript
of the composed interaction `s₁.append s₂`. -/
def Transcript.append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Transcript (s₁.append s₂)
  | .done, _, _, tr₂ => tr₂
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ =>
      ⟨x, Transcript.append (rest x) (fun p => s₂ ⟨x, p⟩) tail₁ tr₂⟩

/-- Decompose a transcript of `s₁.append s₂` into the first-phase prefix and the
second-phase continuation. Inverse of `Transcript.append`. -/
def Transcript.split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    Transcript (s₁.append s₂) → (tr₁ : Transcript s₁) × Transcript (s₂ tr₁)
  | .done, _, tr => ⟨⟨⟩, tr⟩
  | .node _ rest, s₂, ⟨x, tail⟩ =>
      let ⟨tr₁, tr₂⟩ := Transcript.split (rest x) (fun p => s₂ ⟨x, p⟩) tail
      ⟨⟨x, tr₁⟩, tr₂⟩

/-- Splitting after appending recovers the original components. -/
@[simp, grind =]
theorem Transcript.split_append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    Transcript.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩
  | .done, _, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ => by
      simp only [Transcript.append, split]; rw [split_append]

/-- Appending the components produced by `split` recovers the original transcript. -/
@[simp]
theorem Transcript.append_split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr : Transcript (s₁.append s₂)) →
    let ⟨tr₁, tr₂⟩ := Transcript.split s₁ s₂ tr
    Transcript.append s₁ s₂ tr₁ tr₂ = tr
  | .done, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail⟩ => by
      simp only [split, Transcript.append]; rw [append_split]

theorem append_done (s₂ : Transcript Spec.done → Spec) :
    Spec.done.append s₂ = s₂ ⟨⟩ := rfl

theorem append_node (X : Type u) (rest : X → Spec) (s₂ : Transcript (.node X rest) → Spec) :
    (Spec.node X rest).append s₂ =
      .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩)) := rfl

variable {m : Type u → Type u}

/-- Monadic composition of strategies along `Spec.append`.

The output type is given as a two-argument family
`F : Transcript s₁ → Transcript (s₂ tr₁) → Type u`, lifted to the combined spec
via `Transcript.liftAppend`. The continuation receives the first-phase strategy's
output and produces a second-phase strategy whose output family is `F tr₁`.

This is the preferred composition form: `liftAppend` ensures the output type
reduces definitionally when combined with `Transcript.append`, which is essential
for dependent chain composition (see `Strategy.chainComp`). -/
def Strategy.comp {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Mid : Transcript s₁ → Type u} →
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u} →
    Strategy m s₁ Mid →
    ((tr₁ : Transcript s₁) → Mid tr₁ → m (Strategy m (s₂ tr₁) (F tr₁))) →
    m (Strategy m (s₁.append s₂) (Transcript.liftAppend s₁ s₂ F))
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      comp (rest x) (fun p => s₂ ⟨x, p⟩) next
        (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Monadic composition of strategies along `Spec.append` with a single output family
`Output` on the combined transcript. The continuation indexes into `Output` via
`Transcript.append`.

Use this when the output type is naturally expressed over the combined transcript
rather than as a two-argument family (e.g., constant output types, or when working
with `Strategy.iterate`). See also `Strategy.comp`. -/
def Strategy.compFlat {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Mid : Transcript s₁ → Type u} →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m s₁ Mid →
    ((tr₁ : Transcript s₁) → Mid tr₁ →
      m (Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.append s₁ s₂ tr₁ tr₂)))) →
    m (Strategy m (s₁.append s₂) Output)
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      compFlat (rest x) (fun p => s₂ ⟨x, p⟩) next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Extract the first-phase strategy from a strategy on a composed interaction.
At each first-phase transcript `tr₁`, the remainder is the second-phase strategy
with output indexed by `Transcript.append`. -/
def Strategy.splitPrefix {m : Type u → Type u} [Functor m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m (s₁.append s₂) Output →
    Strategy m s₁ (fun tr₁ =>
      Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.append s₁ s₂ tr₁ tr₂)))
  | .done, _, _, p => p
  | .node _ rest, s₂, _, ⟨x, cont⟩ =>
      ⟨x, (splitPrefix (rest x) (fun p => s₂ ⟨x, p⟩) ·) <$> cont⟩

/-- Concatenate per-node labels along `Spec.append`. -/
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

/-- Concatenate refinement layers along `Spec.append`, over appended base decorations. -/
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

end Spec
end Interaction
