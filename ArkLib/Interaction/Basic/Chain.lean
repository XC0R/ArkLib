/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Replicate

/-!
# Dependent chains (`Spec.chain`)

State-indexed `n`-round composition: each stage’s spec may depend on a value in `Stage i`, updated
by `advance` from the current transcript. Includes `Decoration.chain`, `Refine.chain`, the
`replicate` special case (`replicate_eq_chain`), and `Strategy.chainComp`.
-/

set_option autoImplicit false

universe u v w

namespace Interaction
namespace Spec

/-- `n`-stage dependent composition: append `spec i s`, then continue in state `advance i s tr`. -/
def chain (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → Spec
  | 0, _, _ => .done
  | n + 1, i, s =>
      (spec i s).append (fun tr => chain Stage spec advance n (i + 1) (advance i s tr))

@[simp, grind =]
theorem chain_zero (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (i : Nat) (s : Stage i) :
    Spec.chain Stage spec advance 0 i s = .done := rfl

theorem chain_succ (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (n : Nat) (i : Nat) (s : Stage i) :
    Spec.chain Stage spec advance (n + 1) i s =
      (spec i s).append (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr)) :=
  rfl

/-- `replicate` is `chain` with trivial state `PUnit`. -/
theorem replicate_eq_chain (spec : Spec) (n : Nat) (i : Nat) :
    spec.replicate n = Spec.chain (fun _ => PUnit) (fun _ _ => spec)
      (fun _ _ _ => ⟨⟩) n i ⟨⟩ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [replicate, chain]
    congr 1; funext _; exact ih (i + 1)

/-- Split a chain transcript after the first stage. -/
def Transcript.chainSplit
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i) :
    Transcript (Spec.chain Stage spec advance (n + 1) i s) →
    (tr₁ : Transcript (spec i s)) ×
      Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁)) :=
  Transcript.split (spec i s)
    (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))

/-- Join first-stage and remainder transcripts for a chain. -/
def Transcript.chainJoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript (Spec.chain Stage spec advance (n + 1) i s) :=
  Transcript.join (spec i s)
    (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr)) tr₁ tr₂

@[simp, grind =]
theorem Transcript.chainSplit_chainJoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript.chainSplit n i s (Transcript.chainJoin n i s tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_join _ _ _ _

variable {S : Type u → Type v} {L : Type u → Type v} {F : ∀ X, L X → Type w}

/-- Decoration obtained by taking `deco i s` at each chain stage. -/
def Decoration.chain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (deco : (i : Nat) → (s : Stage i) → Decoration S (spec i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration S (Spec.chain Stage spec advance n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Decoration.append (deco i s)
        (fun tr => Decoration.chain deco n (i + 1) (advance i s tr))

/-- Refined decoration along a chain, fibered over `Decoration.chain`. -/
def Decoration.Refine.chain {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Refine F (spec i s) (deco i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration.Refine F (Spec.chain Stage spec advance n i s)
      (Decoration.chain deco n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Refine.append (rDeco i s)
        (fun tr => Refine.chain rDeco n (i + 1) (advance i s tr))

/-- `Refine.map` commutes with `Refine.chain`. -/
theorem Decoration.Refine.map_chain {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l)
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Refine F (spec i s) (deco i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration.Refine.map η (Spec.chain Stage spec advance n i s)
        (Decoration.chain deco n i s) (Decoration.Refine.chain rDeco n i s) =
      Decoration.Refine.chain (fun j t => Decoration.Refine.map η (spec j t) (deco j t)
        (rDeco j t)) n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [chain_succ, Decoration.chain, Decoration.Refine.chain]
      rw [Decoration.Refine.map_append η (spec i s)
            (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))
            (deco i s) (fun tr => Decoration.chain deco n (i + 1) (advance i s tr))
            (rDeco i s) (fun tr => Decoration.Refine.chain rDeco n (i + 1) (advance i s tr))]
      refine congrArg (Decoration.Refine.append (Decoration.Refine.map η (spec i s) (deco i s)
            (rDeco i s))) ?_
      funext tr
      exact Decoration.Refine.map_chain η rDeco n (i + 1) (advance i s tr)

variable {m : Type u → Type u}

/-- Compose per-stage strategies along a chain, threading a fixed output type `α`. -/
def Strategy.chainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {α : Type u}
    (step : (i : Nat) → (s : Stage i) → α →
      m (Strategy m (spec i s) (fun _ => α))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → α →
    m (Strategy m (Spec.chain Stage spec advance n i s) (fun _ => α))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    Strategy.comp (spec i s) (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))
      strat (fun tr mid => chainComp step n (i + 1) (advance i s tr) mid)

end Spec
end Interaction
