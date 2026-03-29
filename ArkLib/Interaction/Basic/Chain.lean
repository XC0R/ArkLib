/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Replicate

/-!
# Dependent chains (`Spec.chain`)

An `n`-stage state-indexed composition: at each stage `i`, the interaction is `spec i s`
where `s : Stage i` is the current state. After the stage completes with transcript `tr`,
the state advances to `advance i s tr : Stage (i + 1)`.

This file provides the spec-level chain (`Spec.chain`), a transcript telescope type
(`Transcript.chain`), flattening operations (`Transcript.join` / `unjoin`), type-level
lifting (`Transcript.liftJoin`, `Transcript.chainFamily`), decorations, and strategy
composition along chains.
-/

universe u v w

namespace Interaction
namespace Spec

/-- `n`-stage dependent composition: run `spec i s`, then advance to state
`advance i s tr` and repeat for `n` total stages. -/
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

/-- Decompose a `(n+1)`-stage chain transcript into the first-stage transcript and
the remainder. Specialization of `Transcript.split` to the chain structure. -/
def Transcript.chainSplit
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i) :
    Transcript (Spec.chain Stage spec advance (n + 1) i s) →
    (tr₁ : Transcript (spec i s)) ×
      Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁)) :=
  Transcript.split (spec i s)
    (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))

/-- Combine a first-stage transcript with a remainder chain transcript into a
`(n+1)`-stage chain transcript. Specialization of `Transcript.append` to chains. -/
def Transcript.chainAppend
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript (Spec.chain Stage spec advance (n + 1) i s) :=
  Transcript.append (spec i s)
    (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr)) tr₁ tr₂

/-- Splitting after appending at the chain level recovers the components. -/
@[simp, grind =]
theorem Transcript.chainSplit_chainAppend
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript.chainSplit n i s (Transcript.chainAppend n i s tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_append _ _ _ _

/-! ## N-ary transcript operations -/

/-- Dependent telescope of per-stage transcripts: a sequence of individual-stage
transcripts where each stage determines the next via `advance`. Mirrors `Spec.chain`
at the transcript level. -/
def Transcript.chain (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Type u
  | 0, _, _ => PUnit
  | n + 1, i, s =>
      (tr : Transcript (spec i s)) ×
        Transcript.chain Stage spec advance n (i + 1) (advance i s tr)

/-- Flatten a transcript telescope into the combined chain transcript, concatenating
each per-stage transcript via `Transcript.chainAppend`. The n-ary analog of
`Transcript.append`, mirroring `List.join`. -/
def Transcript.join (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Transcript.chain Stage spec advance n i s →
    Transcript (Spec.chain Stage spec advance n i s)
  | 0, _, _, _ => ⟨⟩
  | n + 1, i, s, ⟨tr₁, rest⟩ =>
      Transcript.chainAppend n i s tr₁
        (Transcript.join Stage spec advance n (i + 1) (advance i s tr₁) rest)

/-- Decompose a combined chain transcript into a telescope of per-stage transcripts.
Inverse of `Transcript.join`. -/
def Transcript.unjoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Transcript (Spec.chain Stage spec advance n i s) →
    Transcript.chain Stage spec advance n i s
  | 0, _, _, _ => ⟨⟩
  | n + 1, i, s, tr =>
      let ⟨tr₁, trRest⟩ := Transcript.chainSplit n i s tr
      ⟨tr₁, Transcript.unjoin Stage spec advance n (i + 1) (advance i s tr₁) trRest⟩

/-- `unjoin` after `join` is the identity on telescope transcripts. -/
@[simp]
theorem Transcript.unjoin_join
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)} :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (trs : Transcript.chain Stage spec advance n i s) →
    Transcript.unjoin Stage spec advance n i s
      (Transcript.join Stage spec advance n i s trs) = trs
  | 0, _, _, ⟨⟩ => rfl
  | n + 1, i, s, ⟨tr₁, rest⟩ => by
      dsimp only [Transcript.join, Transcript.unjoin]
      rw [chainSplit_chainAppend]; dsimp only []
      rw [unjoin_join]

/-- `join` after `unjoin` is the identity on combined chain transcripts. -/
@[simp]
theorem Transcript.join_unjoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)} :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (tr : Transcript (Spec.chain Stage spec advance n i s)) →
    Transcript.join Stage spec advance n i s
      (Transcript.unjoin Stage spec advance n i s tr) = tr
  | 0, _, _, ⟨⟩ => rfl
  | n + 1, i, s, tr => by
      dsimp only [Transcript.unjoin, Transcript.join]
      rw [join_unjoin n (i + 1)]
      exact Transcript.append_split _ _ tr

/-- Lift a family indexed by the transcript telescope to a family on the combined
chain transcript. Uses `Transcript.liftAppend` at each stage, ensuring that
`liftJoin ... F (join ... trs)` reduces **definitionally** to `F trs`. -/
def Transcript.liftJoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (Transcript.chain Stage spec advance n i s → Type u) →
    Transcript (Spec.chain Stage spec advance n i s) → Type u
  | 0, _, _, F, _ => F ⟨⟩
  | n + 1, i, s, F, tr =>
      Transcript.liftAppend (spec i s)
        (fun tr₁ => Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))
        (fun tr₁ trRest =>
          Transcript.liftJoin Stage spec advance n (i + 1) (advance i s tr₁)
            (fun rest => F ⟨tr₁, rest⟩) trRest)
        tr

variable {S : Type u → Type v} {L : Type u → Type v} {F : ∀ X, L X → Type w}

/-- Per-node labels along a chain: at each stage, use `deco i s`. -/
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

/-- Refinement layer along a chain, fibered over `Decoration.chain`. -/
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

/-! ## Chain families -/

/-- The output type of chain composition. Given a per-stage family `Family i s`, this
computes the type at the terminal stage by threading through `Transcript.liftAppend`
at each step. Reduces **definitionally** when the transcript is built via
`Transcript.append`, avoiding Nat-arithmetic casts.

This is the canonical output type for `Strategy.chainComp` and `Counterpart.chainComp`. -/
def Transcript.chainFamily
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Transcript (Spec.chain Stage spec advance n i stage) → Type u
  | 0, i, stage, _ => Family i stage
  | n + 1, i, stage, tr =>
      Transcript.liftAppend (spec i stage)
        (fun tr₁ => Spec.chain Stage spec advance n (i + 1) (advance i stage tr₁))
        (fun tr₁ trRest => Transcript.chainFamily Family n (i + 1) (advance i stage tr₁) trRest)
        tr

@[simp]
theorem Transcript.chainFamily_zero
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u) (i : Nat) (s : Stage i) (tr : PUnit) :
    Transcript.chainFamily (advance := advance) Family 0 i s tr = Family i s := rfl

/-- A constant family is unaffected by `chainFamily`. -/
theorem Transcript.chainFamily_const
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (α : Type u) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (tr : Transcript (Spec.chain Stage spec advance n i s)) →
    Transcript.chainFamily (advance := advance) (fun _ _ => α) n i s tr = α
  | 0, _, _, _ => rfl
  | n + 1, i, s, tr => by
      simp only [Transcript.chainFamily]
      rw [Transcript.liftAppend_congr (spec i s) _ _ _
        (fun tr₁ trR => Transcript.chainFamily_const α n (i + 1) (advance i s tr₁) trR)]
      exact Transcript.liftAppend_const α (spec i s) _ tr

/-! ## Strategy composition along chains -/

variable {m : Type u → Type u}

/-- Compose per-stage strategies along a chain. At each stage, the step function
transforms `Family i s` into a strategy whose output is `Family (i+1) (advance i s tr)`.
The full chain output is `Transcript.chainFamily Family`. -/
def Strategy.chainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (Strategy m (spec i s) (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (Strategy m (Spec.chain Stage spec advance n i s)
      (Transcript.chainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    Strategy.comp (spec i s)
      (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))
      strat (fun tr mid => chainComp step n (i + 1) (advance i s tr) mid)

/-- Uniform `Strategy.chainComp` with a fixed output type `α` at every stage. -/
def Strategy.chainCompUniform {m : Type u → Type u} [Monad m]
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
    Strategy.compFlat (spec i s)
      (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))
      strat (fun tr mid => chainCompUniform step n (i + 1) (advance i s tr) mid)

end Spec
end Interaction
