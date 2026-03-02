/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Tactic.TypeStar

/-!
# Heterogeneous Vectors

`HVector A as` is a heterogeneous vector: given a type family `A : α → Type*` and a list
`as : List α` of indices, it holds one value of type `A a` for each `a` in `as`.

Important universe note:

This file deliberately defines `HVector` as a nested `Prod`/`PUnit` *function* rather than
an inductive type. When the index type `α` lives in a higher universe (e.g. `ProtocolSpec.Round :
Type 1`), an inductive `HVector` would also live in that higher universe, and then values like
`Transcript pSpec` would no longer be usable as arguments to monads `m : Type → Type`. The nested
encoding keeps `HVector A l` in the universe of `A`'s codomain.
-/

/-- A heterogeneous vector indexed by a list, defined as nested products.
Marked `@[reducible]` so that `(x, xs) : HVector A (a :: as)` type-checks without casts.

The base case explicitly uses `PUnit.{v + 1}` to pin the empty-list universe to `A`'s
codomain universe, preventing universe metavariables from leaking into downstream
definitions (e.g. `Verifier.compNth`, `OracleVerifier.compNth`). -/
@[reducible] def HVector.{u, v} {α : Type u} (A : α → Type v) : List α → Type v
  | [] => PUnit.{v + 1}
  | a :: as => A a × HVector A as

namespace HVector

/-! ## Constructors and destructors -/

infixr:67 " ::ₕ " => HVector.cons

def nil {α : Type*} {A : α → Type*} : HVector A ([] : List α) := PUnit.unit

def cons {α : Type*} {A : α → Type*} {a : α} {as : List α}
    (x : A a) (xs : HVector A as) : HVector A (a :: as) := (x, xs)

infixr:67 " ::ₕ " => HVector.cons

def head {α : Type*} {A : α → Type*} {a : α} {as : List α}
    (v : HVector A (a :: as)) : A a := v.1

def tail {α : Type*} {A : α → Type*} {a : α} {as : List α}
    (v : HVector A (a :: as)) : HVector A as := v.2

/-! ## Notation -/

syntax "[" withoutPosition(term,*) "]ₕ" : term

macro_rules
  | `([ $elems,* ]ₕ) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.TSyntax `term) :
        Lean.MacroM Lean.Syntax := do
      match i, skip with
      | 0, _ => pure result
      | i + 1, true => expandListLit i false result
      | i + 1, false =>
        expandListLit i true (← ``(HVector.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(HVector.nil))
    else
      `(%[ $elems,* | List.nil ])

/-! ## Core operations -/

def get {α : Type*} {A : α → Type*} :
    (l : List α) → HVector A l → (i : Fin l.length) → A (l.get i)
  | [], _, i => i.elim0
  | _ :: _, v, ⟨0, _⟩ => v.1
  | hd :: tl, v, ⟨n + 1, h⟩ =>
    have : (hd :: tl).length = tl.length + 1 := List.length_cons
    get tl v.2 ⟨n, by omega⟩

def map {α : Type*} {A B : α → Type*} (f : ∀ (a : α), A a → B a) :
    (l : List α) → HVector A l → HVector B l
  | [], _ => PUnit.unit
  | _ :: tl, v => (f _ v.1, map f tl v.2)

def foldl {α : Type*} {A : α → Type*} {β : Type*} (f : ∀ (a : α), β → A a → β) :
    (l : List α) → β → HVector A l → β
  | [], b, _ => b
  | _ :: tl, b, v => foldl f tl (f _ b v.1) v.2

/-! ## Append -/

def append {α : Type*} {A : α → Type*} :
    {l₁ : List α} → {l₂ : List α} → HVector A l₁ → HVector A l₂ → HVector A (l₁ ++ l₂)
  | [], _, _, ys => ys
  | _ :: tl, _, v, ys => (v.1, @append _ _ tl _ v.2 ys)

instance {α : Type*} {A : α → Type*} {l₁ l₂ : List α} :
    HAppend (HVector A l₁) (HVector A l₂) (HVector A (l₁ ++ l₂)) where
  hAppend := append

/-- Append a single element to the end of the vector. -/
def snoc {α : Type*} {A : α → Type*} {a : α} {as : List α}
    (xs : HVector A as) (x : A a) : HVector A (as ++ [a]) :=
  append xs (x, PUnit.unit)

/-! ## splitAt -/

/-- Split a vector at a list-append boundary into left and right sub-vectors. -/
def splitAt {α : Type*} {A : α → Type*} :
    (l₁ : List α) → {l₂ : List α} →
    HVector A (l₁ ++ l₂) → HVector A l₁ × HVector A l₂
  | [], _, v => (PUnit.unit, v)
  | _ :: tl, _, v => let (l, r) := splitAt tl v.2; ((v.1, l), r)

/-! ## take / drop -/

/-- Keep the first `n` elements of the vector. -/
def take {α : Type*} {A : α → Type*} :
    (n : Nat) → (l : List α) → HVector A l → HVector A (l.take n)
  | 0, _, _ => PUnit.unit
  | _ + 1, [], _ => PUnit.unit
  | n + 1, _ :: tl, v => (v.1, take n tl v.2)

/-- Remove the first `n` elements of the vector. -/
def drop {α : Type*} {A : α → Type*} :
    (n : Nat) → (l : List α) → HVector A l → HVector A (l.drop n)
  | 0, _, v => v
  | _ + 1, [], _ => PUnit.unit
  | n + 1, _ :: tl, v => drop n tl v.2

/-! # Theorems -/

variable {α : Type*} {A : α → Type*}

theorem splitAt_append (l₁ l₂ : List α) (v₁ : HVector A l₁) (v₂ : HVector A l₂) :
    HVector.splitAt (A := A) l₁ (HVector.append v₁ v₂) = (v₁, v₂) := by
  induction l₁ with
  | nil =>
      simp [HVector.splitAt, HVector.append]
  | cons _ tl ih =>
      cases v₁ with
      | mk hd tlv =>
          simp [HVector.splitAt, HVector.append, ih (v₁ := tlv)]

@[simp] theorem head_cons {a : α} {as : List α}
    {x : A a} {xs : HVector A as} :
    (x ::ₕ xs).head = x := rfl

@[simp] theorem cons_append {hd : α} {tl₁ tl₂ : List α}
    (x : A hd) (v₁ : HVector A tl₁) (v₂ : HVector A tl₂) :
    HVector.cons x (HVector.append v₁ v₂) = HVector.append (HVector.cons x v₁) v₂ := rfl

@[simp] theorem tail_cons {a : α} {as : List α}
    {x : A a} {xs : HVector A as} :
    (x ::ₕ xs).tail = xs := rfl

@[simp] theorem cons_head_tail {a : α} {as : List α}
    (v : HVector A (a :: as)) :
    v.head ::ₕ v.tail = v := rfl

end HVector
