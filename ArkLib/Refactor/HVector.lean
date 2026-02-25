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

Ported from lean-mlir's `LeanMLIR.HVector`, dropping Qq/meta dependencies and adding
`snoc`, `splitAt`, `take`, `drop`, and additional simp lemmas needed for the IOP refactor.
-/

universe u v

/-- A heterogeneous vector indexed by a list. -/
inductive HVector {α : Type*} (A : α → Type*) : List α → Type _
  | nil : HVector A []
  | cons {a : α} : (A a) → HVector A as → HVector A (a :: as)

namespace HVector

variable {α : Type u} {A B : α → Type*} {a : α} {as bs : List α}

/-!
## Core operations
-/

protected instance decidableEq [∀ a, DecidableEq (A a)] :
    ∀ {l : List α}, DecidableEq (HVector A l)
  | _, .nil, .nil => isTrue rfl
  | _, .cons x₁ v₁, .cons x₂ v₂ =>
    letI d := HVector.decidableEq v₁ v₂
    decidable_of_iff (x₁ = x₂ ∧ v₁ = v₂) (by simp)

def head : HVector A (a :: as) → A a
  | .cons x _ => x

def tail : HVector A (a :: as) → HVector A as
  | .cons _ xs => xs

def get : HVector A as → (i : Fin as.length) → A (as.get i)
  | .nil, i => i.elim0
  | .cons x _, ⟨0, _⟩ => x
  | .cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, Nat.succ_lt_succ_iff.mp h⟩

def map (f : ∀ (a : α), A a → B a) :
    ∀ {l : List α}, HVector A l → HVector B l
  | [], .nil => .nil
  | _ :: _, .cons a as => .cons (f _ a) (map f as)

def mapM [Monad m] {α : Type} {A : α → Type} {B : α → Type}
    (f : ∀ (a : α), A a → m (B a)) :
    ∀ {l : List α}, HVector A l → m (HVector B l)
  | [], .nil => return .nil
  | t :: _, .cons a as => do return HVector.cons (← f t a) (← HVector.mapM f as)

def foldl {B : Type*} (f : ∀ (a : α), B → A a → B) :
    ∀ {l : List α}, B → HVector A l → B
  | [], b, .nil => b
  | _ :: _, b, .cons a as => foldl f (f _ b a) as

def foldr {β : Type*} (f : ∀ (a : α), A a → β → β) :
    ∀ {l : List α}, (init : β) → HVector A l → β
  | [], b, .nil => b
  | _ :: _, b, .cons a as => f _ a (foldr f b as)

/-!
## Notation
-/

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

infixr:50 " ::ₕ " => HVector.cons

/-!
## ToTupleType
-/

def ToTupleType (A : α → Type*) : List α → Type _
  | [] => PUnit
  | [a] => A a
  | a :: as => A a × ToTupleType A as

def toTuple : HVector A as → ToTupleType A as
  | .nil => ⟨⟩
  | .cons x .nil => x
  | .cons x₁ (.cons x₂ xs) => (x₁, (cons x₂ xs).toTuple)

abbrev toSingle : HVector A [a₁] → A a₁ := toTuple
abbrev toPair : HVector A [a₁, a₂] → A a₁ × A a₂ := toTuple
abbrev toTriple : HVector A [a₁, a₂, a₃] → A a₁ × A a₂ × A a₃ := toTuple

/-!
## ofFn
-/

def ofFn (A : α → Type _) (as : List α) (f : (i : Fin as.length) → A as[i]) :
    HVector A as :=
  match as with
  | [] => .nil
  | _ :: as => f (0 : Fin (_ + 1)) ::ₕ ofFn A as (fun i => f i.succ)

/-!
## Append
-/

def append : HVector A as → HVector A bs → HVector A (as ++ bs)
  | .nil, ys => ys
  | x ::ₕ xs, ys => x ::ₕ (append xs ys)

instance : HAppend (HVector A as) (HVector A bs) (HVector A (as ++ bs)) where
  hAppend := append

/-!
## snoc (append single element at end)
-/

def snoc (xs : HVector A as) (x : A a) : HVector A (as ++ [a]) :=
  append xs (.cons x .nil)

/-!
## splitAt
-/

def splitAt : ∀ (l₁ : List α) {l₂ : List α}, HVector A (l₁ ++ l₂) → HVector A l₁ × HVector A l₂
  | [], _, v => (.nil, v)
  | _ :: _, _, .cons x xs =>
    let (left, right) := splitAt _ xs
    (.cons x left, right)

/-!
## take / drop
-/

def take : ∀ (n : Nat) {l : List α}, HVector A l → HVector A (l.take n)
  | 0, _, _ => .nil
  | _ + 1, [], .nil => .nil
  | n + 1, _ :: _, .cons x xs => .cons x (take n xs)

def drop : ∀ (n : Nat) {l : List α}, HVector A l → HVector A (l.drop n)
  | 0, _, v => v
  | _ + 1, [], .nil => .nil
  | n + 1, _ :: _, .cons _ xs => drop n xs

/-!
## length / isEmpty
-/

def length (_ : HVector A as) : Nat := as.length

def isEmpty : HVector A as → Bool
  | .nil => true
  | .cons _ _ => false

/-!
## Repr
-/

instance [∀ a, Repr (A a)] : Repr (HVector A as) where
  reprPrec xs _ :=
    let elems := xs.map (fun _ x => s!"{repr x}") |>.foldl (fun _ _ s => s) "" -- placeholder
    f!"[HVector ...]"

/-!
# Theorems
-/

/-! ## get -/

@[simp] theorem cons_get_zero {e : A a} {vec : HVector A as} :
    (HVector.cons e vec).get (@OfNat.ofNat (Fin (as.length + 1)) 0 Fin.instOfNat) = e :=
  rfl

@[simp] theorem cons_get_succ {e : A a} {vec : HVector A as} {i : Fin as.length} :
    (HVector.cons e vec).get i.succ = vec.get i :=
  rfl

/-! ## map -/

@[simp] theorem map_nil {f : (a : α) → A a → B a} :
    map f (.nil) = .nil := rfl

@[simp] theorem map_cons {f : (a : α) → A a → B a}
    {x : A a} {xs : HVector A as} :
    map f (cons x xs) = cons (f _ x) (map f xs) := by
  induction xs <;> simp_all [map]

theorem map_map {C : α → Type*} {l : List α} (t : HVector A l)
    (f : ∀ a, A a → B a) (g : ∀ a, B a → C a) :
    (t.map f).map g = t.map (fun a v => g a (f a v)) := by
  induction t <;> simp_all [map]

@[simp] theorem get_map (xs : HVector A as) (f : (a : α) → A a → B a) :
    (xs.map f).get i = f _ (xs.get i) := by
  induction xs with
  | nil => exact i.elim0
  | cons x xs ih =>
    cases i using Fin.succRecOn
    · rfl
    · simp_all [map]

/-! ## foldl -/

@[simp] theorem foldl_cons {f : ∀ (a : α), β → A a → β} {b : β}
    {x : A a} {xs : HVector A as} :
    foldl f b (cons x xs) = foldl f (f _ b x) xs := rfl

/-! ## ofFn -/

@[simp] theorem ofFn_nil : ofFn A [] f = .nil := rfl

@[simp] theorem get_ofFn {f : (i : Fin as.length) → A as[i]} :
    (ofFn A as f).get i = f i := by
  induction as with
  | nil => exact i.elim0
  | cons _ _ ih =>
    cases i using Fin.succRec
    · rfl
    · simp [ofFn, ih]

/-! ## append -/

@[simp] theorem append_eq {xs : HVector A as} {ys : HVector A bs} :
    append xs ys = xs ++ ys := rfl

@[simp] theorem nil_append {ys : HVector A bs} : (.nil : HVector A []) ++ ys = ys := rfl

@[simp] theorem cons_append {x : A a} {xs : HVector A as} {ys : HVector A bs} :
    (x ::ₕ xs) ++ ys = (x ::ₕ (xs ++ ys)) := rfl

/-! ## splitAt -/

@[simp] theorem splitAt_nil {v : HVector A l₂} :
    splitAt ([] : List α) v = (.nil, v) := rfl

@[simp] theorem splitAt_fst_append {xs : HVector A as} {ys : HVector A bs} :
    (splitAt as (xs ++ ys)).1 = xs := by
  induction xs with
  | nil => simp [splitAt]
  | cons x xs ih => simp [splitAt, ih]

@[simp] theorem splitAt_snd_append {xs : HVector A as} {ys : HVector A bs} :
    (splitAt as (xs ++ ys)).2 = ys := by
  induction xs with
  | nil => simp [splitAt]
  | cons x xs ih => simp [splitAt, ih]

/-! ## take -/

@[simp] theorem take_zero {v : HVector A l} : take 0 v = .nil := rfl

@[simp] theorem take_nil {n : Nat} : take n (.nil : HVector A []) = .nil := by
  cases n <;> rfl

@[simp] theorem take_cons_succ {x : A a} {xs : HVector A as} :
    take (n + 1) (.cons x xs) = .cons x (take n xs) := rfl

/-! ## drop -/

@[simp] theorem drop_zero {v : HVector A l} : drop 0 v = v := rfl

@[simp] theorem drop_nil {n : Nat} : drop n (.nil : HVector A []) = .nil := by
  cases n <;> rfl

@[simp] theorem drop_cons_succ {x : A a} {xs : HVector A as} :
    drop (n + 1) (.cons x xs) = drop n xs := rfl

/-! ## ext -/

@[ext] theorem ext {xs ys : HVector A as}
    (h : ∀ i, xs.get i = ys.get i) : xs = ys := by
  induction xs <;> cases ys
  case nil => rfl
  case cons ih _ _ =>
    specialize ih (fun i => by simpa using h i.succ)
    specialize h (0 : Fin <| _ + 1)
    simp_all

/-! ## head / tail -/

@[simp] theorem head_cons {x : A a} {xs : HVector A as} :
    (x ::ₕ xs).head = x := rfl

@[simp] theorem tail_cons {x : A a} {xs : HVector A as} :
    (x ::ₕ xs).tail = xs := rfl

@[simp] theorem cons_head_tail {v : HVector A (a :: as)} :
    v.head ::ₕ v.tail = v := by
  cases v; rfl

/-! ## snoc -/

@[simp] theorem snoc_nil {x : A a} :
    (.nil : HVector A []).snoc x = .cons x .nil := rfl

end HVector
