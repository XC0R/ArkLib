/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.PolyUtils
import CompPoly.Multivariate.Rename
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Partial Evaluation and Domain Summation for CMvPolynomial

Computable operations on multivariate polynomials for symbolic sumcheck:

- `partialEvalFirst` / `partialEvalLast` — fix the first/last variable to a scalar
- `sumOverLast` — sum out the last variable over a finite domain
- `toUnivariate` — convert a 1-variable polynomial to `CPolynomial`
- `sumAllButFirst` — iterate `sumOverLast` to sum all but variable 0
- `roundPoly` — compute the round polynomial (variable 0 free, rest summed)

All definitions are computable and cast-free. Correctness lemmas relate the computable
definitions to `CMvPolynomial.eval` and `CPolynomial.eval`.
-/

open CompPoly CPoly Std

attribute [local instance] instDecidableEqOfLawfulBEq

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-! ## Core primitives -/

/-- Fix variable 0 of a multivariate polynomial to a scalar value `a`.
For each term `c · X₀^e₀ · X₁^e₁ · ⋯ · Xₙ^eₙ`, produces
`(c · a^e₀) · X₀^e₁ · ⋯ · Xₙ₋₁^eₙ`. -/
def partialEvalFirst (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  ExtTreeMap.foldl (fun acc mono c =>
    acc + monomial (Vector.ofFn fun j : Fin n => mono.get j.succ) (c * a ^ mono.get 0))
    0 p.1

/-- Fix the last variable of a multivariate polynomial to a scalar value `a`.
For each term `c · X₀^e₀ · ⋯ · Xₙ^eₙ`, produces
`(c · a^eₙ) · X₀^e₀ · ⋯ · Xₙ₋₁^eₙ₋₁`. -/
def partialEvalLast (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  ExtTreeMap.foldl (fun acc mono c =>
    acc + monomial (Vector.ofFn fun j : Fin n => mono.get j.castSucc)
      (c * a ^ mono.get (Fin.last n)))
    0 p.1

variable {m : ℕ}

/-- Sum out the last variable of a polynomial over domain `D`.
Defined as `∑ d ∈ D, partialEvalLast d p` — the innermost sumcheck equation. -/
def sumOverLast (D : Fin m → R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  (Finset.univ : Finset (Fin m)).sum (fun j => partialEvalLast (D j) p)

/-! ## Conversion to univariate -/

/-- Convert a single-variable multivariate polynomial to a univariate `CPolynomial`.
Each term `c · X₀^e` maps to `c · X^e`. -/
def toUnivariate (p : CMvPolynomial 1 R) : CPolynomial R :=
  ExtTreeMap.foldl (fun acc mono c =>
    acc + CPolynomial.monomial (mono.get 0) c) 0 p.1

/-! ## Composed operations -/

/-- Extend a valuation on the remaining variables with a fixed prefix. -/
def prefixPoint : ∀ {i n : ℕ}, Vector R i → (Fin n → R) → Fin (n + i) → R
  | 0, _, _, v => v
  | i + 1, _, fixed, v =>
      Fin.cons (fixed.get 0) (prefixPoint (Vector.ofFn fun j : Fin i => fixed.get j.succ) v)

omit [CommSemiring R] [BEq R] [LawfulBEq R] in
/-- Characterization of `prefixPoint`: for `x.1 < i` it returns `fixed[x]`,
otherwise it returns `v` at the shifted index. -/
theorem prefixPoint_spec {i n : ℕ} (fixed : Vector R i) (v : Fin n → R) (x : Fin (n + i)) :
    prefixPoint fixed v x =
      if h : x.1 < i then fixed.get ⟨x.1, h⟩
      else v ⟨x.1 - i, by omega⟩ := by
  induction i generalizing v with
  | zero => simp [prefixPoint]
  | succ i ih =>
      cases x using Fin.cases with
      | zero => simp [prefixPoint]
      | succ x =>
          by_cases hx : x.1 < i
          · have hx' : x.succ.1 < i + 1 := by
              simpa using Nat.succ_lt_succ hx
            simpa [prefixPoint, hx, hx', Vector.get_ofFn] using
              (ih (Vector.ofFn fun j : Fin i => fixed.get j.succ) v x)
          · have hx' : ¬ x.succ.1 < i + 1 := fun h => hx (Nat.lt_of_succ_lt_succ h)
            simp only [prefixPoint, Fin.cons_succ, dif_neg hx']
            rw [ih, dif_neg hx]
            congr 1; ext; simp [Fin.val_succ]

/-- Iteratively fix the first `i` variables of a polynomial according to `fixed`. -/
def partialEvalPrefix : ∀ {i n : ℕ}, Vector R i → CMvPolynomial (n + i) R → CMvPolynomial n R
  | 0, _, _, p => p
  | i + 1, n, fixed, p =>
      partialEvalPrefix (n := n) (Vector.ofFn fun j : Fin i => fixed.get j.succ)
        (partialEvalFirst (fixed.get 0) p)

/-- Iterate `sumOverLast` to sum out all variables except variable 0.
`sumAllButFirst D k p` takes a polynomial in `k + 1` variables, keeps variable 0 free,
and sums variables 1 through k over domain `D`.

Type arithmetic is definitional: `(k + 1) + 1` reduces to `succ (k + 1)` by `Nat.add`. -/
def sumAllButFirst (D : Fin m → R) : (k : ℕ) → CMvPolynomial (k + 1) R → CMvPolynomial 1 R
  | 0, p => p
  | k + 1, p => sumAllButFirst D k (sumOverLast D p)

/-- Compute the round polynomial from a "current" multivariate polynomial.
Variable 0 is the free variable; variables 1 through k are summed over D.
Returns a univariate `CPolynomial`. -/
def roundPoly (D : Fin m → R) (k : ℕ) (p : CMvPolynomial (k + 1) R) : CPolynomial R :=
  toUnivariate (sumAllButFirst D k p)

/-! ## Correctness lemmas

These relate the computable operations to `CMvPolynomial.eval` and `CPolynomial.eval`,
establishing that the symbolic operations faithfully implement partial evaluation. -/

/-- `partialEvalFirst a p` correctly implements partial evaluation:
evaluating the result at `v` equals evaluating `p` at `Fin.cons a v`. -/
theorem partialEvalFirst_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalFirst a p).eval v = p.eval (Fin.cons a v) := by
  simp only [eval_equiv]
  have hPEF : fromCMvPolynomial (partialEvalFirst a p) =
      Finsupp.sum (fromCMvPolynomial p) (fun μ c =>
        MvPolynomial.monomial
          (CMvMonomial.toFinsupp
            (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.succ))
          (c * a ^ (CMvMonomial.ofFinsupp μ).get 0)) := by
    unfold partialEvalFirst
    rw [foldl_add_comm' (fun mono c =>
      CMvPolynomial.monomial (Vector.ofFn fun j : Fin n => mono.get j.succ)
        (c * a ^ mono.get 0)) p.1]
    rw [foldl_eq_sum, fromCMvPolynomial_finsupp_sum]
    simp only [Function.comp_def, fromCMvPolynomial_monomial]
  rw [hPEF]
  simp only [Finsupp.sum, map_sum, MvPolynomial.eval_monomial]
  change _ = MvPolynomial.eval₂ (RingHom.id R) (Fin.cons a v) (fromCMvPolynomial p)
  simp only [MvPolynomial.eval₂, Finsupp.sum, RingHom.id_apply]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finsupp.prod_fintype _ _ (fun i => by simp),
      Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [toFinsupp_apply, Vector.get_ofFn, CMvMonomial.ofFinsupp]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- `partialEvalLast a p` correctly implements partial evaluation of the last variable:
evaluating the result at `v` equals evaluating `p` at `Fin.snoc v a`. -/
theorem partialEvalLast_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalLast a p).eval v = p.eval (Fin.snoc v a) := by
  simp only [eval_equiv]
  -- Express partialEvalLast as Finsupp.sum of MvPolynomial.monomials
  have hPEL : fromCMvPolynomial (partialEvalLast a p) =
      Finsupp.sum (fromCMvPolynomial p) (fun μ c =>
        MvPolynomial.monomial
          (CMvMonomial.toFinsupp
            (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.castSucc))
          (c * a ^ (CMvMonomial.ofFinsupp μ).get (Fin.last n))) := by
    unfold partialEvalLast
    rw [foldl_add_comm' (fun mono c =>
      CMvPolynomial.monomial (Vector.ofFn fun j : Fin n => mono.get j.castSucc)
        (c * a ^ mono.get (Fin.last n))) p.1]
    rw [foldl_eq_sum, fromCMvPolynomial_finsupp_sum]
    simp only [Function.comp_def, fromCMvPolynomial_monomial]
  rw [hPEL]
  -- Distribute eval over the Finsupp.sum and evaluate monomials
  simp only [Finsupp.sum, map_sum, MvPolynomial.eval_monomial]
  -- RHS: unfold MvPolynomial.eval to sum form
  change _ = MvPolynomial.eval₂ (RingHom.id R) (Fin.snoc v a) (fromCMvPolynomial p)
  simp only [MvPolynomial.eval₂, Finsupp.sum, RingHom.id_apply]
  -- Both sides are Finset.sum over same support, show terms equal
  apply Finset.sum_congr rfl
  intro μ _
  -- Convert Finsupp.prod to Finset.prod over full Fintype
  rw [Finsupp.prod_fintype _ _ (fun i => by simp),
      Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [toFinsupp_apply, Vector.get_ofFn, CMvMonomial.ofFinsupp]
  -- Split the RHS product using Fin.prod_univ_castSucc
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- `sumOverLast` evaluates correctly: sums the polynomial over the domain in the last
variable. -/
theorem sumOverLast_eval (D : Fin m → R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (sumOverLast D p).eval v =
      (Finset.univ : Finset (Fin m)).sum (fun j => p.eval (Fin.snoc v (D j))) := by
  simp only [sumOverLast]
  induction (Finset.univ : Finset (Fin m)) using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    simp [eval_equiv]
  | cons j s hj ih =>
    simp only [Finset.sum_cons]
    rw [eval_add, ih]
    congr 1
    exact partialEvalLast_eval (D j) p v

/-- Iterated prefix evaluation is semantically correct. -/
theorem partialEvalPrefix_eval :
    ∀ {i n : ℕ} (fixed : Vector R i) (p : CMvPolynomial (n + i) R) (v : Fin n → R),
      (partialEvalPrefix fixed p).eval v = p.eval (prefixPoint fixed v)
  | 0, _, _, _, _ => by
      rfl
  | i + 1, n, fixed, p, v => by
      simpa [partialEvalPrefix, prefixPoint] using
        (partialEvalPrefix_eval (Vector.ofFn fun j : Fin i => fixed.get j.succ)
          (partialEvalFirst (fixed.get 0) p) v).trans
        (partialEvalFirst_eval (fixed.get 0) p
          (prefixPoint (Vector.ofFn fun j : Fin i => fixed.get j.succ) v))

/-- Summing out all variables except the first agrees with direct evaluation over the
remaining domain points. -/
theorem sumAllButFirst_eval (D : Fin m → R) :
    ∀ (k : ℕ) (p : CMvPolynomial (k + 1) R) (x : R),
      (sumAllButFirst D k p).eval (fun _ : Fin 1 => x) =
        (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
          p.eval (Fin.cons x (D ∘ z)))
  | 0, p, x => by
      simp only [sumAllButFirst, Finset.univ_unique, Nat.reduceAdd, Finset.sum_singleton]
      congr 1
      ext j
      fin_cases j
      simp
  | k + 1, p, x => by
      rw [sumAllButFirst, sumAllButFirst_eval D k (sumOverLast D p) x]
      have hSnoc :
          ∀ z : Fin k → Fin m, ∀ a : Fin m,
            p.eval (Fin.snoc (Fin.cons x (D ∘ z)) (D a)) =
              p.eval (Fin.cons x (D ∘ Fin.snoc z a)) := by
        intro z a
        congr 1
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [Function.comp_def]
        | succ j =>
            rw [Fin.cons_succ]
            by_cases hj : (j : ℕ) < k
            · have hsucc : (j.succ : ℕ) ≤ k := Nat.succ_le_of_lt hj
              have hlt : (j.succ : ℕ) < k + 1 := Nat.lt_succ_of_le hsucc
              have hidx : j.succ.castLT hlt = (j.castLT hj).succ := by
                apply Fin.ext
                rfl
              simp [Fin.snoc, hj, hidx]
            · have hjlast : j = Fin.last k := Fin.eq_last_of_not_lt hj
              subst hjlast
              simp
      have hSum :
          (∑ z : Fin k → Fin m, (sumOverLast D p).eval (Fin.cons x (D ∘ z))) =
            ∑ z : Fin k → Fin m, ∑ a : Fin m, p.eval (Fin.cons x (D ∘ Fin.snoc z a)) := by
        refine Fintype.sum_congr
          (f := fun z => (sumOverLast D p).eval (Fin.cons x (D ∘ z)))
          (g := fun z => ∑ a : Fin m, p.eval (Fin.cons x (D ∘ Fin.snoc z a))) ?_
        intro z
        calc
          (sumOverLast D p).eval (Fin.cons x (D ∘ z))
              = ∑ a : Fin m, p.eval (Fin.snoc (Fin.cons x (D ∘ z)) (D a)) := by
                  simpa using sumOverLast_eval D p (Fin.cons x (D ∘ z))
          _ = ∑ a : Fin m, p.eval (Fin.cons x (D ∘ Fin.snoc z a)) := by
                  refine Fintype.sum_congr
                    (f := fun a => p.eval (Fin.snoc (Fin.cons x (D ∘ z)) (D a)))
                    (g := fun a => p.eval (Fin.cons x (D ∘ Fin.snoc z a))) ?_
                  intro a
                  exact hSnoc z a
      rw [hSum]
      have hProd :
          (∑ z : Fin k → Fin m, ∑ a : Fin m, p.eval (Fin.cons x (D ∘ Fin.snoc z a))) =
            ∑ za : (Fin k → Fin m) × Fin m, p.eval (Fin.cons x (D ∘ Fin.snoc za.1 za.2)) := by
        simpa using
          (Fintype.sum_prod_type
            (f := fun za : (Fin k → Fin m) × Fin m =>
              p.eval (Fin.cons x (D ∘ Fin.snoc za.1 za.2)))).symm
      rw [hProd]
      let e : ((Fin k → Fin m) × Fin m) ≃ (Fin (k + 1) → Fin m) := {
        toFun := fun za => Fin.snoc za.1 za.2
        invFun := fun z => ((fun j => z j.castSucc), z (Fin.last k))
        left_inv := by
          intro za
          cases za with
          | mk z a =>
              simp
        right_inv := by
          intro z
          ext j
          refine Fin.lastCases ?_ ?_ j
          · simp
          · intro i
            simp
      }
      simpa [e] using
        (Fintype.sum_equiv e
          (fun za : (Fin k → Fin m) × Fin m => p.eval (Fin.cons x (D ∘ Fin.snoc za.1 za.2)))
          (fun z : Fin (k + 1) → Fin m => p.eval (Fin.cons x (D ∘ z)))
          (fun _ => rfl))

/-! ## Degree bound lemmas -/

omit [LawfulBEq R] in
theorem CPolynomial.natDegree_zero_le (d : ℕ) :
    (0 : CPolynomial R).natDegree ≤ d := by
  suffices h : (0 : CPolynomial R).natDegree = 0 from h ▸ Nat.zero_le d
  unfold CompPoly.CPolynomial.natDegree CompPoly.CPolynomial.Raw.natDegree
  unfold CompPoly.CPolynomial.Raw.lastNonzero
  split
  · rfl
  · next i _ =>
    have hsz : (↑(0 : CompPoly.CPolynomial R) : CompPoly.CPolynomial.Raw R).size = 0 := rfl
    exact absurd i.isLt (by omega)

end CPoly.CMvPolynomial

/-! ## Degree bound lemmas

These require `CommRing R` for the `natDegree_toPoly` bridge. -/

namespace CPoly.CMvPolynomial

variable {n m : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R]

omit [BEq R] [LawfulBEq R] in
private lemma coeff_ne_zero_of_mem_monomials {k : ℕ} {p : CMvPolynomial k R}
    {mono : CMvMonomial k} (hmono : mono ∈ Lawful.monomials p) :
    coeff mono p ≠ 0 :=
  Lawful.getD_getElem?_ne_zero_of_mem ((Lawful.mem_monomials_iff).1 hmono)

omit [BEq R] [LawfulBEq R] in
private lemma mem_monomials_of_coeff_ne_zero {k : ℕ} {p : CMvPolynomial k R}
    {mono : CMvMonomial k} (hcoeff : coeff mono p ≠ 0) :
    mono ∈ Lawful.monomials p := by
  apply (Lawful.mem_monomials_iff).2
  rw [Lawful.mem_iff]
  unfold coeff at hcoeff
  cases hlookup : p.1[mono]? with
  | none =>
      simp [hlookup] at hcoeff
  | some c =>
      refine ⟨c, ?_, ?_⟩
      · simpa [hlookup] using hcoeff
      · rfl

private lemma coeff_eq_zero_of_not_mem_monomials {k : ℕ} {p : CMvPolynomial k R}
    {mono : CMvMonomial k} (hmono : mono ∉ Lawful.monomials p) :
    coeff mono p = 0 := by
  by_contra hcoeff
  exact hmono (mem_monomials_of_coeff_ne_zero hcoeff)

private theorem fromCMvPolynomial_partialEvalFirst (a : R) (p : CMvPolynomial (n + 1) R) :
    fromCMvPolynomial (partialEvalFirst a p) =
      Finsupp.sum (fromCMvPolynomial p) (fun μ c =>
        MvPolynomial.monomial
          (CMvMonomial.toFinsupp
            (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.succ))
          (c * a ^ (CMvMonomial.ofFinsupp μ).get 0)) := by
  unfold partialEvalFirst
  rw [foldl_add_comm' (fun mono c =>
    CMvPolynomial.monomial (Vector.ofFn fun j : Fin n => mono.get j.succ)
      (c * a ^ mono.get 0)) p.1]
  rw [foldl_eq_sum, fromCMvPolynomial_finsupp_sum]
  simp only [Function.comp_def, fromCMvPolynomial_monomial]

private theorem fromCMvPolynomial_partialEvalLast (a : R) (p : CMvPolynomial (n + 1) R) :
    fromCMvPolynomial (partialEvalLast a p) =
      Finsupp.sum (fromCMvPolynomial p) (fun μ c =>
        MvPolynomial.monomial
          (CMvMonomial.toFinsupp
            (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.castSucc))
          (c * a ^ (CMvMonomial.ofFinsupp μ).get (Fin.last n))) := by
  unfold partialEvalLast
  rw [foldl_add_comm' (fun mono c =>
    CMvPolynomial.monomial (Vector.ofFn fun j : Fin n => mono.get j.castSucc)
      (c * a ^ mono.get (Fin.last n))) p.1]
  rw [foldl_eq_sum, fromCMvPolynomial_finsupp_sum]
  simp only [Function.comp_def, fromCMvPolynomial_monomial]

private lemma exists_source_of_mem_partialEvalFirst
    (a : R) (p : CMvPolynomial (n + 1) R) {mono : CMvMonomial n}
    (hmono : mono ∈ Lawful.monomials (partialEvalFirst a p)) :
    ∃ src ∈ Lawful.monomials p,
      Vector.ofFn (fun j : Fin n => src.get j.succ) = mono := by
  have hmono_support : CMvMonomial.toFinsupp mono ∈
      (fromCMvPolynomial (partialEvalFirst a p)).support := by
    rw [MvPolynomial.mem_support_iff, coeff_eq]
    simpa [CMvMonomial.ofFinsupp_toFinsupp] using coeff_ne_zero_of_mem_monomials hmono
  rw [fromCMvPolynomial_partialEvalFirst] at hmono_support
  have hmono_biUnion :
      CMvMonomial.toFinsupp mono ∈
        ((fromCMvPolynomial p).support).biUnion (fun μ =>
          (MvPolynomial.monomial
            (CMvMonomial.toFinsupp
              (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.succ))
            ((fromCMvPolynomial p).coeff μ * a ^ (CMvMonomial.ofFinsupp μ).get 0)).support) := by
    exact (MvPolynomial.support_sum (s := (fromCMvPolynomial p).support)
      (f := fun μ =>
        MvPolynomial.monomial
          (CMvMonomial.toFinsupp
            (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.succ))
          ((fromCMvPolynomial p).coeff μ * a ^ (CMvMonomial.ofFinsupp μ).get 0)))
      (by simpa [Finsupp.sum] using hmono_support)
  rcases Finset.mem_biUnion.mp hmono_biUnion with ⟨μ, hμ, hμmono⟩
  have hsingleton :
      CMvMonomial.toFinsupp mono ∈
        {CMvMonomial.toFinsupp
          (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.succ)} :=
    MvPolynomial.support_monomial_subset hμmono
  refine ⟨CMvMonomial.ofFinsupp μ, ?_, ?_⟩
  · apply mem_monomials_of_coeff_ne_zero
    rw [← coeff_eq (a := p) (m := μ)]
    exact MvPolynomial.mem_support_iff.mp hμ
  · apply CMvMonomial.injective_toFinsupp
    exact (Finset.mem_singleton.mp hsingleton).symm

private lemma exists_source_of_mem_partialEvalLast
    (a : R) (p : CMvPolynomial (n + 1) R) {mono : CMvMonomial n}
    (hmono : mono ∈ Lawful.monomials (partialEvalLast a p)) :
    ∃ src ∈ Lawful.monomials p,
      Vector.ofFn (fun j : Fin n => src.get j.castSucc) = mono := by
  have hmono_support : CMvMonomial.toFinsupp mono ∈
      (fromCMvPolynomial (partialEvalLast a p)).support := by
    rw [MvPolynomial.mem_support_iff, coeff_eq]
    simpa [CMvMonomial.ofFinsupp_toFinsupp] using coeff_ne_zero_of_mem_monomials hmono
  rw [fromCMvPolynomial_partialEvalLast] at hmono_support
  have hmono_biUnion :
      CMvMonomial.toFinsupp mono ∈
        ((fromCMvPolynomial p).support).biUnion (fun μ =>
          (MvPolynomial.monomial
            (CMvMonomial.toFinsupp
              (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.castSucc))
            ((fromCMvPolynomial p).coeff μ
              * a ^ (CMvMonomial.ofFinsupp μ).get (Fin.last n))).support) := by
    exact (MvPolynomial.support_sum (s := (fromCMvPolynomial p).support)
      (f := fun μ =>
        MvPolynomial.monomial
          (CMvMonomial.toFinsupp
            (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.castSucc))
          ((fromCMvPolynomial p).coeff μ
            * a ^ (CMvMonomial.ofFinsupp μ).get (Fin.last n))))
      (by simpa [Finsupp.sum] using hmono_support)
  rcases Finset.mem_biUnion.mp hmono_biUnion with ⟨μ, hμ, hμmono⟩
  have hsingleton :
      CMvMonomial.toFinsupp mono ∈
        {CMvMonomial.toFinsupp
          (Vector.ofFn fun j : Fin n => (CMvMonomial.ofFinsupp μ).get j.castSucc)} :=
    MvPolynomial.support_monomial_subset hμmono
  refine ⟨CMvMonomial.ofFinsupp μ, ?_, ?_⟩
  · apply mem_monomials_of_coeff_ne_zero
    rw [← coeff_eq (a := p) (m := μ)]
    exact MvPolynomial.mem_support_iff.mp hμ
  · apply CMvMonomial.injective_toFinsupp
    exact (Finset.mem_singleton.mp hsingleton).symm

private lemma exists_summand_of_mem_monomials_sum {k : ℕ} {α : Type}
    (s : Finset α) (f : α → CMvPolynomial k R) {mono : CMvMonomial k}
    (hmono : mono ∈ Lawful.monomials (∑ x ∈ s, f x)) :
    ∃ x ∈ s, mono ∈ Lawful.monomials (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty] at hmono
      exact (Lawful.not_mem_zero (x := mono) ((Lawful.mem_monomials_iff).1 hmono)).elim
  | @insert a s ha ih =>
      let tail : CMvPolynomial k R := ∑ x ∈ s, f x
      have hcoeff_sum : coeff mono (∑ x ∈ insert a s, f x) ≠ 0 := by
        convert coeff_ne_zero_of_mem_monomials hmono
      have hcoeff_add :
          coeff mono (f a) + coeff mono tail ≠ 0 := by
        simpa [tail, Finset.sum_insert, ha, coeff_add] using hcoeff_sum
      by_cases hfa : mono ∈ Lawful.monomials (f a)
      · exact ⟨a, Finset.mem_insert_self a s, hfa⟩
      · have hsum : coeff mono tail ≠ 0 := by
          intro hsum_zero
          apply hcoeff_add
          simp [tail, coeff_eq_zero_of_not_mem_monomials hfa, hsum_zero]
        obtain ⟨x, hx, hmono_fx⟩ := ih (by
          simpa [tail] using mem_monomials_of_coeff_ne_zero hsum)
        exact ⟨x, Finset.mem_insert_of_mem hx, hmono_fx⟩

private theorem toUnivariate_toPoly (p : CMvPolynomial 1 R) :
    (toUnivariate p).toPoly =
      Finset.sum (fromCMvPolynomial p).support (fun μ =>
        Polynomial.monomial ((CMvMonomial.ofFinsupp μ).get 0)
          ((fromCMvPolynomial p).coeff μ)) := by
  unfold toUnivariate
  rw [foldl_add_comm' (fun mono c => CPolynomial.monomial (mono.get 0) c) p.1]
  rw [foldl_eq_sum, Finsupp.sum]
  let s : Finset (Fin 1 →₀ ℕ) := (fromCMvPolynomial p).support
  change
      (∑ x ∈ s,
        CPolynomial.monomial ((CMvMonomial.ofFinsupp x).get 0)
          ((fromCMvPolynomial p).coeff x)).toPoly
    =
      ∑ x ∈ s,
        Polynomial.monomial ((CMvMonomial.ofFinsupp x).get 0) ((fromCMvPolynomial p).coeff x)
  induction s using Finset.cons_induction with
  | empty =>
      change CompPoly.CPolynomial.toPoly (0 : CPolynomial R) = (0 : Polynomial R)
      change CompPoly.CPolynomial.Raw.toPoly (0 : CompPoly.CPolynomial.Raw R) = (0 : Polynomial R)
      simpa using (CompPoly.CPolynomial.Raw.toPoly_zero (R := R))
  | cons μ s hμ ih =>
      simp [hμ, CompPoly.CPolynomial.toPoly_add',
        CompPoly.CPolynomial.monomial_toPoly, ih]

/-- `toUnivariate` preserves evaluation at the unique remaining variable. -/
theorem toUnivariate_eval (p : CMvPolynomial 1 R) (x : R) :
    CPolynomial.eval x (toUnivariate p) = p.eval (fun _ : Fin 1 => x) := by
  have hMonomialEval :
      ∀ n c, CPolynomial.eval x (CPolynomial.monomial n c) = c * x ^ n := by
    intro n c
    rw [CompPoly.CPolynomial.eval_toPoly, CompPoly.CPolynomial.monomial_toPoly]
    simp
  unfold toUnivariate
  rw [foldl_add_comm' (fun mono c => CPolynomial.monomial (mono.get 0) c) p.1]
  rw [foldl_eq_sum, Finsupp.sum]
  rw [CompPoly.CPolynomial.eval_sum']
  change
    ∑ μ ∈ (fromCMvPolynomial p).support,
      CPolynomial.eval x
        (CPolynomial.monomial ((CMvMonomial.ofFinsupp μ).get 0) ((fromCMvPolynomial p).coeff μ))
      = p.eval (fun _ : Fin 1 => x)
  simp only [hMonomialEval, eval_equiv]
  change
    ∑ μ ∈ (fromCMvPolynomial p).support,
      (fromCMvPolynomial p).coeff μ * x ^ (CMvMonomial.ofFinsupp μ).get 0 =
      MvPolynomial.eval₂ (RingHom.id R) (fun _ : Fin 1 => x) (fromCMvPolynomial p)
  simp only [MvPolynomial.eval₂, Finsupp.sum, RingHom.id_apply]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_succ]
  simp [CMvMonomial.ofFinsupp]
  rfl

/-- The symbolic round polynomial computes the exact remaining-sum function. -/
theorem roundPoly_eval (D : Fin m → R) (k : ℕ) (p : CMvPolynomial (k + 1) R) (x : R) :
    CPolynomial.eval x (roundPoly D k p) =
      (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
        p.eval (Fin.cons x (D ∘ z))) := by
  unfold roundPoly
  rw [toUnivariate_eval, sumAllButFirst_eval]

/-- `toUnivariate` preserves degree bounds: if every monomial of `p : CMvPolynomial 1 R`
has `mono.get 0 ≤ deg`, then `(toUnivariate p).natDegree ≤ deg`. -/
theorem toUnivariate_natDegree_le {deg : ℕ}
    (p : CMvPolynomial 1 R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.get 0 ≤ deg) :
    (toUnivariate p).natDegree ≤ deg := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  rw [toUnivariate_toPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro μ hμ
  exact _root_.le_trans
    (Polynomial.natDegree_monomial_le ((fromCMvPolynomial p).coeff μ)
      (m := (CMvMonomial.ofFinsupp μ).get 0))
    (hDeg (CMvMonomial.ofFinsupp μ) (by
      apply mem_monomials_of_coeff_ne_zero
      rw [← coeff_eq (a := p) (m := μ)]
      exact MvPolynomial.mem_support_iff.mp hμ))

/-- `partialEvalFirst` preserves individual degree bounds by shifting output variable `j`
to input variable `j.succ`. -/
theorem partialEvalFirst_individualDegreeLE {deg : ℕ} (a : R)
    (p : CMvPolynomial (n + 1) R)
    (hDeg : IndividualDegreeLE (R := R) deg p) :
    IndividualDegreeLE (R := R) deg (partialEvalFirst a p) := by
  intro j mono hmono
  obtain ⟨src, hsrc, hEq⟩ := exists_source_of_mem_partialEvalFirst a p hmono
  rw [← hEq, Vector.get_ofFn]
  exact hDeg j.succ src hsrc

/-- Iterated prefix evaluation preserves individual degree bounds. -/
theorem partialEvalPrefix_individualDegreeLE {deg : ℕ} :
    ∀ {i n : ℕ} (fixed : Vector R i) (p : CMvPolynomial (n + i) R),
      IndividualDegreeLE (R := R) deg p →
        IndividualDegreeLE (R := R) deg (partialEvalPrefix fixed p)
  | 0, _, _, _, hDeg => by
      simpa [partialEvalPrefix] using hDeg
  | i + 1, n, fixed, p, hDeg => by
      have hStep :
          IndividualDegreeLE (R := R) deg (partialEvalFirst (fixed.get 0) p) :=
        partialEvalFirst_individualDegreeLE (fixed.get 0) p hDeg
      simpa [partialEvalPrefix] using
        partialEvalPrefix_individualDegreeLE
          (n := n)
          (Vector.ofFn fun j : Fin i => fixed.get j.succ)
          (partialEvalFirst (fixed.get 0) p)
          hStep

/-- `sumOverLast` preserves the degree bound in variable 0. -/
theorem sumOverLast_monomials_get0_le {deg : ℕ} (D : Fin m → R)
    (p : CMvPolynomial (n + 2) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.get 0 ≤ deg) :
    ∀ mono ∈ Lawful.monomials (sumOverLast D p), mono.get 0 ≤ deg := by
  intro mono hmono
  obtain ⟨j, -, hj⟩ := exists_summand_of_mem_monomials_sum
    (s := (Finset.univ : Finset (Fin m)))
    (f := fun j => partialEvalLast (D j) p)
    (by simpa [sumOverLast] using hmono)
  obtain ⟨src, hsrc, hEq⟩ := exists_source_of_mem_partialEvalLast (D j) p hj
  rw [← hEq, Vector.get_ofFn]
  simpa using hDeg src hsrc

/-- `sumAllButFirst` preserves the degree bound in variable 0. -/
theorem sumAllButFirst_monomials_get0_le {deg : ℕ} (D : Fin m → R) (k : ℕ)
    (p : CMvPolynomial (k + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.get 0 ≤ deg) :
    ∀ mono ∈ Lawful.monomials (sumAllButFirst D k p), mono.get 0 ≤ deg := by
  induction k with
  | zero => exact hDeg
  | succ k ih => exact ih (sumOverLast D p) (sumOverLast_monomials_get0_le D p hDeg)

/-- The round polynomial has degree at most `deg` when the original polynomial has
individual degree at most `deg` in variable 0. -/
theorem roundPoly_natDegree_le {deg : ℕ} (D : Fin m → R) {k : ℕ}
    (p : CMvPolynomial (k + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.get 0 ≤ deg) :
    (roundPoly D k p).natDegree ≤ deg :=
  toUnivariate_natDegree_le (sumAllButFirst D k p)
    (sumAllButFirst_monomials_get0_le D k p hDeg)

end CPoly.CMvPolynomial
