/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.PolyUtils
import CompPoly.Multivariate.Rename

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

variable [DecidableEq R]

/-- Convert a single-variable multivariate polynomial to a univariate `CPolynomial`.
Each term `c · X₀^e` maps to `c · X^e`. -/
def toUnivariate (p : CMvPolynomial 1 R) : CPolynomial R :=
  ExtTreeMap.foldl (fun acc mono c =>
    acc + CPolynomial.monomial (mono.get 0) c) 0 p.1

/-! ## Composed operations -/

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

omit [DecidableEq R] in
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

omit [DecidableEq R] in
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

omit [DecidableEq R] in
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

/-! ## Degree bound lemmas -/

omit [LawfulBEq R] [DecidableEq R] in
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

/-- The round polynomial has degree at most `deg` when the original polynomial has
individual degree at most `deg` in variable 0. -/
theorem roundPoly_natDegree_le {deg : ℕ} (D : Fin m → R) {k : ℕ}
    (p : CMvPolynomial (k + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.get 0 ≤ deg) :
    (roundPoly D k p).natDegree ≤ deg := by
  sorry

end CPoly.CMvPolynomial
