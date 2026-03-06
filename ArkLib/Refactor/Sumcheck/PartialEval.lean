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

/-! ## Degree bound lemmas -/

/-- `p` has individual degree at most `deg` when every monomial exponent is bounded by `deg`
in every coordinate. This is the invariant preserved by symbolic `partialEvalFirst`. -/
def IndividualDegreeLE {n : ℕ} (deg : ℕ) (p : CMvPolynomial n R) : Prop :=
  ∀ i : Fin n, ∀ mono ∈ Lawful.monomials p, mono.get i ≤ deg

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

/-- `toUnivariate` preserves degree bounds: if every monomial of `p : CMvPolynomial 1 R`
has `mono.get 0 ≤ deg`, then `(toUnivariate p).natDegree ≤ deg`. -/
theorem toUnivariate_natDegree_le {deg : ℕ}
    (p : CMvPolynomial 1 R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.get 0 ≤ deg) :
    (toUnivariate p).natDegree ≤ deg := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  let q : Polynomial R :=
    Finset.sum (fromCMvPolynomial p).support (fun μ =>
      Polynomial.monomial ((CMvMonomial.ofFinsupp μ).get 0)
        ((fromCMvPolynomial p).coeff μ))
  have hToPoly : (toUnivariate p).toPoly = q := by
    unfold q
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
  rw [hToPoly]
  unfold q
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
