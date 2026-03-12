/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Prelims

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
  # Definitions and Theorems about Bivariate Polynomials with coefficients in a semiring

  This file keeps the remaining Mathlib-facing bivariate degree/evaluation surface that is still
  used inside ArkLib after the CompPoly cutover.
-/

open Polynomial
open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type} [Semiring F]

/-- The set of coefficients of a bivariate polynomial. -/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

/-- `(i, j)`-coefficient of a polynomial, i.e. the coefficient of `X^i Y^j`. -/
def coeff.{u} {F : Type u} [Semiring F] (f : F[X][Y]) (i j : ℕ) : F := (f.coeff j).coeff i

/-- The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY (f : F[X][Y]) : F[X] := f.coeff (natDegree f)

/-- The polynomial coefficient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial. -/
@[simp, grind =]
theorem leadingCoeffY_eq_zero (f : F[X][Y]) : leadingCoeffY f = 0 ↔ f = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (Finset.mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/-- The polynomial coefficient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero. -/
@[simp, grind =]
lemma leadingCoeffY_ne_zero (f : F[X][Y]) : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  rw [Ne, leadingCoeffY_eq_zero]

/-- A bivariate polynomial is non-zero if and only if all its coefficients are non-zero. -/
@[grind =_]
lemma ne_zero_iff_coeffs_ne_zero (f : F[X][Y]) : f ≠ 0 ↔ f.coeff ≠ 0 :=
  ⟨
    fun hf ↦ by
      have f_finsupp : f.toFinsupp ≠ 0 := by aesop
      simpa [Polynomial.coeff],
    fun f_coeffs ↦ by aesop (add simp Polynomial.coeff)
  ⟩

/-- The `Y`-degree of a bivariate polynomial, as a natural number. -/
def natDegreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

/-- The set of `Y`-degrees is non-empty. -/
lemma degreesY_nonempty {f : F[X][Y]} (hf : f ≠ 0) : (f.toFinsupp.support).Nonempty :=
  Finsupp.support_nonempty_iff.mpr
    fun h ↦ hf (Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl))

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ := f.support.sup (fun n => (f.coeff n).natDegree)

/-- The total degree of a bivariate polynomial. -/
def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natDegree + m)

/-- `(u,v)`-weighted degree of a polynomial.
The maximal `u * i + v * j` such that the polynomial `p`
contains a monomial `x^i * y^j`. -/
def weightedDegree.{u} {F : Type u} [Semiring F] (p : F[X][Y]) (u v : ℕ) : Option ℕ :=
  List.max? <|
    List.map (fun n => u * (p.coeff n).natDegree + v * n) (List.range p.natDegree.succ)

def natWeightedDegree.{u} {F : Type u} [Semiring F] (f : F[X][Y]) (u v : ℕ) : ℕ :=
  f.support.sup (fun m => u * (f.coeff m).natDegree + v * m)

variable {f : F[X][Y]}

/-- The weighted degree is always defined (never none). -/
lemma weightedDegree_ne_none {F : Type} [Semiring F] (f : F[X][Y]) (u v : ℕ) :
    weightedDegree f u v ≠ none := by
  unfold weightedDegree
  aesop

theorem natWeightedDegree_mem_weight_list {u v : ℕ} (hf : f ≠ 0) :
    natWeightedDegree f u v ∈
      List.map (fun n => u * (f.coeff n).natDegree + v * n)
        (List.range f.natDegree.succ) := by
  classical
  have hsupp : f.support.Nonempty := by
    refine ⟨f.natDegree, ?_⟩
    exact Polynomial.natDegree_mem_support_of_nonzero (p := f) hf
  obtain ⟨m, hm, hsup⟩ :=
    Finset.exists_mem_eq_sup (s := f.support) hsupp
      (fun n => u * (f.coeff n).natDegree + v * n)
  have hm_le : m ≤ f.natDegree := Polynomial.le_natDegree_of_mem_supp (p := f) m hm
  have hm_range : m ∈ List.range f.natDegree.succ := by
    exact List.mem_range.mpr (Nat.lt_succ_of_le hm_le)
  have hw_mem :
      (u * (f.coeff m).natDegree + v * m) ∈
        List.map (fun n => u * (f.coeff n).natDegree + v * n)
          (List.range f.natDegree.succ) := by
    exact List.mem_map_of_mem (f := fun n => u * (f.coeff n).natDegree + v * n) hm_range
  unfold natWeightedDegree
  simpa [hsup] using hw_mem

theorem weight_le_natWeightedDegree_of_lt_natDegree_succ {u v n : ℕ}
    (hf : f ≠ 0) (hn : n < f.natDegree.succ) :
    u * (f.coeff n).natDegree + v * n ≤ natWeightedDegree f u v := by
  classical
  unfold natWeightedDegree
  by_cases hns : n ∈ f.support
  · exact Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hns
  ·
    have hcoeff : f.coeff n = 0 := Polynomial.notMem_support_iff.1 hns
    have hnle : n ≤ f.natDegree := Nat.lt_succ_iff.mp hn
    have hmul : v * n ≤ v * f.natDegree := Nat.mul_le_mul_left v hnle
    have hdegmem : f.natDegree ∈ f.support := Polynomial.natDegree_mem_support_of_nonzero hf
    have hsup : u * (f.coeff f.natDegree).natDegree + v * f.natDegree ≤
        f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) := by
      exact
        Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hdegmem
    have hvdeg : v * f.natDegree ≤ u * (f.coeff f.natDegree).natDegree + v * f.natDegree := by
      exact Nat.le_add_left _ _
    have hvdeg' : v * f.natDegree ≤
        f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) :=
      le_trans hvdeg hsup
    have : v * n ≤ f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) :=
      le_trans hmul hvdeg'
    simpa [hcoeff] using this

@[grind _=_]
lemma weightedDegree_eq_natWeightedDegree {u v : ℕ} :
    f ≠ 0 → weightedDegree f u v = natWeightedDegree f u v := by
  intro hf
  let w : ℕ → ℕ := fun n => u * (f.coeff n).natDegree + v * n
  let xs : List ℕ := List.map w (List.range f.natDegree.succ)
  have ha : natWeightedDegree f u v ∈ xs := by
    simpa [xs, w] using (natWeightedDegree_mem_weight_list (f := f) (u := u) (v := v) hf)
  have hle : ∀ b, b ∈ xs → b ≤ natWeightedDegree f u v := by
    intro b hb
    rcases List.mem_map.1 hb with ⟨n, hn, rfl⟩
    have hnlt : n < f.natDegree.succ := (List.mem_range.1 hn)
    exact
      weight_le_natWeightedDegree_of_lt_natDegree_succ
        (f := f) (u := u) (v := v) (n := n) hf hnlt
  have hmax : xs.max? = some (natWeightedDegree f u v) := by
    apply (List.max?_eq_some_iff (xs := xs) (a := natWeightedDegree f u v)).2
    refine ⟨ha, ?_⟩
    intro b hb
    exact hle b hb
  simpa [weightedDegree, xs, w] using hmax

/-- The total degree of a bivariate polynomial is equal to the `(1,1)`-weighted degree. -/
@[grind _=_]
lemma total_deg_as_weighted_deg :
    totalDegree f = natWeightedDegree f 1 1 := by
  unfold natWeightedDegree totalDegree
  simp

/-- The `X`-degree of a bivariate polynomial is equal to the `(1,0)`-weighted degree. -/
@[grind _=_]
lemma degreeX_as_weighted_deg :
    degreeX f = natWeightedDegree f 1 0 := by
  grind [degreeX, natWeightedDegree]

/-- The `Y`-degree of a bivariate polynomial is equal to the `(0,1)`-weighted degree. -/
@[grind _=_]
lemma degreeY_as_weighted_deg (hf : f ≠ 0) :
    natDegreeY f = natWeightedDegree f 0 1 := by
  rw [
    natDegreeY, natWeightedDegree,
    Polynomial.natDegree_eq_support_max' (p := f) hf, Finset.max'_eq_sup'
  ]
  simp [Finset.sup'_eq_sup]

/-- Over an intergal domain, the product of two non-zero bivariate polynomials is non-zero. -/
@[grind ←]
lemma mul_ne_zero [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := _root_.mul_ne_zero hf hg

/-- Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeY_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0)
    : natDegreeY (f * g) = natDegreeY f + natDegreeY g := by
  unfold natDegreeY
  rw [← leadingCoeffY_ne_zero] at hf hg
  have h_lc : leadingCoeffY f * leadingCoeffY g ≠ 0 := _root_.mul_ne_zero hf hg
  exact Polynomial.natDegree_mul' h_lc

attribute [local grind] Finsupp.support_nonempty_iff natDegree_mul_le degree_eq_bot
  WithBot.bot_lt_coe isMaxOn_iff sup_eq_of_isMaxOn monomial_eq_monomial_iff
attribute [local grind ←] toFinsupp_eq_zero
attribute [local grind _=_] Finsupp.mem_support_iff toFinsupp_apply smul_monomial
attribute [local grind =] natDegree_mul natDegree_add_eq_right_of_degree_lt
  natDegree_zero
@[local grind _=_]
private lemma support_eq_support_toFinsupp {f : F[X][Y]} : f.support = f.toFinsupp.support := rfl

theorem natDegree_sum_lt_of_forall_lt {F : Type} [Semiring F] {α : Type} {s : Finset α}
    {g : α → F[X]} {deg : ℕ} :
    0 < deg → (∀ x ∈ s, (g x).natDegree < deg) → (∑ x ∈ s, g x).natDegree < deg := by
  intro deg_pos h
  have hle : (∑ x ∈ s, g x).natDegree ≤ Nat.pred deg := by
    refine Polynomial.natDegree_sum_le_of_forall_le (s := s) (f := g) (n := Nat.pred deg) ?_
    intro x hx
    exact Nat.le_pred_of_lt (h x hx)
  exact lt_of_le_of_lt hle (Nat.pred_lt_self deg_pos)

theorem natDeg_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
    (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  classical
  intro hmxdeg others
  by_cases hdeg0 : deg = 0
  ·
    have hothers0 : ∀ y ∈ s, y ≠ mx → f y = 0 := by
      intro y hy hne
      have h' := others y hy hne
      rcases h' with hlt | hy0
      ·
        have hlt0 : (f y).natDegree < 0 := by simpa [hdeg0] using hlt
        exact (False.elim ((Nat.not_lt_zero _) hlt0))
      · exact hy0
    have hsum : (∑ x ∈ s, f x) = f mx := by
      classical
      refine Finset.sum_eq_single_of_mem mx h ?_?
      intro y hy hne
      exact hothers0 y hy hne
    calc
      (∑ x ∈ s, f x).natDegree = (f mx).natDegree := by simpa [hsum]
      _ = deg := hmxdeg
  ·
    have deg_pos : 0 < deg := Nat.pos_of_ne_zero hdeg0
    have hlt_sum : (∑ x ∈ s \ {mx}, f x).natDegree < deg := by
      refine natDegree_sum_lt_of_forall_lt (s := s \ {mx}) (g := f) (deg := deg) deg_pos ?_
      intro y hy
      have hy_s : y ∈ s := (Finset.mem_sdiff.mp hy).1
      have hy_not : y ∉ ({mx} : Finset α) := (Finset.mem_sdiff.mp hy).2
      have hy_ne : y ≠ mx := by
        simpa [Finset.mem_singleton] using hy_not
      have h' := others y hy_s hy_ne
      rcases h' with hlt | hy0
      · exact hlt
      · simpa [hy0] using deg_pos
    have hlt_mx : (∑ x ∈ s \ {mx}, f x).natDegree < (f mx).natDegree := by
      simpa [hmxdeg] using hlt_sum
    have hsum_decomp : (∑ x ∈ s, f x) = (∑ x ∈ s \ {mx}, f x) + f mx := by
      classical
      simpa using (Finset.sum_eq_sum_diff_singleton_add (s := s) (i := mx) (f := f) h)
    calc
      (∑ x ∈ s, f x).natDegree = ((∑ x ∈ s \ {mx}, f x) + f mx).natDegree := by
        simpa [hsum_decomp]
      _ = (f mx).natDegree := by
        exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt_mx
      _ = deg := hmxdeg

/-- If some element `x ∈ s` maps to `y` under `f`, and every element of `s` maps to a value
less than or equal to `y`, then the supremum of `f` over `s` is exactly `y`. -/
lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α}
    {f : α → β} (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  grind

theorem coeff_natDegree_le_degreeX (f : F[X][Y]) (n : ℕ) : (f.coeff n).natDegree ≤ degreeX f := by
  classical
  unfold degreeX
  by_cases hn : n ∈ f.support
  · exact (Finset.le_sup (s := f.support) (f := fun m => (f.coeff m).natDegree) hn)
  ·
    have hcoeff : f.coeff n = 0 := by
      exact Polynomial.notMem_support_iff.mp hn
    simpa [hcoeff] using (Nat.zero_le (f.support.sup fun m => (f.coeff m).natDegree))

theorem degreeX_mul_le (f g : F[X][Y]) : degreeX (f * g) ≤ degreeX f + degreeX g := by
  classical
  unfold degreeX
  refine Finset.sup_le ?_
  intro k hk
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.antidiagonal k)
    (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2)
    (n := degreeX f + degreeX g) ?_
  intro x hx
  have hf : (f.coeff x.1).natDegree ≤ degreeX f := coeff_natDegree_le_degreeX f x.1
  have hg : (g.coeff x.2).natDegree ≤ degreeX g := coeff_natDegree_le_degreeX g x.2
  exact le_trans (Polynomial.natDegree_mul_le (p := f.coeff x.1) (q := g.coeff x.2))
    (Nat.add_le_add hf hg)

theorem exists_max_index_degreeX (f : F[X][Y]) (hf : f ≠ 0) :
    ∃ mm ∈ f.support,
      (f.coeff mm).natDegree = degreeX f ∧
      ∀ n, mm < n → (f.coeff n).natDegree < degreeX f ∨ f.coeff n = 0 := by
  classical
  let s₁ : Finset ℕ := f.support.filter (fun n => (f.coeff n).natDegree = degreeX f)
  have hs₁ : s₁.Nonempty := by
    have hsupp : f.support.Nonempty := (Polynomial.support_nonempty).2 hf
    obtain ⟨m, hm_mem, hm_sup⟩ :=
      Finset.exists_mem_eq_sup (s := f.support) (h := hsupp)
        (f := fun n => (f.coeff n).natDegree)
    refine ⟨m, ?_⟩
    have hm_deg : (f.coeff m).natDegree = degreeX f := by
      simpa [Polynomial.Bivariate.degreeX] using hm_sup.symm
    simp [s₁, hm_mem, hm_deg]

  set mm : ℕ := s₁.max' hs₁ with hmm
  refine ⟨mm, ?_, ?_, ?_⟩
  ·
    have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have : mm ∈ f.support ∧ (f.coeff mm).natDegree = degreeX f := by
      simpa [s₁] using (Finset.mem_filter.1 hmm_mem)
    exact this.1
  ·
    have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have : mm ∈ f.support ∧ (f.coeff mm).natDegree = degreeX f := by
      simpa [s₁] using (Finset.mem_filter.1 hmm_mem)
    exact this.2
  ·
    have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have hmm_upper : ∀ b ∈ s₁, b ≤ mm := by
      have hchar : mm ∈ s₁ ∧ ∀ b, b ∈ s₁ → b ≤ mm := by
        simpa [hmm] using
          (Finset.max'_eq_iff (s := s₁) (H := hs₁) (a := mm)).1 rfl
      exact fun b hb => hchar.2 b hb

    intro n hmn
    by_cases hn0 : f.coeff n = 0
    · exact Or.inr hn0
    ·
      have hn_support : n ∈ f.support := by
        exact (Polynomial.mem_support_iff).2 hn0
      have hn_le : (f.coeff n).natDegree ≤ degreeX f := coeff_natDegree_le_degreeX f n
      have hn_ne : (f.coeff n).natDegree ≠ degreeX f := by
        intro hEq
        have hn_s₁ : n ∈ s₁ := by
          simp [s₁, hn_support, hEq]
        have hn_le_mm : n ≤ mm := hmm_upper n hn_s₁
        exact (not_le_of_gt hmn) hn_le_mm
      exact Or.inl (lt_of_le_of_ne hn_le hn_ne)

theorem natDegree_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
    (mx : α) (hmx : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  intro hdeg hothers
  classical
  have hle : ∀ y ∈ s, (f y).natDegree ≤ deg := by
    intro y hy
    by_cases hym : y = mx
    · subst hym
      simpa [hdeg]
    ·
      have hy' := hothers y hy hym
      cases hy' with
      | inl hlt =>
          exact le_of_lt hlt
      | inr hy0 =>
          simpa [hy0] using (Nat.zero_le deg)
  have hSle : (∑ x ∈ s, f x).natDegree ≤ deg :=
    Polynomial.natDegree_sum_le_of_forall_le (s := s) (f := f) (n := deg) hle
  by_cases hdeg0 : deg = 0
  ·
    subst hdeg0
    exact Nat.eq_zero_of_le_zero hSle
  ·
    have hmx_ne0 : f mx ≠ 0 := by
      intro h0
      apply hdeg0
      have : (0 : ℕ) = deg := by
        simpa [h0] using hdeg
      exact this.symm
    have hmx_coeff_ne0 : (f mx).coeff deg ≠ 0 := by
      have hlc : (f mx).leadingCoeff ≠ 0 :=
        (Polynomial.leadingCoeff_ne_zero).2 hmx_ne0
      simpa [Polynomial.leadingCoeff, hdeg] using hlc
    have hcoeff_others : ∀ y ∈ s, y ≠ mx → (f y).coeff deg = 0 := by
      intro y hy hym
      have hy' := hothers y hy hym
      cases hy' with
      | inl hlt =>
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      | inr hy0 =>
          simpa [hy0]
    have hsum_coeff : (∑ y ∈ s, (f y).coeff deg) = (f mx).coeff deg := by
      refine Finset.sum_eq_single_of_mem mx hmx ?_
      intro y hy hym
      exact hcoeff_others y hy hym
    have hcoeff_eq : (∑ x ∈ s, f x).coeff deg = (f mx).coeff deg := by
      rw [Polynomial.finset_sum_coeff (s := s) (f := f) (n := deg)]
      exact hsum_coeff
    have hcoeff_ne0 : (∑ x ∈ s, f x).coeff deg ≠ 0 := by
      simpa [hcoeff_eq] using hmx_coeff_ne0
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hSle hcoeff_ne0

theorem degreeX_mul_ge [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    degreeX f + degreeX g ≤ degreeX (f * g) := by
  classical
  rcases exists_max_index_degreeX f hf with ⟨mmfx, hmmfx, hmmfx_deg, hmmfx_max⟩
  rcases exists_max_index_degreeX g hg with ⟨mmgx, hmmgx, hmmgx_deg, hmmgx_max⟩
  let N : ℕ := mmfx + mmgx
  let deg : ℕ := degreeX f + degreeX g
  let term : ℕ × ℕ → F[X] := fun x => f.coeff x.1 * g.coeff x.2
  have hmx : (mmfx, mmgx) ∈ Finset.antidiagonal N := by
    simp [Finset.mem_antidiagonal, N]
  have hfx0 : f.coeff mmfx ≠ 0 := by
    exact (mem_support_iff.mp hmmfx)
  have hgx0 : g.coeff mmgx ≠ 0 := by
    exact (mem_support_iff.mp hmmgx)
  have hterm_mx : (term (mmfx, mmgx)).natDegree = deg := by
    simpa [term, deg, hmmfx_deg, hmmgx_deg] using
      (Polynomial.natDegree_mul (p := f.coeff mmfx) (q := g.coeff mmgx) hfx0 hgx0)
  have hterm_other :
      ∀ y ∈ Finset.antidiagonal N, y ≠ (mmfx, mmgx) →
        (term y).natDegree < deg ∨ term y = 0 := by
    intro y hy hyne
    rcases y with ⟨i, j⟩
    have hij : i + j = N := by
      simpa [Finset.mem_antidiagonal] using hy
    have hij' : i + j = mmfx + mmgx := by
      simpa [N] using hij
    have hlt : mmfx < i ∨ mmgx < j := by
      by_contra hcontra
      have hi : i ≤ mmfx :=
        le_of_not_gt (fun hlt => hcontra (Or.inl hlt))
      have hj : j ≤ mmgx :=
        le_of_not_gt (fun hlt => hcontra (Or.inr hlt))
      have h1 : i + j ≤ i + mmgx := Nat.add_le_add_left hj i
      have h2 : mmfx + mmgx ≤ i + mmgx := by
        simpa [hij'] using h1
      have hmmfx_le_i : mmfx ≤ i := (Nat.add_le_add_iff_right).1 h2
      have h3 : i + j ≤ mmfx + j := Nat.add_le_add_right hi j
      have h4 : mmfx + mmgx ≤ mmfx + j := by
        simpa [hij'] using h3
      have hmmgx_le_j : mmgx ≤ j := (Nat.add_le_add_iff_left).1 h4
      have hi_eq : i = mmfx := Nat.le_antisymm hi hmmfx_le_i
      have hj_eq : j = mmgx := Nat.le_antisymm hj hmmgx_le_j
      exact hyne (by
        cases hi_eq
        cases hj_eq
        rfl)
    cases hlt with
    | inl hi_lt =>
        have hfi : (f.coeff i).natDegree < degreeX f ∨ f.coeff i = 0 :=
          hmmfx_max i hi_lt
        cases hfi with
        | inr hfi0 =>
            right
            simp [term, hfi0]
        | inl hfi_lt =>
            by_cases hgj0 : g.coeff j = 0
            ·
              right
              simp [term, hgj0]
            ·
              left
              have hnat_le :
                  (term (i, j)).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
                simpa [term] using
                  (Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j))
              have hgj_le : (g.coeff j).natDegree ≤ degreeX g :=
                coeff_natDegree_le_degreeX g j
              have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
                have := Nat.add_lt_add_of_lt_of_le hfi_lt hgj_le
                simpa [deg] using this
              exact lt_of_le_of_lt hnat_le hsum_lt
    | inr hj_lt =>
        have hgj : (g.coeff j).natDegree < degreeX g ∨ g.coeff j = 0 :=
          hmmgx_max j hj_lt
        cases hgj with
        | inr hgj0 =>
            right
            simp [term, hgj0]
        | inl hgj_lt =>
            by_cases hfi0 : f.coeff i = 0
            ·
              right
              simp [term, hfi0]
            ·
              left
              have hnat_le :
                  (term (i, j)).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
                simpa [term] using
                  (Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j))
              have hfi_le : (f.coeff i).natDegree ≤ degreeX f :=
                coeff_natDegree_le_degreeX f i
              have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
                have := Nat.add_lt_add_of_le_of_lt hfi_le hgj_lt
                simpa [deg] using this
              exact lt_of_le_of_lt hnat_le hsum_lt
  have hsum_nat : (∑ x ∈ Finset.antidiagonal N, term x).natDegree = deg := by
    exact natDegree_sum_eq_of_unique (mx := (mmfx, mmgx)) (hmx := hmx) hterm_mx hterm_other
  have hcoeff_nat : ((f * g).coeff N).natDegree = deg := by
    have hcoeff : (f * g).coeff N = ∑ x ∈ Finset.antidiagonal N, term x := by
      simpa [term] using (Polynomial.coeff_mul f g N)
    simpa [hcoeff] using hsum_nat
  have hle : deg ≤ degreeX (f * g) := by
    have hle' : ((f * g).coeff N).natDegree ≤ degreeX (f * g) :=
      coeff_natDegree_le_degreeX (f * g) N
    simpa [hcoeff_nat] using hle'
  simpa [deg] using hle

theorem degreeX_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    degreeX (f * g) = degreeX f + degreeX g := by
  exact le_antisymm (degreeX_mul_le f g) (degreeX_mul_ge f g hf hg)

/-- The evaluation at a point of a bivariate polynomial in the first variable `X`. -/
def evalX (a : F) (f : F[X][Y]) : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/-- Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`. -/
def evalSetX [DecidableEq F] (f : F[X][Y]) (P : Finset F) [Nonempty P] : Finset (Polynomial F) :=
  P.image (fun a => evalX a f)

/-- The evaluation at a point of a bivariate polynomial in the second variable `Y`. -/
def evalY (a : F) (f : F[X][Y]) : Polynomial F := Polynomial.eval (Polynomial.C a) f

/-- Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`. -/
def evalSetY [DecidableEq F] (f : F[X][Y]) (P : Finset F) [Nonempty P] : Finset (Polynomial F) :=
  P.image (fun a => evalY a f)

/-- The bivariate quotient polynomial. -/
def quotient (f g : F[X][Y]) : Prop := ∃ q : F[X][Y], g = q * f

/-- The quotient of two non-zero bivariate polynomials is non-zero. -/
@[grind .]
lemma quotient_nezero {f q : F[X][Y]} (hg : q * f ≠ 0) : q ≠ 0 := by
  by_contra h
  apply hg
  simp [h]

/-- If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quotient are non-zero. -/
@[grind .]
lemma coeff_ne_zero {f q : F[X][Y]} (hg : q * f ≠ 0) : q.coeff ≠ 0 :=
  (ne_zero_iff_coeffs_ne_zero q).1 (quotient_nezero hg)

/-
If `q * f ≠ 0`, then the `X`-degree of `q` is bounded above by the difference of the
`X`-degrees: `degreeX q ≤ degreeX (q * f) - degreeX f`.
-/
@[grind .]
lemma degreeX_le_degreeX_sub_degreeX [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
    degreeX q ≤ degreeX (q * f) - degreeX f := by
  have hq : q ≠ 0 := quotient_nezero (f := f) (q := q) hg
  have hmul : degreeX (q * f) = degreeX q + degreeX f := degreeX_mul q f hq hf
  have hsum : degreeX q + degreeX f ≤ degreeX (q * f) := by
    simpa [hmul] using (le_rfl : degreeX q + degreeX f ≤ degreeX q + degreeX f)
  have hfb : degreeX f ≤ degreeX (q * f) := by
    exact le_trans (Nat.le_add_left _ _) hsum
  exact (Nat.le_sub_iff_add_le hfb).2 hsum

/-
If `q * f ≠ 0`, then the `Y`-degree of `q` is bounded above by the difference of the
`Y`-degrees: `natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f`.
-/
@[grind .]
lemma degreeY_le_degreeY_sub_degreeY [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
    natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f := by
  grind

end
end Polynomial.Bivariate
