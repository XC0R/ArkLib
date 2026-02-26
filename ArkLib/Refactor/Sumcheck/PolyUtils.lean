/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.OracleInterface
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Univariate.ToPoly

/-!
# CompPoly Utilities for Sumcheck

Self-contained CompPoly extensions needed for the sumcheck protocol:

- `OracleInterface` instances for `CMvPolynomial` and `CPolynomial`
- `CDegreeLE R d`: degree-bounded computable univariate polynomial
- `CPolynomial` eval / degree bridge lemmas (derived from `eval_toPoly` / `natDegree_toPoly`)
- General Lagrange interpolation for `CPolynomial R`

No dependency on the IOP framework (`ProtocolSpec`, `Prover`, etc.).
-/

open CompPoly CPoly

/-! ## OracleInterface instances -/

section OracleInterface

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

instance instOracleInterfaceCMvPolynomial :
    OracleInterface (CMvPolynomial n R) where
  Query := Fin n → R
  toOC := {
    spec := (Fin n → R) →ₒ R
    impl := fun points => do return CMvPolynomial.eval points (← read)
  }

variable [Nontrivial R]

instance instOracleInterfaceCPolynomial :
    OracleInterface (CPolynomial R) where
  Query := R
  toOC := {
    spec := R →ₒ R
    impl := fun point => do return CPolynomial.eval point (← read)
  }

end OracleInterface

/-! ## Degree-bounded computable univariate polynomial -/

/-- A computable univariate polynomial with `natDegree ≤ d`. Used as the message type
for sumcheck rounds (the prover sends a degree-bounded polynomial). -/
def CDegreeLE (R : Type) [BEq R] [Semiring R] [LawfulBEq R] (d : ℕ) :=
  { p : CPolynomial R // p.natDegree ≤ d }

namespace CDegreeLE

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] {d : ℕ}

instance : OracleInterface (CDegreeLE R d) where
  Query := R
  toOC := {
    spec := R →ₒ R
    impl := fun point => do return CPolynomial.eval point (← read).val
  }

def eval (x : R) (p : CDegreeLE R d) : R := CPolynomial.eval x p.val

end CDegreeLE

/-! ## CPolynomial toPoly preservation lemmas

These lift CompPoly's existing `toPoly_*` lemmas from `CPolynomial.Raw` to `CPolynomial`. -/

namespace CompPoly.CPolynomial

variable {R : Type} [CommRing R] [BEq R] [LawfulBEq R]

theorem toPoly_add' (p q : CPolynomial R) :
    (p + q).toPoly = p.toPoly + q.toPoly :=
  toPoly_addC p.val q.val

/-! ## CPolynomial eval bridge lemmas -/

theorem eval_add' (x : R) (p q : CPolynomial R) :
    eval x (p + q) = eval x p + eval x q := by
  simp only [eval_toPoly, toPoly_add', Polynomial.eval_add]

theorem eval_mul' (x : R) (p q : CPolynomial R) :
    eval x (p * q) = eval x p * eval x q := by
  simp only [eval_toPoly, toPoly_mul, Polynomial.eval_mul]

theorem eval_sum' {ι : Type} [DecidableEq ι] (x : R) (s : Finset ι) (f : ι → CPolynomial R) :
    eval x (s.sum f) = s.sum (fun i => eval x (f i)) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    change eval x 0 = 0
    rw [eval_toPoly]
    have : (0 : CPolynomial R).toPoly = 0 := by
      change (0 : CPolynomial.Raw R).toPoly = 0
      exact Raw.toPoly_zero
    rw [this, Polynomial.eval_zero]
  | cons a s ha ih =>
    rw [Finset.sum_cons, eval_add', ih, Finset.sum_cons]

/-! ## CPolynomial degree bridge lemmas -/

theorem natDegree_add_le' (p q : CPolynomial R) :
    natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  simp only [natDegree_toPoly, toPoly_add']
  exact Polynomial.natDegree_add_le p.toPoly q.toPoly

end CompPoly.CPolynomial

/-! ## General Lagrange interpolation

Given `n + 1` distinct evaluation points and corresponding values, construct the unique
polynomial of degree ≤ `n` interpolating these values. Fully computable. -/

namespace CompPoly.CPolynomial

variable {n : ℕ} {R : Type} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]

/-- The `i`-th Lagrange basis polynomial for the given set of evaluation points.
`lagrangeBasis pts i` is the unique polynomial of degree `n` that equals `1` at
`pts[i]` and `0` at all other `pts[j]`. -/
def lagrangeBasis (pts : Vector R (n + 1)) (i : Fin (n + 1)) : CPolynomial R :=
  (List.finRange (n + 1)).foldl (fun acc j =>
    if i = j then acc
    else acc * (X - C (pts[j])) * C (pts[i] - pts[j])⁻¹
  ) 1

/-- General Lagrange interpolation. Given `n + 1` points `pts` and `n + 1` values `vals`,
construct the polynomial `p` of degree ≤ `n` such that `p.eval pts[i] = vals[i]`. -/
def lagrangeInterpolate (pts vals : Vector R (n + 1)) : CPolynomial R :=
  (List.finRange (n + 1)).foldl (fun acc i =>
    acc + C (vals[i]) * lagrangeBasis pts i
  ) 0

theorem lagrangeInterpolate_natDegree (pts vals : Vector R (n + 1)) :
    (lagrangeInterpolate pts vals).natDegree ≤ n := by
  sorry

theorem lagrangeInterpolate_eval (pts vals : Vector R (n + 1))
    (h_distinct : pts.toList.Nodup) (i : Fin (n + 1)) :
    (lagrangeInterpolate pts vals).eval pts[i] = vals[i] := by
  sorry

end CompPoly.CPolynomial
