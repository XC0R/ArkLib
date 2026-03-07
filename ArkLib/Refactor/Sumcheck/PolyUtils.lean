/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.OracleInterface
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Univariate.ToPoly
import Init.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.LinearAlgebra.Lagrange

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
open scoped BigOperators

/-! ## Multivariate individual-degree bounds -/

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `p` has individual degree at most `deg` when every monomial exponent is bounded by `deg`
in every coordinate. This is the natural multivariate analogue of `natDegree ≤ deg`. -/
def IndividualDegreeLE (deg : ℕ) (p : CMvPolynomial n R) : Prop :=
  ∀ i : Fin n, ∀ mono ∈ Lawful.monomials p, mono.get i ≤ deg

end CPoly.CMvPolynomial

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

/-! ## Degree-bounded computable polynomial wrappers -/

/-- A computable univariate polynomial with `natDegree ≤ d`. Used as the message type
for sumcheck rounds (the prover sends a degree-bounded polynomial). -/
def CDegreeLE (R : Type) [BEq R] [Semiring R] [LawfulBEq R] (d : ℕ) :=
  { p : CPolynomial R // p.natDegree ≤ d }

/-- A computable `n`-variate polynomial with individual degree at most `d` in every
coordinate. This is the bundled statement type for sumcheck instances. -/
def CMvDegreeLE (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (n d : ℕ) :=
  { p : CMvPolynomial n R // CMvPolynomial.IndividualDegreeLE (R := R) d p }

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

namespace CMvDegreeLE

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] {n d : ℕ}

instance : OracleInterface (CMvDegreeLE R n d) where
  Query := Fin n → R
  toOC := {
    spec := (Fin n → R) →ₒ R
    impl := fun point => do return CMvPolynomial.eval point (← read).val
  }

def eval (x : Fin n → R) (p : CMvDegreeLE R n d) : R := CMvPolynomial.eval x p.val

end CMvDegreeLE

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

theorem eval_sum' {ι : Type} (x : R) (s : Finset ι) (f : ι → CPolynomial R) :
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

private def ofPoly (p : Polynomial R) : CPolynomial R :=
  ⟨p.toImpl, CompPoly.CPolynomial.Raw.trim_toImpl p⟩

omit [Nontrivial R] [DecidableEq R] in
private theorem ofPoly_toPoly (p : Polynomial R) :
    (ofPoly p).toPoly = p := by
  change CompPoly.CPolynomial.Raw.toPoly p.toImpl = p
  simpa using (CompPoly.CPolynomial.Raw.toPoly_toImpl (p := p))

omit [Nontrivial R] [DecidableEq R] in
private theorem toPoly_zero : (toPoly (0 : CPolynomial R)) = (0 : Polynomial R) := by
  change (CompPoly.CPolynomial.Raw.toPoly (0 : CompPoly.CPolynomial.Raw R)) = 0
  simpa using (CompPoly.CPolynomial.Raw.toPoly_zero (R := R))

omit [DecidableEq R] in
private theorem toPoly_one : (toPoly (1 : CPolynomial R)) = (1 : Polynomial R) := by
  change (CompPoly.CPolynomial.Raw.toPoly (1 : CompPoly.CPolynomial.Raw R)) = 1
  simp

omit [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] in
private theorem nodup_injOn_pts (pts : Vector R (n + 1))
    (h_distinct : pts.toList.Nodup) :
    Set.InjOn (fun i : Fin (n + 1) => pts[i]) (Finset.univ : Finset (Fin (n + 1))) := by
  intro i _hi j _hj hij
  apply Fin.ext
  have hi' : i.1 < pts.toList.length := by simpa using i.2
  have hj' : j.1 < pts.toList.length := by simpa using j.2
  have hlist : pts.toList[i.1] = pts.toList[j.1] := by
    simpa [Vector.getElem_toList hi', Vector.getElem_toList hj'] using hij
  exact (List.Nodup.getElem_inj_iff (l := pts.toList) h_distinct
    (i := i.1) (hi := hi') (j := j.1) (hj := hj')).1 hlist

/-- Precomputed data for repeated interpolation on fixed points. -/
structure InterpPlan (R : Type) [Field R] (n : ℕ) where
  pts : Vector R (n + 1)
  invDenoms : Vector R (n + 1)
  invDelta : Vector (Vector R (n + 1)) (n + 1)

/-- Compile an interpolation plan by precomputing all inverse Lagrange denominators. -/
def compileInterpPlan (pts : Vector R (n + 1)) : InterpPlan R n where
  pts := pts
  invDenoms := Vector.ofFn (fun i : Fin (n + 1) =>
    ((∏ j ∈ (Finset.univ.erase i), (pts[i] - pts[j])) : R)⁻¹)
  invDelta := Vector.ofFn (fun i : Fin (n + 1) =>
    Vector.ofFn (fun j : Fin (n + 1) =>
      if j.1 < i.1 then (pts[i] - pts[j])⁻¹ else 0))

/-- The `i`-th Lagrange basis polynomial for the given points and precomputed data. -/
def lagrangeBasisWithPlan (plan : InterpPlan R n) (i : Fin (n + 1)) : CPolynomial R :=
  C (plan.invDenoms[i]) * ∏ j ∈ (Finset.univ.erase i), (X + C (-plan.pts[j]))

/-- The `i`-th Lagrange basis polynomial for the given points. -/
def lagrangeBasis (pts : Vector R (n + 1)) (i : Fin (n + 1)) : CPolynomial R :=
  lagrangeBasisWithPlan (compileInterpPlan pts) i

private def interpPolyTermWithPlan (plan : InterpPlan R n) (vals : Vector R (n + 1))
    (i : Fin (n + 1)) : CPolynomial R :=
  C (vals[i] * plan.invDenoms[i]) *
    ∏ j ∈ (Finset.univ.erase i), (X + C (-plan.pts[j]))

/-- Proof-oriented interpolation spec used by theorem statements. -/
private def lagrangeInterpolateWithPlanSpec (plan : InterpPlan R n) (vals : Vector R (n + 1)) :
    CPolynomial R :=
  ∑ i : Fin (n + 1), interpPolyTermWithPlan plan vals i

private def rawCoeffGet {α : Type} (a : Array α) (i : Nat) (d : α) : α :=
  (a[i]?).getD d

private def rawCoeffGetR (a : Array R) (i : Nat) : R :=
  (a[i]?).getD 0

private def rawPolyEval (coeffs : Array R) (x : R) : R :=
  (coeffs.toList.reverse.foldl (fun acc a => acc * x + a) 0)

private def rawPolyScale (c : R) (coeffs : Array R) : Array R :=
  coeffs.map (fun a => c * a)

private def rawPolyAdd (p q : Array R) : Array R :=
  let m := max p.size q.size
  Array.ofFn (fun i : Fin m => rawCoeffGetR p i.1 + rawCoeffGetR q i.1)

/-- Multiply by `(X - x)` using a linear-time coefficient recurrence. -/
private def rawPolyMulXSubC (coeffs : Array R) (x : R) : Array R :=
  let m := coeffs.size
  Array.ofFn (fun i : Fin (m + 1) =>
    (if i.1 = 0 then 0 else rawCoeffGetR coeffs (i.1 - 1)) - x * rawCoeffGetR coeffs i.1)

private def rawDenomInv (invDelta : Array (Array R)) (k : Nat) : R :=
  (List.range k).foldl (fun acc j =>
    acc * rawCoeffGetR (rawCoeffGet invDelta k #[]) j) 1

private def newtonStep
    (pts vals : Array R) (invDelta : Array (Array R)) (k : Nat)
    (st : Array R × Array R) : Array R × Array R :=
  let coeffs := st.1
  let basis := st.2
  let xk := rawCoeffGetR pts k
  let yk := rawCoeffGetR vals k
  let denomInv := rawDenomInv invDelta k
  let corr := (yk - rawPolyEval coeffs xk) * denomInv
  let coeffs' := rawPolyAdd coeffs (rawPolyScale corr basis)
  let basis' := rawPolyMulXSubC basis xk
  (coeffs', basis')

private def newtonLoop
    (pts vals : Array R) (invDelta : Array (Array R)) :
    Nat → Nat → (Array R × Array R) → (Array R × Array R)
  | _, 0, st => st
  | k, fuel + 1, st => newtonLoop pts vals invDelta (k + 1) fuel
      (newtonStep pts vals invDelta k st)

private def lagrangeInterpolateWithPlanRawFastImpl
    (plan : InterpPlan R n) (vals : Vector R (n + 1)) : CPolynomial.Raw R := by
  let ptsArr : Array R := plan.pts.toArray
  let valsArr : Array R := vals.toArray
  let invArr : Array (Array R) := plan.invDelta.toArray.map (fun row => row.toArray)
  let x0 := rawCoeffGetR ptsArr 0
  let y0 := rawCoeffGetR valsArr 0
  let initCoeffs : Array R := #[y0]
  let initBasis : Array R := #[-x0, 1]
  let out := newtonLoop ptsArr valsArr invArr 1 n (initCoeffs, initBasis)
  exact out.1

private def lagrangeInterpolateWithPlanFast (plan : InterpPlan R n) (vals : Vector R (n + 1)) :
    CPolynomial R := by
  let _ := (inferInstance : LawfulBEq R)
  let _ := (inferInstance : Nontrivial R)
  refine ⟨(lagrangeInterpolateWithPlanRawFastImpl plan vals).trim, ?_⟩
  simpa using (CompPoly.CPolynomial.Raw.Trim.trim_twice
    (lagrangeInterpolateWithPlanRawFastImpl plan vals))

/-- Interpolate using a precompiled plan. -/
@[implemented_by lagrangeInterpolateWithPlanFast]
def lagrangeInterpolateWithPlan (plan : InterpPlan R n) (vals : Vector R (n + 1)) :
    CPolynomial R :=
  lagrangeInterpolateWithPlanSpec plan vals

/-- Raw interpolation output (unchecked/canonical raw representation) with precompiled plan. -/
def lagrangeInterpolateWithPlanRawFast (plan : InterpPlan R n) (vals : Vector R (n + 1)) :
    CPolynomial.Raw R :=
  (lagrangeInterpolateWithPlanRawFastImpl plan vals).trim

/-- Raw interpolation output (unchecked/canonical raw representation). -/
def lagrangeInterpolateRawFast (pts vals : Vector R (n + 1)) : CPolynomial.Raw R :=
  lagrangeInterpolateWithPlanRawFast (compileInterpPlan pts) vals

/-- General Lagrange interpolation. Given `n + 1` points `pts` and `n + 1` values `vals`,
construct the polynomial `p` of degree ≤ `n` such that `p.eval pts[i] = vals[i]`
when points are distinct. -/
def lagrangeInterpolate (pts vals : Vector R (n + 1)) : CPolynomial R :=
  lagrangeInterpolateWithPlan (compileInterpPlan pts) vals

omit [DecidableEq R] in
private theorem interpPolyTermWithPlan_toPoly (plan : InterpPlan R n)
    (vals : Vector R (n + 1)) (i : Fin (n + 1)) :
    (interpPolyTermWithPlan plan vals i).toPoly =
      Polynomial.C (vals[i] * plan.invDenoms[i]) *
        ∏ j ∈ (Finset.univ.erase i), (Polynomial.X - Polynomial.C (plan.pts[j])) := by
  unfold interpPolyTermWithPlan
  rw [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly]
  have hProd :
      (∏ j ∈ (Finset.univ.erase i), (X + C (-plan.pts[j]))).toPoly =
        ∏ j ∈ (Finset.univ.erase i), (Polynomial.X - Polynomial.C (plan.pts[j])) := by
    induction (Finset.univ.erase i : Finset (Fin (n + 1))) using Finset.induction_on with
    | empty =>
      simp [toPoly_one]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, CompPoly.CPolynomial.toPoly_mul, ih]
      rw [toPoly_add', CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.C_toPoly]
      simp [sub_eq_add_neg]
  rw [hProd]

omit [DecidableEq R] in
private theorem interpPolyTermWithPlan_toPoly_sum
    (plan : InterpPlan R n) (vals : Vector R (n + 1))
    (s : Finset (Fin (n + 1))) :
    (Finset.sum s (fun i => interpPolyTermWithPlan plan vals i)).toPoly =
      Finset.sum s (fun i => (interpPolyTermWithPlan plan vals i).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [toPoly_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, toPoly_add', ih]

omit [DecidableEq R] in
private theorem lagrangeInterpolateWithPlan_toPoly_terms (plan : InterpPlan R n)
    (vals : Vector R (n + 1)) :
    (lagrangeInterpolateWithPlan plan vals).toPoly =
      Finset.sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i => (interpPolyTermWithPlan plan vals i).toPoly) := by
  unfold lagrangeInterpolateWithPlan
  simpa using interpPolyTermWithPlan_toPoly_sum plan vals (Finset.univ : Finset (Fin (n + 1)))

omit [DecidableEq R] in
private theorem lagrangeInterpolateWithPlan_toPoly (plan : InterpPlan R n)
    (vals : Vector R (n + 1)) :
    (lagrangeInterpolateWithPlan plan vals).toPoly =
      ∑ i : Fin (n + 1),
        Polynomial.C (vals[i] * plan.invDenoms[i]) *
          ∏ j ∈ (Finset.univ.erase i), (Polynomial.X - Polynomial.C (plan.pts[j])) := by
  classical
  rw [lagrangeInterpolateWithPlan_toPoly_terms]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact interpPolyTermWithPlan_toPoly plan vals i

omit [DecidableEq R] in
private theorem interpPolyTermWithPlan_natDegree_le
    (plan : InterpPlan R n) (vals : Vector R (n + 1)) (i : Fin (n + 1)) :
    (interpPolyTermWithPlan plan vals i).toPoly.natDegree ≤ n := by
  rw [interpPolyTermWithPlan_toPoly plan vals i]
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hsumLe :
      (∑ j ∈ (Finset.univ.erase i), (Polynomial.X - Polynomial.C (plan.pts[j])).natDegree) ≤
        (∑ _j ∈ (Finset.univ.erase i), (1 : ℕ)) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact Polynomial.natDegree_X_sub_C_le (plan.pts[j])
  have hsumEq :
      (∑ _j ∈ (Finset.univ.erase i), (1 : ℕ)) = n := by
    have hcard :
        ((Finset.univ.erase i : Finset (Fin (n + 1))).card) = n := by
      simp
    calc
      (∑ _j ∈ (Finset.univ.erase i), (1 : ℕ)) =
          (Finset.univ.erase i : Finset (Fin (n + 1))).card := by simp
      _ = n := hcard
  exact hsumLe.trans (le_of_eq hsumEq)

omit [DecidableEq R] in
theorem lagrangeInterpolateWithPlan_natDegree (plan : InterpPlan R n)
    (vals : Vector R (n + 1)) :
    (lagrangeInterpolateWithPlan plan vals).natDegree ≤ n := by
  let f : Fin (n + 1) → Polynomial R := fun i => (interpPolyTermWithPlan plan vals i).toPoly
  rw [CompPoly.CPolynomial.natDegree_toPoly, lagrangeInterpolateWithPlan_toPoly_terms]
  have hsum :
      (∑ i : Fin (n + 1), f i).natDegree ≤
        Finset.fold max 0 (Polynomial.natDegree ∘ f) (Finset.univ : Finset (Fin (n + 1))) :=
    Polynomial.natDegree_sum_le (s := (Finset.univ : Finset (Fin (n + 1)))) (f := f)
  have hfold :
      Finset.fold max 0 (Polynomial.natDegree ∘ f) (Finset.univ : Finset (Fin (n + 1))) ≤ n :=
    (Finset.fold_max_le
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (b := 0)
      (f := Polynomial.natDegree ∘ f)
      (c := n)).2
      ⟨Nat.zero_le n, by
        intro i _hi
        simpa [f] using interpPolyTermWithPlan_natDegree_le plan vals i⟩
  exact hsum.trans hfold

omit [DecidableEq R] in
theorem lagrangeInterpolate_natDegree (pts vals : Vector R (n + 1)) :
    (lagrangeInterpolate pts vals).natDegree ≤ n := by
  simpa [lagrangeInterpolate] using
    (lagrangeInterpolateWithPlan_natDegree (plan := compileInterpPlan pts) (vals := vals))

omit [DecidableEq R] in
theorem lagrangeInterpolate_eval (pts vals : Vector R (n + 1))
    (h_distinct : pts.toList.Nodup) (i : Fin (n + 1)) :
    (lagrangeInterpolate pts vals).eval pts[i] = vals[i] := by
  classical
  rw [CompPoly.CPolynomial.eval_toPoly]
  have hPoly :
      (lagrangeInterpolate pts vals).toPoly =
        Lagrange.interpolate (s := (Finset.univ : Finset (Fin (n + 1))))
          (v := fun j => pts[j]) (fun j => vals[j]) := by
    calc
      (lagrangeInterpolate pts vals).toPoly
          = ∑ j : Fin (n + 1),
              Polynomial.C
                (vals[j] *
                  (∏ k ∈ (Finset.univ.erase j), (pts[j] - pts[k]))⁻¹) *
                ∏ k ∈ (Finset.univ.erase j), (Polynomial.X - Polynomial.C (pts[k])) := by
              simp [lagrangeInterpolate, lagrangeInterpolateWithPlan_toPoly,
                compileInterpPlan]
      _ = Lagrange.interpolate (s := (Finset.univ : Finset (Fin (n + 1))))
            (v := fun j => pts[j]) (fun j => vals[j]) := by
          symm
          simpa [div_eq_mul_inv] using (Lagrange.interpolate_eq_sum
            (s := (Finset.univ : Finset (Fin (n + 1))))
            (v := fun j => pts[j]) (r := fun j => vals[j]))
  rw [hPoly]
  simpa using Lagrange.eval_interpolate_at_node
    (r := fun j : Fin (n + 1) => vals[j])
    (hvs := nodup_injOn_pts (pts := pts) h_distinct)
    (hi := by simp)

end CompPoly.CPolynomial
