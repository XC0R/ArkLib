/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import ArkLib.Data.Probability.Instances
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import ArkLib.Data.CodingTheory.InterleavedCode
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.Logic.Equiv.Fin.Basic
import ArkLib.Data.CodingTheory.PolishchukSpielman.Degrees
import ArkLib.Data.CodingTheory.PolishchukSpielman

/-!
  # Definitions and Theorems about Proximity Gaps

  We state the main results from [BCIKS20] about proximity gap properties of Reed-Solomon codes.

  ## References

  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
      * NB we use version 20210703:203025

  ## Main Definitions and Statements

  - statement of Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].
  - statements of all the correlated agreement theorems from [BCIKS20]:
  Theorem 1.4 (Main Theorem — Correlated agreement over affine lines),
  Theorem 4.1 (Correlated agreement over affine lines in the unique decoding regime),
  Theorem 1.5 (Correlated agreement for low-degree parameterised curves)
  Theorem 1.6 (Correlated agreement over affine spaces).

-/

namespace ProximityGap

open NNReal Finset Function
open scoped BigOperators
open NNReal Finset Function ProbabilityTheory Finset
open scoped BigOperators LinearCode
open Code

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ (0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ ((1-ρ)/2 , 1 - √ρ)`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := ρ (ReedSolomon.code domain deg)
  if δ ∈ Set.Icc 0 ((1 - ρ)/2)
  then Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ)/2) (1 - ρ.sqrt)
       then letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0


/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].

Let `C` be a collection of affine spaces. Then `C` displays a `(δ, ε)`-proximity gap with respect to
a Reed-Solomon code, where `(δ,ε)` are the proximity and error parameters defined up to the
Johnson bound. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  δ_ε_proximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanFinsetCollection C)
    δ
    (errorBound δ deg domain) := by sorry

set_option linter.style.commandStart false

/-
Theorem 4.1. Suppose `δ ≤ (1-ρ) / 2`. Let `u_0, u_1: 𝒟 → 𝔽_q` be functions. Let
`S = {z ∈ 𝔽_q : Δ(u_0 + z u_1, V) ≤ δ}`
and suppose `|S| > n`. Then `S = 𝔽_q`. Furthermore there are `v_0, v_1 ∈ V` such that
for all `z ∈ 𝔽_q`, `Δ(u_0 + z u_1, v_0 + z v_1) ≤ δ`
and in fact `|{x ∈ 𝒟 : (u_0(x), u_1(x)) ≠ (v_0(x), v_1(x))}| ≤ δ|𝒟|.`
-/
def BW_homMatrix {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → R) (f : ι → R) :
    Matrix ι (Fin ((e + 1) + (e + k))) R :=
  Matrix.of fun i j =>
    if hj : (j.1 < e + 1) then
      f i * (ωs i) ^ j.1
    else
      - (ωs i) ^ (j.1 - (e + 1))

open Polynomial in
theorem BW_homMatrix_entry_natDegree_eq_zero_of_ge {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree = 0 := by
  classical
  have hle : ¬ (j.1 ≤ e) := by
    have hgt : e < j.1 := by
      exact lt_of_lt_of_le (Nat.lt_succ_self e) hj
    exact not_le_of_gt hgt
  -- reduce to the second branch
  simp [BW_homMatrix, hle]

open Polynomial in
theorem BW_homMatrix_entry_natDegree_eq_zero_of_ge_comm {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X) i j).natDegree = 0 := by
  have h :=
    BW_homMatrix_entry_natDegree_eq_zero_of_ge (ι := ι) (F := F) e k ωs f0 f1 i j hj
  have hfun :
      (fun i : ι => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
        = (fun i : ι => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X) := by
    funext i'
    rw [mul_comm Polynomial.X (Polynomial.C (f1 i'))]
  -- rewrite the auxiliary lemma with the commuting multiplication
  simpa [hfun] using h


open Polynomial in
theorem BW_homMatrix_entry_natDegree_le_one {F : Type} [Field F] {ι : Type} [Fintype ι] (e k : ℕ)
    (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree ≤ 1 := by
  classical
  by_cases hjle : (j.1 ≤ e)
  · -- j.1 ≤ e
    simp [BW_homMatrix, hjle, Nat.lt_succ_iff]
    have hlin :
        (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤ 1 := by
      have hadd :
          (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤
            max (Polynomial.C (f0 i) : F[X]).natDegree
              (Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree := by
        simpa using
          (Polynomial.natDegree_add_le (Polynomial.C (f0 i) : F[X])
            (Polynomial.C (f1 i) * Polynomial.X : F[X]))
      have hC : (Polynomial.C (f0 i) : F[X]).natDegree ≤ 1 := by
        simpa using (Nat.zero_le 1)
      have hX : (Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤ 1 := by
        simpa using
          (Polynomial.natDegree_mul_le (p := (Polynomial.C (f1 i) : F[X])) (q := (Polynomial.X : F[X])))
      exact le_trans hadd (max_le hC hX)
    have hq : ((Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree = 0 := by
      simp
    calc
      ((Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]) *
            (Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree ≤
          (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree +
            ((Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree := by
        exact
          (Polynomial.natDegree_mul_le (p := (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]))
            (q := (Polynomial.C (ωs i) : F[X]) ^ j.1))
      _ = (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree := by
        simp [hq]
      _ ≤ 1 := hlin
  · -- ¬ j.1 ≤ e
    simp [BW_homMatrix, hjle, Nat.lt_succ_iff]

open Polynomial in
theorem BW_homMatrix_map_evalRingHom {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs f0 f1 : ι → F) (z : F) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
          (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))).map
        (Polynomial.evalRingHom z)
      =
      BW_homMatrix (ι := ι) e k ωs (fun i => f0 i + z * f1 i) := by
  ext i j
  by_cases hje : (j.1 ≤ e)
  ·
    have hcomm : f1 i * z = z * f1 i := mul_comm (f1 i) z
    have : f1 i * z = z * f1 i ∨ ωs i = 0 ∧ ¬j = 0 := Or.inl hcomm
    simpa [BW_homMatrix, Nat.lt_succ_iff, hje, mul_add, add_mul] using this
  · simp [BW_homMatrix, Nat.lt_succ_iff, hje]

open scoped BigOperators in
theorem BW_homMatrix_mulVec_eq_zero_iff {R : Type} [CommRing R] {ι : Type} [Fintype ι] (e k : ℕ)
    (ωs : ι → R) (f : ι → R)
    (a : Fin (e + 1) → R) (b : Fin (e + k) → R) :
    Matrix.mulVec (BW_homMatrix (ι := ι) e k ωs f) (Fin.append a b) = 0 ↔
      (∀ i : ι,
        (∑ t : Fin (e + 1), a t * (ωs i) ^ t.1) * (f i)
          = ∑ s : Fin (e + k), b s * (ωs i) ^ s.1) := by
  classical

  -- helper facts to simplify the `if` guards coming from `BW_homMatrix`
  have hx : ∀ x : Fin (e + 1), (x.1 ≤ e) := fun x => Nat.le_of_lt_succ x.isLt
  have hy : ∀ x : Fin (e + k), ¬ (e + 1 + x.1 ≤ e) := by
    intro x hle
    have : e + 1 ≤ e := le_trans (Nat.le_add_right (e + 1) x.1) hle
    exact Nat.not_succ_le_self e this

  constructor
  · intro h i
    have hi := congrArg (fun v => v i) h
    have hi' :
        (∑ j : Fin ((e + 1) + (e + k)),
            BW_homMatrix (ι := ι) e k ωs f i j * Fin.append a b j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hi

    have hi'' := hi'
    rw [Fin.sum_univ_add] at hi''
    simp [BW_homMatrix, hx, hy] at hi''

    have hAC :
        (∑ x : Fin (e + 1), f i * ωs i ^ x.1 * a x) =
          ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
      have := eq_neg_of_add_eq_zero_left hi''
      simpa using this

    -- Convert `hAC` into the desired coefficientwise identity.
    calc
      (∑ t : Fin (e + 1), a t * ωs i ^ t.1) * f i
          = f i * (∑ t : Fin (e + 1), a t * ωs i ^ t.1) := by
              simpa [mul_comm]
      _ = ∑ t : Fin (e + 1), f i * (a t * ωs i ^ t.1) := by
              simpa [Finset.mul_sum]
      _ = ∑ t : Fin (e + 1), f i * ωs i ^ t.1 * a t := by
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
              simpa using hAC
      _ = ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
              simp [mul_comm]

  · intro h
    ext i

    -- expand the matrix-vector multiplication at coordinate `i`
    simp [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add]
    simp [BW_homMatrix, hx, hy]

    -- turn the hypothesis `h i` into the same normal form
    have hEq0 : f i * (∑ t : Fin (e + 1), a t * ωs i ^ t.1) =
        ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
      simpa [mul_comm] using h i

    have hEq1 : (∑ t : Fin (e + 1), f i * (a t * ωs i ^ t.1)) =
        ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
      simpa [Finset.mul_sum] using hEq0

    have hAC :
        (∑ x : Fin (e + 1), f i * ωs i ^ x.1 * a x) =
          ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
      -- rearrange products in `hEq1`
      simpa [mul_assoc, mul_left_comm, mul_comm] using hEq1

    -- use `hAC` to close the goal
    simpa [hAC]

open scoped BigOperators in
theorem Fin_sum_ite_lt_e_add_one (e k : ℕ) :
    #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} = e + 1 := by
  classical
  have hle : e + 1 ≤ (e + 1) + (e + k) := Nat.le_add_right (e + 1) (e + k)

  have hcard_lt0 :
      Fintype.card {i : Fin ((e + 1) + (e + k)) // i.1 < e + 1} = e + 1 :=
    Fintype.card_fin_lt_of_le (m := e + 1) (n := (e + 1) + (e + k)) hle

  have hcard_lt : #{i : Fin ((e + 1) + (e + k)) | i.1 < e + 1} = e + 1 := by
    simpa [Fintype.card_subtype] using hcard_lt0

  simpa [Nat.lt_succ_iff] using hcard_lt

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem BW_homMatrix_det_submatrix_natDegree_le_e_add_one {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι) :
    (Matrix.det
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) e k
            (fun i => (Polynomial.C (ωs i) : F[X]))
            (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
          r id)).natDegree ≤ e + 1 := by
  classical
  -- Name the matrices to keep subsequent expressions manageable.
  let M : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let A : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix M r id
  change (Matrix.det A).natDegree ≤ e + 1
  -- Expand determinant as a sum over permutations.
  rw [Matrix.det_apply]
  refine
    (Polynomial.natDegree_sum_le_of_forall_le
        (s :=
          (Finset.univ : Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), A (σ i) i)
        (n := e + 1) ?_)
  intro σ hσ
  -- The permutation sign is a unit (±1), so it does not increase natDegree.
  have hsign :
      (Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree ≤
        (∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  -- Degree of a product is bounded by the sum of degrees.
  have hprod :
      (∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree ≤
        ∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree := by
    simpa using
      (Polynomial.natDegree_prod_le
        (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
        (f := fun i : Fin ((e + 1) + (e + k)) => A (σ i) i))
  -- Only the first `e+1` columns can contribute degree (and each contributes at most 1).
  have hsum :
      (∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree) ≤ e + 1 := by
    have hpoint :
        ∀ i : Fin ((e + 1) + (e + k)),
          (A (σ i) i).natDegree ≤ ite (i.1 < e + 1) (1 : ℕ) 0 := by
      intro i
      by_cases hi : i.1 < e + 1
      · -- In the first `e+1` columns, each entry has natDegree ≤ 1.
        have hle1 :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree ≤ 1 :=
          BW_homMatrix_entry_natDegree_le_one (ι := ι) (F := F) e k ωs f0 f1
            (r (σ i)) i
        simpa [A, M, Matrix.submatrix, hi] using hle1
      · -- After column `e+1`, the entry is constant in `X`, hence natDegree = 0.
        have hi' : e + 1 ≤ i.1 := Nat.le_of_not_gt hi
        have hzero :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X)
                (r (σ i)) i).natDegree = 0 :=
          BW_homMatrix_entry_natDegree_eq_zero_of_ge_comm (ι := ι) (F := F) e k ωs
            f0 f1 (r (σ i)) i hi'
        have hzero' :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree = 0 := by
          -- For these columns, the definition of `BW_homMatrix` ignores the input `f`.
          simpa [BW_homMatrix, Nat.not_lt_of_ge hi'] using hzero
        have hA : (A (σ i) i).natDegree = 0 := by
          simpa [A, M, Matrix.submatrix] using hzero'
        simpa [hi, hA]
    have hle :
        (∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree)
          ≤
          ∑ i : Fin ((e + 1) + (e + k)), ite (i.1 < e + 1) (1 : ℕ) 0 := by
      simpa using
        (Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (fun i _ => hpoint i))
    -- `simp` rewrites this indicator sum into a cardinality, so rewrite the axiom the same way.
    have hcard :
        (#{x : Fin ((e + 1) + (e + k)) | (x.1 : ℕ) ≤ e} : ℕ) = e + 1 := by
      simpa [Nat.lt_succ_iff] using (Fin_sum_ite_lt_e_add_one (e := e) (k := k))
    -- Conclude.
    simpa [hcard] using hle
  -- Assemble the inequalities.
  exact le_trans hsign (le_trans hprod hsum)


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem BW_homMatrix_det_updateCol_natDegree_le_of_ge {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι)
    (i0 : Fin ((e + 1) + (e + k)))
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (Matrix.det
        (Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k
              (fun i => (Polynomial.C (ωs i) : F[X]))
              (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
            r id)
          j (Pi.single i0 (1 : F[X])))).natDegree ≤ e + 1 := by
  classical
  let A : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let B : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix A r id
  let B' : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.updateCol B j (Pi.single i0 (1 : F[X]))
  have hB' : (Matrix.det B').natDegree ≤ e + 1 := by
    -- Expand the determinant using Leibniz formula
    rw [Matrix.det_apply]
    -- Bound the natDegree of the sum by bounding each summand
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := (Finset.univ : Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (n := e + 1)
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i)
        ?_
    intro σ hσ
    -- Ignore the sign: it is ±1, so it does not increase natDegree
    have hsign :
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤
            (∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simp [hs]
      · simp [hs, Units.neg_smul]
    -- Bound degree of the product by the sum of degrees
    have hprod :
        (∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤
            ∑ i : Fin ((e + 1) + (e + k)), (B' (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i : Fin ((e + 1) + (e + k)) => B' (σ i) i))
    -- Bound each factor's natDegree by an indicator for the first (e+1) columns
    have hsum :
        (∑ i : Fin ((e + 1) + (e + k)), (B' (σ i) i).natDegree) ≤
            ∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0 := by
      classical
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i : Fin ((e + 1) + (e + k)) => (B' (σ i) i).natDegree)
          (g := fun i : Fin ((e + 1) + (e + k)) => if i.1 ≤ e then (1 : ℕ) else 0)
          (by
            intro i hi
            by_cases hij : i = j
            · -- updated column: entries are `Pi.single`, hence constant
              have hval : B' (σ i) i =
                  ((Pi.single i0 (1 : F[X])) : Fin ((e + 1) + (e + k)) → F[X]) (σ i) := by
                simpa [B', hij.symm] using
                  (Matrix.updateCol_self (M := B) (j := j) (c := Pi.single i0 (1 : F[X]))
                    (i := σ i))
              have hdeg : (B' (σ i) i).natDegree = 0 := by
                -- reduce to a constant polynomial (either `1` or `0`)
                rw [hval]
                by_cases hsi : σ i = i0
                · -- hit the support
                  rw [hsi]
                  simp
                · -- miss the support
                  have :
                      ((Pi.single i0 (1 : F[X])) : Fin ((e + 1) + (e + k)) → F[X]) (σ i) = 0 := by
                    simp [Pi.single, hsi]
                  simp [this]
              have hi0 : ¬(i.1 ≤ e) := by
                have hge : e + 1 ≤ i.1 := by
                  simpa [hij] using hj
                exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self e) hge)
              simp [hdeg, hi0]
            · -- non-updated column
              have hentry : (B' (σ i) i).natDegree = (A (r (σ i)) i).natDegree := by
                simp [B', B, Matrix.updateCol_apply, hij]
              by_cases hi0 : i.1 ≤ e
              · have hle : (A (r (σ i)) i).natDegree ≤ 1 := by
                  simpa [A] using
                    (BW_homMatrix_entry_natDegree_le_one (ι := ι) (F := F) e k ωs f0 f1
                      (r (σ i)) i)
                have : (B' (σ i) i).natDegree ≤ 1 := by
                  simpa [hentry] using hle
                simpa [hi0] using this
              · have hig : e + 1 ≤ i.1 := by
                  exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hi0)
                have hdeg0 : (A (r (σ i)) i).natDegree = 0 := by
                  simpa [A] using
                    (BW_homMatrix_entry_natDegree_eq_zero_of_ge (ι := ι) (F := F) e k ωs f0 f1
                      (r (σ i)) i hig)
                have : (B' (σ i) i).natDegree = 0 := by
                  simpa [hentry] using hdeg0
                simp [this, hi0]))
    -- Evaluate the indicator sum using the provided counting lemma
    have hcount :
        (∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0) = e + 1 := by
      classical
      have :
          (∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0) =
            #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} := by
        simpa using
          (Finset.card_filter (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
            (p := fun i : Fin ((e + 1) + (e + k)) => i.1 ≤ e)).symm
      simpa [this] using (Fin_sum_ite_lt_e_add_one (e := e) (k := k))
    -- Put everything together
    have :
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤ e + 1 := by
      calc
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤
            (∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree := hsign
        _ ≤ ∑ i : Fin ((e + 1) + (e + k)), (B' (σ i) i).natDegree := hprod
        _ ≤ ∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0 := hsum
        _ = e + 1 := hcount
    simpa using this
  simpa [A, B, B'] using hB'

open scoped BigOperators in
theorem Fin_sum_ite_lt_and_ne_eq_e (e k : ℕ) (j : Fin ((e + 1) + (e + k))) (hj : j.1 ≤ e) :
    #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} = e := by
  classical
  -- Let `n := (e+1) + (e+k)` and `S := {i : Fin n | i.1 ≤ e}`.
  let S : Finset (Fin ((e + 1) + (e + k))) := {i : Fin ((e + 1) + (e + k)) | i.1 ≤ e}

  have hScard : S.card = e + 1 := by
    simpa [S] using (Fin_sum_ite_lt_e_add_one e k)

  have hjS : j ∈ S := by
    simpa [S] using hj

  have hErase : (S.erase j).card = e := by
    calc
      (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hjS
      _ = (e + 1) - 1 := by simpa [hScard]
      _ = e := by simp

  have hEq : ({i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} : Finset (Fin ((e + 1) + (e + k)))) =
      S.erase j := by
    ext i
    by_cases hij : i = j
    · subst hij
      simp [S]
    · simp [S, hij, Finset.mem_erase, and_left_comm, and_assoc, and_comm]

  -- Rewrite the goal using the identification with `S.erase j`.
  simpa [hEq] using hErase

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem BW_homMatrix_det_updateCol_natDegree_le_of_lt {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι)
    (i0 : Fin ((e + 1) + (e + k)))
    (j : Fin ((e + 1) + (e + k))) (hj : j.1 < e + 1) :
    (Matrix.det
        (Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k
              (fun i => (Polynomial.C (ωs i) : F[X]))
              (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
            r id)
          j (Pi.single i0 (1 : F[X])))).natDegree ≤ e := by
  classical

  -- Abbreviations for the matrices involved
  let A : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let B : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix A r id
  let M : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.updateCol B j (Pi.single i0 (1 : F[X]))

  have hmain : (Matrix.det M).natDegree ≤ e := by
    -- Expand determinant via Leibniz formula and bound degrees termwise
    rw [Matrix.det_apply]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s :=
          (Finset.univ :
            Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (n := e)
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), M (σ i) i)
        ?_
    intro σ hσ

    -- the sign scalar does not increase natDegree
    have hsmul :
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), M (σ i) i).natDegree ≤
          (∏ i : Fin ((e + 1) + (e + k)), M (σ i) i).natDegree :=
      Polynomial.natDegree_smul_le (a := Equiv.Perm.sign σ)
        (p := ∏ i : Fin ((e + 1) + (e + k)), M (σ i) i)
    refine hsmul.trans ?_

    -- bound degree of product by sum of degrees
    have hprod :
        (∏ i : Fin ((e + 1) + (e + k)), M (σ i) i).natDegree ≤
          ∑ i : Fin ((e + 1) + (e + k)), (M (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i : Fin ((e + 1) + (e + k)) => M (σ i) i))
    refine hprod.trans ?_

    -- degree bound for each factor depending on the column
    have hterm :
        ∀ i : Fin ((e + 1) + (e + k)),
          (M (σ i) i).natDegree ≤ (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0) := by
      intro i
      by_cases hij : i = j
      · -- updated column: the entry is 0 or 1, hence natDegree 0
        have hdeg0 : (M (σ i) i).natDegree = 0 := by
          by_cases hrow : σ j = i0
          · simp [M, B, Matrix.updateCol_apply, hij, Pi.single, hrow]
          · simp [M, B, Matrix.updateCol_apply, hij, Pi.single, hrow]
        simpa [hij] using (le_of_eq hdeg0)
      · by_cases hle : i.1 ≤ e
        · have hdeg : (A (r (σ i)) i).natDegree ≤ 1 := by
            simpa [A] using
              (BW_homMatrix_entry_natDegree_le_one (e := e) (k := k) (ωs := ωs)
                (f0 := f0) (f1 := f1) (i := r (σ i)) (j := i))
          have hdeg' : (M (σ i) i).natDegree ≤ 1 := by
            simpa [M, B, Matrix.updateCol_apply, hij, Matrix.submatrix_apply, A] using hdeg
          simpa [hle, hij] using hdeg'
        · have hlt : e < i.1 := Nat.lt_of_not_ge hle
          have hge : e + 1 ≤ i.1 := Nat.succ_le_of_lt hlt
          have hdeg0 : (A (r (σ i)) i).natDegree = 0 := by
            simpa [A] using
              (BW_homMatrix_entry_natDegree_eq_zero_of_ge (e := e) (k := k) (ωs := ωs)
                (f0 := f0) (f1 := f1) (i := r (σ i)) (j := i) hge)
          have hdeg0' : (M (σ i) i).natDegree = 0 := by
            simpa [M, B, Matrix.updateCol_apply, hij, Matrix.submatrix_apply, A] using hdeg0
          simpa [hle, hij] using (le_of_eq hdeg0')

    have hsum_indicator :
        (∑ i : Fin ((e + 1) + (e + k)), (M (σ i) i).natDegree) ≤
          ∑ i : Fin ((e + 1) + (e + k)),
            (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0) := by
      classical
      simpa using
        (Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (fun i hi => hterm i))

    have hjle : j.1 ≤ e := Nat.lt_succ_iff.mp hj

    have hindicator_sum :
        (∑ i : Fin ((e + 1) + (e + k)),
            (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0 : ℕ)) = e := by
      classical
      have hsum_card :
          (∑ i : Fin ((e + 1) + (e + k)),
              (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0 : ℕ)) =
            #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} := by
        simpa using
          (Finset.sum_boole
            (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
            (p := fun i : Fin ((e + 1) + (e + k)) => i.1 ≤ e ∧ i ≠ j)
            (R := ℕ))
      simpa [hsum_card] using
        (Fin_sum_ite_lt_and_ne_eq_e (e := e) (k := k) (j := j) hjle)

    -- combine the bounds
    simpa [hindicator_sum] using hsum_indicator

  simpa [A, B, M] using hmain

theorem RS_BW_bound_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    2 * Nat.floor (δ * Fintype.card ι) < Fintype.card ι - deg + 1 := by
  classical
  set n : ℕ := Fintype.card ι
  set e : ℕ := Nat.floor (δ * n)
  have hnpos : (0 : ℝ≥0) < (n : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos (α := ι))
  have he_le_mul : (e : ℝ≥0) ≤ δ * n := by
    simpa [e] using (Nat.floor_le (a := δ * n) (ha := by positivity))
  have he_div_le_δ : (e : ℝ≥0) / n ≤ δ := by
    -- `div_le_iff₀` works in `ℝ≥0` as `n > 0`
    exact (div_le_iff₀ hnpos).2 he_le_mul
  have he_div_le_relUDR : (e : ℝ≥0) / n ≤
      Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg) :=
    le_trans he_div_le_δ hδ
  have he_le_UDR : e ≤ Code.uniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg) := by
    exact (Code.dist_le_UDR_iff_relDist_le_relUDR
      (C := (ReedSolomon.code domain deg : Set (ι → F))) e).2 he_div_le_relUDR
  have hdist_pos : 0 < n - deg + 1 := by
    omega
  have hdist_ne : (‖(ReedSolomon.code domain deg : Set (ι → F))‖₀) ≠ 0 := by
    have hdist_eq : ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ = n - deg + 1 := by
      simpa [n] using
        (ReedSolomonCode.dist_eq' (ι := ι) (F := F) (α := domain) (n := deg) hdeg)
    simpa [hdist_eq] using (ne_of_gt hdist_pos)
  haveI : NeZero (‖(ReedSolomon.code domain deg : Set (ι → F))‖₀) := ⟨hdist_ne⟩
  have htwo : 2 * e < ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ := by
    exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 he_le_UDR
  have hdist_eq : ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ = n - deg + 1 := by
    simpa [n] using
      (ReedSolomonCode.dist_eq' (ι := ι) (F := F) (α := domain) (n := deg) hdeg)
  simpa [n, e, hdist_eq] using htwo

open Matrix in
open Polynomial in
theorem RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F))
    (t : Fin (n + 1)) :
    B.adjugate t (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (t : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
  simpa [Fin.succAbove_last] using
    (Matrix.adjugate_fin_succ_eq_det_submatrix (A := B) (i := t) (j := Fin.last n))

open Matrix in
open Polynomial in
theorem RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F)) :
    B.adjugate (Fin.last n) (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
  -- apply the provided adjugate formula with t = Fin.last n
  simpa using
    (RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := n) (B := B) (t := Fin.last n))

open Matrix in
open Polynomial in
theorem RS_det_submatrix_eq_zero_of_det_eq_zero (n : ℕ)
    (K : Matrix (Fin n) (Fin n) (Polynomial F))
    (hdet : Matrix.det K = 0)
    (I J : Fin n ↪ Fin n) :
    Matrix.det (K.submatrix I J) = 0 := by
  classical
  let eI : Fin n ≃ Fin n := I.equivOfFiniteSelfEmbedding
  let eJ : Fin n ≃ Fin n := J.equivOfFiniteSelfEmbedding
  have hI : (eI.toEmbedding : Fin n ↪ Fin n) = I := by
    simpa [eI] using
      (Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding (e := I))
  have hJ : (eJ.toEmbedding : Fin n ↪ Fin n) = J := by
    simpa [eJ] using
      (Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding (e := J))
  have hsub : K.submatrix I J = K.submatrix eI eJ := by
    ext i j
    have hIi : eI i = I i := by
      have := congrArg (fun f : Fin n ↪ Fin n => f i) hI
      simpa [Equiv.toEmbedding_apply] using this
    have hJj : eJ j = J j := by
      have := congrArg (fun f : Fin n ↪ Fin n => f j) hJ
      simpa [Equiv.toEmbedding_apply] using this
    simp [Matrix.submatrix_apply, hIi, hJj]
  calc
    Matrix.det (K.submatrix I J) = Matrix.det (K.submatrix eI eJ) := by
      simpa [hsub]
    _ = Matrix.det (K.reindex eI.symm eJ.symm) := by
      simpa [Matrix.reindex_apply]
    _ = Equiv.Perm.sign (eJ.symm.trans eI) * Matrix.det K := by
      simpa [eI, eJ] using (Matrix.det_reindex (e := eI.symm) (e' := eJ.symm) K)
    _ = 0 := by
      simp [hdet]

open Matrix in
open Polynomial in
theorem RS_exists_nonzero_kernelVec_of_det_eq_zero {F : Type} [Field F] (e : ℕ)
    (K : Matrix (Fin (e + 1)) (Fin (e + 1)) (Polynomial F))
    (hdet : Matrix.det K = 0) :
    ∃ a : Fin (e + 1) → (Polynomial F), a ≠ 0 ∧ Matrix.mulVec K a = 0 := by
  classical
  rcases (Matrix.exists_mulVec_eq_zero_iff (M := K)).2 hdet with ⟨a, ha0, hmul⟩
  refine ⟨a, ha0, ?_⟩
  simpa using hmul

theorem RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    Nat.floor (δ * Fintype.card ι) + deg ≤ Fintype.card ι := by
  have hBW := RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hdeg hδ
  omega

theorem RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    Nat.floor (δ * Fintype.card ι) + 1 ≤ Fintype.card ι := by
  classical
  -- abbreviate the main numerals
  set n : ℕ := Fintype.card ι
  set e : ℕ := Nat.floor (δ * n)

  have heBW : 2 * e < n - deg + 1 := by
    simpa [n, e] using (RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hdeg hδ)

  have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
  have hdeg1 : 1 ≤ deg := Nat.succ_le_iff.2 hdegpos

  have hle : n - deg + 1 ≤ n := by
    calc
      n - deg + 1 ≤ n - deg + deg := by
        exact Nat.add_le_add_left hdeg1 (n - deg)
      _ = n := by
        exact Nat.sub_add_cancel (by simpa [n] using hdeg)

  have h2 : 2 * e < n := lt_of_lt_of_le heBW hle

  have hele : e ≤ 2 * e := by
    simpa [two_mul] using (Nat.le_add_left e e)

  have hlt : e < n := lt_of_le_of_lt hele h2

  -- finish
  simpa [n, e, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hlt)

noncomputable def RS_goodCoeffs {deg : ℕ} {domain : ι ↪ F}
    (u : WordStack F (Fin 2) ι) (δ : ℝ≥0) : Finset F :=
  Finset.filter (fun z : F => δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ) Finset.univ

open Polynomial in
theorem RS_exists_Pz_of_mem_goodCoeffs {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι) {z : F}
    (hz : z ∈ RS_goodCoeffs (deg := deg) (domain := domain) u δ) :
    ∃ Pz : F[X], Pz.natDegree < deg ∧
      Δ₀(u 0 + z • u 1, Pz.eval ∘ domain) ≤ Nat.floor (δ * Fintype.card ι) := by
  classical
  have hz' :
      z ∈
        Finset.filter
          (fun z : F => δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ)
          Finset.univ := by
    simpa [RS_goodCoeffs] using hz
  have hrel : δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ :=
    (Finset.mem_filter.mp hz').2

  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hdist :
      Δ₀(u 0 + z • u 1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h :=
      (Code.relDistFromCode_le_iff_distFromCode_le
          (u := u 0 + z • u 1) (C := (ReedSolomon.code domain deg : Set (ι → F)))
          (δ := δ)).1
        hrel
    simpa [e] using h

  rcases
      (Code.closeToCode_iff_closeToCodeword_of_minDist
            (u := u 0 + z • u 1) (C := (ReedSolomon.code domain deg : Set (ι → F)))
            (e := e)).1
        hdist with
    ⟨v, hvC, hvdist⟩

  rcases hvC with ⟨Pz, hPz, rfl⟩
  refine ⟨Pz, ?_, ?_⟩
  · exact ReedSolomonCode.natDegree_lt_of_mem_degreeLT (deg := deg) hPz
  · simpa [e] using hvdist

open scoped BigOperators in
open Polynomial in
theorem RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffs {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι) {z : F}
    (hz : z ∈ RS_goodCoeffs (deg := deg) (domain := domain) u δ) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F,
      ∃ b : Fin (e + deg) → F,
        a ≠ 0 ∧
          Matrix.mulVec
              (BW_homMatrix (ι := ι) e deg (fun i => domain i)
                (fun i => u 0 i + z * u 1 i))
              (Fin.append a b) = 0 := by
  classical
  -- Unfold the `let e := ...` in the goal, but avoid changing the quantifier structure
  simp only

  -- Name the error bound (this rewrites occurrences of the floor expression)
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he

  -- Get the close polynomial `Pz`
  obtain ⟨Pz, hPzdeg, hdist⟩ :=
    RS_exists_Pz_of_mem_goodCoeffs (deg := deg) (domain := domain) (δ := δ) u (z := z) hz
  have hdist' : Δ₀(u 0 + z • u 1, Pz.eval ∘ domain) ≤ e := by
    simpa [he] using hdist

  -- Extract a small set of disagreement coordinates
  obtain ⟨D, hDcard, hAgree⟩ :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols
        (u := u 0 + z • u 1)
        (v := Pz.eval ∘ domain)
        (e := e)).1 hdist'

  -- Error-locator polynomial and the corresponding `Q`
  set E : F[X] := ∏ i ∈ D, (Polynomial.X - Polynomial.C (domain i)) with hE
  set Q : F[X] := E * Pz with hQ

  -- Coefficient vectors (truncated to the required degrees)
  let a : Fin (e + 1) → F := fun t => E.coeff t.1
  let b : Fin (e + deg) → F := fun s => Q.coeff s.1

  have hE_monic : E.Monic := by
    -- `E` is a product of monic linear factors
    simpa [hE] using (Polynomial.monic_prod_X_sub_C (b := fun i : ι => domain i) (s := D))

  have hE_natDegree : E.natDegree = D.card := by
    -- degree of product of monic polynomials is sum of degrees
    have hdeg :=
      Polynomial.natDegree_prod_of_monic (s := D)
        (f := fun i : ι => (Polynomial.X - Polynomial.C (domain i) : F[X]))
        (by
          intro i hi
          simpa using (Polynomial.monic_X_sub_C (domain i)))
    -- simplify the RHS
    simpa [hE, Polynomial.natDegree_X_sub_C] using hdeg

  have hE_deg_lt : E.natDegree < e + 1 := by
    have : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    simpa [hE_natDegree] using this

  have hQ_deg_lt : Q.natDegree < e + deg := by
    -- `natDegree (E*Pz) ≤ natDegree E + natDegree Pz`
    have hmul : Q.natDegree ≤ E.natDegree + Pz.natDegree := by
      simpa [hQ] using (Polynomial.natDegree_mul_le (p := E) (q := Pz))
    have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPzdeg
    have hE_le : E.natDegree ≤ e := by
      simpa [hE_natDegree] using hDcard
    have hsum_le : E.natDegree + Pz.natDegree ≤ e + (deg - 1) := Nat.add_le_add hE_le hPz_le
    have hle : Q.natDegree ≤ e + (deg - 1) := le_trans hmul (by simpa [Nat.add_assoc] using hsum_le)
    -- turn into a strict inequality
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    have : e + (deg - 1) < e + deg :=
      Nat.add_lt_add_left (Nat.pred_lt (Nat.ne_of_gt hdegpos)) e
    exact lt_of_le_of_lt hle this

  -- `a` is nonzero because the leading coefficient of `E` is 1
  have ha_ne : a ≠ 0 := by
    have hcard_lt : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    let t0 : Fin (e + 1) := ⟨D.card, hcard_lt⟩
    have hcoeff : E.coeff D.card = 1 := by
      have hlead : E.leadingCoeff = 1 := hE_monic.leadingCoeff
      simpa [Polynomial.leadingCoeff, hE_natDegree] using hlead
    have ht0 : a t0 = 1 := by
      simpa [a, t0] using hcoeff
    intro hzero
    have hz0 : a t0 = 0 := by
      simpa using congrArg (fun f => f t0) hzero
    have h1 : (1 : F) = 0 := by simpa [ht0] using hz0
    exact one_ne_zero h1

  refine ⟨a, b, ha_ne, ?_⟩

  -- Show the vector is in the kernel via the characterization lemma
  apply (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (e := e) (k := deg)
      (ωs := fun i => domain i)
      (f := fun i => u 0 i + z * u 1 i)
      (a := a) (b := b)).2
  intro i

  -- Convert the coefficient sums into polynomial evaluations
  have hsum_a : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) = E.eval (domain i) := by
    have hfin : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1)
        = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n := by
      simpa [a] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => E.coeff n * (domain i) ^ n) (n := e + 1))
    have heval : E.eval (domain i) = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := E) (n := e + 1) hE_deg_lt (domain i)
    simpa [hfin] using heval.symm

  have hsum_b : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1) = Q.eval (domain i) := by
    have hfin : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1)
        = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n := by
      simpa [b] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => Q.coeff n * (domain i) ^ n) (n := e + deg))
    have heval : Q.eval (domain i) = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := Q) (n := e + deg) hQ_deg_lt (domain i)
    simpa [hfin] using heval.symm

  -- Reduce to showing `E.eval ω * f = Q.eval ω` and discharge by cases
  by_cases hiD : i ∈ D
  · -- On error positions, `E(ω_i)=0`
    have hE0 : E.eval (domain i) = 0 := by
      -- expand `E` and use that evaluation commutes with products
      rw [hE]
      rw [Polynomial.eval_prod (s := D)
        (p := fun j : ι => (Polynomial.X - Polynomial.C (domain j) : F[X]))
        (x := domain i)]
      refine Finset.prod_eq_zero hiD ?_
      simp

    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * (u 0 i + z * u 1 i)
          = (E.eval (domain i)) * (u 0 i + z * u 1 i) := by simpa [hsum_a]
      _ = 0 := by simp [hE0]
      _ = Q.eval (domain i) := by
            have hmul_eval : Q.eval (domain i) = (E.eval (domain i)) * (Pz.eval (domain i)) := by
              simpa [hQ] using (Polynomial.eval_mul (domain i) E Pz)
            simp [hmul_eval, hE0]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by simpa [hsum_b]

  · -- On agreement positions, `f_i = Pz(ω_i)`
    have hf_eq : (u 0 i + z * u 1 i) = Pz.eval (domain i) := by
      have := hAgree i hiD
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * (u 0 i + z * u 1 i)
          = (E.eval (domain i)) * (u 0 i + z * u 1 i) := by simpa [hsum_a]
      _ = (E.eval (domain i)) * (Pz.eval (domain i)) := by simp [hf_eq]
      _ = Q.eval (domain i) := by
            simpa [hQ] using (Polynomial.eval_mul (domain i) E Pz).symm
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by simpa [hsum_b]


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    let N : ℕ := (e + 1) + (e + deg)
    ∀ r : Fin N ↪ ι,
      Matrix.det
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e deg
              (fun i => (Polynomial.C (domain i) : F[X]))
              (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
            r id) = 0 := by
  classical
  dsimp
  intro r

  -- Abbreviations for the parameters appearing throughout
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  let N : ℕ := (e + 1) + (e + deg)

  -- The set of "good" coefficients
  let S : Finset F := RS_goodCoeffs (deg := deg) (domain := domain) u δ

  -- Polynomial matrix and its square submatrix
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg
      (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
  let A : Matrix (Fin N) (Fin N) F[X] :=
    Matrix.submatrix M (r : Fin N → ι) (id : Fin N → Fin N)

  -- Degree bound on det(A)
  have hdeg_det : (Matrix.det A).natDegree ≤ e + 1 := by
    simpa [A, M, N, e] using
      (BW_homMatrix_det_submatrix_natDegree_le_e_add_one (ι := ι) (F := F) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i)
        (r := (r : Fin N → ι)))

  -- Bound e+1 ≤ card ι
  have he1_le : e + 1 ≤ Fintype.card ι := by
    simpa [e] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) (hdeg := hdeg) (hδ := hδ))

  -- card ι < card S
  have hS' : Fintype.card ι < S.card := by
    simpa [S] using hS

  have he1_lt : e + 1 < S.card := lt_of_le_of_lt he1_le hS'
  have hdeg_lt : (Matrix.det A).natDegree < S.card := lt_of_le_of_lt hdeg_det he1_lt

  -- det(A) vanishes on all points of S
  have heval : ∀ z ∈ S, (Matrix.det A).eval z = 0 := by
    intro z hz

    have hz' : z ∈ RS_goodCoeffs (deg := deg) (domain := domain) u δ := by
      simpa [S] using hz

    -- Extract a nonzero kernel vector for the evaluated BW matrix
    have hk :=
      RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffs (deg := deg) (domain := domain)
        (δ := δ) (u := u) (z := z) hz'
    -- unfold the `let e := ...` in hk
    dsimp at hk
    rcases hk with ⟨a, b, ha0, hmul⟩

    let v : Fin N → F := Fin.append a b

    have hv_ne : v ≠ 0 := by
      intro hv
      apply ha0
      ext i
      have hvi : v (Fin.castAdd (e + deg) i) = (0 : Fin N → F) (Fin.castAdd (e + deg) i) :=
        congrArg (fun f => f (Fin.castAdd (e + deg) i)) hv
      simpa [v, N] using hvi

    let Mz : Matrix ι (Fin N) F :=
      BW_homMatrix (ι := ι) e deg (fun i => domain i) (fun i => u 0 i + z * u 1 i)

    have hmulMz : Mz *ᵥ v = 0 := by
      simpa [Mz, v, N, e] using hmul

    have hmulSub :
        (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v = 0 := by
      ext i
      have hi : (Mz *ᵥ v) (r i) = 0 := by
        simpa using congrArg (fun f => f (r i)) hmulMz
      simpa [Matrix.mulVec, Matrix.submatrix] using hi

    have hdetMz :
        Matrix.det (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) = 0 := by
      have hex : ∃ v' : Fin N → F, v' ≠ 0 ∧
          (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v' = 0 :=
        ⟨v, hv_ne, hmulSub⟩
      exact (Matrix.exists_mulVec_eq_zero_iff
        (M := Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N))).1 hex

    -- Relate evaluation of det(A) to determinant of the evaluated matrix
    have hdet_eval : (Matrix.det A).eval z = Matrix.det (A.map (Polynomial.eval z)) := by
      simpa [Polynomial.coe_evalRingHom] using (RingHom.map_det (Polynomial.evalRingHom z) A)

    -- Identify the mapped matrix with the evaluated BW matrix
    have hAmap : A.map (Polynomial.eval z) =
        Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N) := by
      have hMmap : M.map (Polynomial.eval z) = Mz := by
        simpa [M, Mz, N, e, Polynomial.coe_evalRingHom] using
          (BW_homMatrix_map_evalRingHom (ι := ι) (F := F) e deg (fun i => domain i)
            (fun i => u 0 i) (fun i => u 1 i) z)
      ext i j
      -- Unfold everything and reduce to the corresponding entry of `hMmap`
      simp [A, Matrix.submatrix, Matrix.map]
      -- rewrite the row of `Mz` using `hMmap`
      rw [← hMmap]
      simp [Matrix.map]

    -- conclude evaluation is zero
    rw [hdet_eval]
    simpa [hAmap] using hdetMz

  -- Root counting: det(A) has too many roots, hence is zero
  have hdetA0 : Matrix.det A = 0 := by
    exact
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p := Matrix.det A) (s := S) heval
        (by simpa using hdeg_lt)

  -- Finish: unfold A and M
  simpa [A, M, N, e] using hdetA0

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt_fun {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    let N : ℕ := (e + 1) + (e + deg)
    ∀ r : Fin N → ι,
      Matrix.det
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e deg
              (fun i => (Polynomial.C (domain i) : F[X]))
              (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
            r id) = 0 := by
  classical
  dsimp
  intro r
  by_cases hinj : Function.Injective r
  ·
    let r' : Fin ((Nat.floor (δ * Fintype.card ι) + 1) + (Nat.floor (δ * Fintype.card ι) + deg)) ↪ ι :=
      ⟨r, hinj⟩
    have h :=
      RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt
        (deg := deg) (domain := domain) (δ := δ) u hdeg hδ hS
    dsimp at h
    exact h r'
  ·
    have hinj' : ∃ i j : Fin ((Nat.floor (δ * Fintype.card ι) + 1) + (Nat.floor (δ * Fintype.card ι) + deg)),
        r i = r j ∧ i ≠ j := by
      -- unfold Injective and push negation
      have : ¬ (∀ i j, r i = r j → i = j) := by
        simpa [Function.Injective] using hinj
      push_neg at this
      -- `this` is now ∃ i j, r i = r j ∧ i ≠ j
      simpa [and_left_comm, and_assoc, and_comm] using this
    rcases hinj' with ⟨i, j, hij, hne⟩
    have hrow : (Matrix.submatrix
        (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
        r id) i =
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
          r id) j := by
      ext k
      simp [Matrix.submatrix, hij]
    -- determinant is zero due to repeated rows
    exact Matrix.det_zero_of_row_eq (M :=
        Matrix.submatrix
          (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
          r id) hne hrow


open Polynomial in
open Matrix in
theorem RS_isUnit_det_vandermonde_C_of_injective (n : ℕ) (v : Fin n → F) (hv : Function.Injective v) :
    IsUnit
      (Matrix.det
        (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])))) := by
  classical
  -- Rewrite goal using dot-notation for the determinant
  change IsUnit (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])) |>.det)

  -- The Vandermonde matrix over `F[X]` with constant entries is the entrywise image of the
  -- Vandermonde matrix over `F` under the ring hom `Polynomial.C`.
  have hdet :
      (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X]))).det =
        (Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det) := by
    have hvand :
        (Polynomial.C : F →+* F[X]).mapMatrix (Matrix.vandermonde v) =
          Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])) := by
      ext i j
      simp [Matrix.vandermonde]
    -- Map the determinant through `Polynomial.C` and rewrite the mapped matrix as a Vandermonde.
    simpa [hvand] using
      (RingHom.map_det (f := (Polynomial.C : F →+* F[X])) (M := Matrix.vandermonde v)).symm

  -- Over a field, the Vandermonde determinant is nonzero iff the entries are distinct.
  have hne : (Matrix.vandermonde v).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv

  -- In a field, nonzero elements are units.
  have hunit : IsUnit ((Matrix.vandermonde v).det) := (isUnit_iff_ne_zero).2 hne

  -- Constant polynomials are units iff their coefficients are units.
  have hunitC : IsUnit ((Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det)) :=
    (Polynomial.isUnit_C (x := (Matrix.vandermonde v).det)).2 hunit

  -- Conclude by rewriting the determinant as a constant polynomial.
  simpa [hdet] using hunitC

open Matrix in
open Polynomial in
theorem RS_mulVec_adjugate_col_eq_det (n : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial F)) (j : Fin n) :
    Matrix.mulVec A (fun i : Fin n => A.adjugate i j) = (fun i : Fin n => if i = j then Matrix.det A else 0) := by
  classical
  funext i
  calc
    Matrix.mulVec A (fun k : Fin n => A.adjugate k j) i = (A * A.adjugate) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    _ = (A.det • (1 : Matrix (Fin n) (Fin n) (Polynomial F))) i j := by
      simpa using
        congrArg (fun M : Matrix (Fin n) (Fin n) (Polynomial F) => M i j) (Matrix.mul_adjugate A)
    _ = (if i = j then Matrix.det A else 0) := by
      simp [Matrix.one_apply]

open Matrix in
open Polynomial in
theorem RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial F)) (j : Fin n)
    (hdet : Matrix.det A = 0) :
    Matrix.mulVec A (fun i : Fin n => A.adjugate i j) = 0 := by
  classical
  -- Rewrite using the adjugate column identity
  rw [RS_mulVec_adjugate_col_eq_det n A j]
  -- Now simplify using det A = 0
  ext i
  by_cases h : i = j
  · simp [h, hdet]
  · simp [h, hdet]


open scoped BigOperators in
open Matrix in
theorem RS_mulVec_append_castAdd_natAdd {R : Type} [NonUnitalNonAssocSemiring R] {ι : Type} [Fintype ι]
    (m n : ℕ) (M : Matrix ι (Fin (m + n)) R) (a : Fin m → R) (b : Fin n → R) :
    Matrix.mulVec M (Fin.append a b) =
      Matrix.mulVec (M.submatrix id (Fin.castAdd n)) a +
        Matrix.mulVec (M.submatrix id (Fin.natAdd m)) b := by
  classical
  -- check names
  have _ := (dotProduct : (Fin (m + n) → R) → (Fin (m + n) → R) → R)
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append, Matrix.submatrix]

open Polynomial in
open Matrix in
theorem RS_natDegree_det_le_of_entry_natDegree_le_one (n : ℕ) (A : Matrix (Fin n) (Fin n) F[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ 1) :
    (Matrix.det A).natDegree ≤ n := by
  classical
  rw [Matrix.det_apply]
  -- bound degree of the determinant by bounding each Leibniz summand
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)) ?_
  intro σ hσ
  -- ignore the scalar `sign σ` (it is ±1)
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)).natDegree
        ≤ (∏ i : Fin n, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  -- bound the product by summing the bounds on the factors
  have hprod : (∏ i : Fin n, A (σ i) i).natDegree ≤ n := by
    have h1 : (∏ i : Fin n, A (σ i) i).natDegree ≤ ∑ i : Fin n, (A (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => A (σ i) i))
    have h2 : (∑ i : Fin n, (A (σ i) i).natDegree) ≤ n := by
      -- each summand is ≤ 1 by hypothesis
      have hle1 : ∀ i : Fin n, (A (σ i) i).natDegree ≤ 1 := by
        intro i
        simpa using hdeg (σ i) i
      -- sum of `n` terms each ≤ 1
      have hsum' : (∑ i ∈ (Finset.univ : Finset (Fin n)), (A (σ i) i).natDegree)
          ≤ (Finset.univ : Finset (Fin n)).card • (1 : ℕ) := by
        refine Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (A (σ i) i).natDegree) (n := (1 : ℕ)) ?_
        intro i hi
        simpa using hle1 i
      -- rewrite sums/cards
      simpa [Finset.card_univ, Fintype.card_fin] using hsum'
    exact le_trans h1 h2
  exact le_trans hsign hprod

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_natDegree_inv_neg_vandermonde_C_eq_zero (n : ℕ) (v : Fin n → F) (hv : Function.Injective v) :
    ∀ i j : Fin n,
      ((-Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X])))⁻¹ i j).natDegree = 0 := by
  classical
  intro i j
  let f : F →+* F[X] := Polynomial.C
  let D0 : Matrix (Fin n) (Fin n) F := -Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) F[X] :=
    -Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X]))
  change ((D⁻¹ i j).natDegree = 0)

  have hDmap : D = D0.map f := by
    ext i j
    simp [D, D0, Matrix.vandermonde, Matrix.map_apply, f, map_pow]

  have hdetV : (Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
    simpa using (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv

  have hdetD0 : (Matrix.det D0) ≠ 0 := by
    have h : ((-1 : F) ^ (Fintype.card (Fin n)) * Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (by simp)) hdetV
    simpa [D0, Matrix.det_neg] using h

  have hunit0 : IsUnit (Matrix.det D0) := (isUnit_iff_ne_zero).2 hdetD0
  have hmul0 : D0 * D0⁻¹ = 1 := Matrix.mul_nonsing_inv D0 hunit0

  have hmul : (D0.map f) * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    simpa [Matrix.map_mul] using congrArg (fun A : Matrix (Fin n) (Fin n) F => A.map f) hmul0

  have hmul' : D * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    simpa [hDmap] using hmul

  have hinv : D⁻¹ = (D0⁻¹).map f := by
    exact Matrix.inv_eq_right_inv (A := D) (B := (D0⁻¹).map f) hmul'

  simpa [hinv, Matrix.map_apply, f]

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_vandermonde_coeffs_eq_zero (m : ℕ) {domain : ι ↪ F} (hm : m ≤ Fintype.card ι) (b : Fin m → F[X]) :
    (∀ i : ι,
      (∑ s : Fin m, b s * (Polynomial.C (domain i) : F[X]) ^ s.1) = 0) →
    b = 0 := by
  classical
  intro h
  let r0 : Fin m ↪ ι :=
    (Fin.castLEEmb hm).trans ((Fintype.equivFin ι).symm.toEmbedding)
  let v : Fin m → F[X] := fun j => (Polynomial.C (domain (r0 j)) : F[X])
  let V : Matrix (Fin m) (Fin m) F[X] := Matrix.vandermonde v
  have hv : Function.Injective v := by
    intro j₁ j₂ hj
    apply r0.injective
    apply domain.injective
    exact Polynomial.C_injective hj
  have hdet : V.det ≠ 0 := by
    simpa [V] using (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  have hmul : V *ᵥ b = 0 := by
    funext j
    have hj := h (r0 j)
    -- Expand the matrix-vector product.
    -- `mulVec` uses `∑ s, V j s * b s` while our hypothesis has `b s * ...`.
    -- Commutativity of multiplication in `F[X]` reconciles the order.
    simpa [Matrix.mulVec, dotProduct, V, v, mul_comm, mul_left_comm, mul_assoc] using hj
  exact Matrix.eq_zero_of_mulVec_eq_zero (M := V) hdet hmul


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_a_ne_zero_of_BW_homMatrix_mulVec_eq_zero {deg : ℕ} {domain : ι ↪ F} {e : ℕ}
    (u : WordStack F (Fin 2) ι)
    {a : Fin (e + 1) → F[X]} {b : Fin (e + deg) → F[X]}
    (hdeg : e + deg ≤ Fintype.card ι)
    (happend : Fin.append a b ≠ 0)
    (hMul :
      Matrix.mulVec
          (BW_homMatrix (ι := ι) e deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
          (Fin.append a b) = 0) :
    a ≠ 0 := by
  intro ha0
  -- Pointwise equality derived from the mulVec hypothesis
  have hEq :
      ∀ i : ι,
        (∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1) *
            (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 :=
    (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (R := F[X]) e deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i =>
            Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
          a b).1 hMul

  have hVand :
      ∀ i : ι,
        (∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1) = 0 := by
    intro i
    -- With a = 0, the left sum is 0, so the RHS must be 0.
    have hi := (hEq i).symm
    simpa [ha0] using hi

  have hb0 : b = 0 :=
    RS_vandermonde_coeffs_eq_zero (ι := ι) (F := F) (m := e + deg) (domain := domain) hdeg b hVand

  have happend0 : Fin.append a b = 0 := by
    ext i
    cases i using Fin.addCases <;> simp [ha0, hb0]

  exact happend happend0

open Matrix in
theorem adjugate_updateRow_same_col {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i j : n) (b : n → R) :
    (A.updateRow i b).adjugate j i = A.adjugate j i := by
  simp [Matrix.adjugate_apply]

theorem card_RS_goodCoeffs_gt_of_prob_gt_n_div_q {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (u : WordStack F (Fin 2) ι)
    (hprob :
      Pr_{let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ]
        > (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) :
    (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι := by
  classical
  -- predicate defining the good coefficients
  let P : F → Prop := fun z : F =>
    δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ

  -- uniform probability equals (card of filter) / (card of the field)
  have hPr :
      Pr_{ let z ← $ᵖ F }[ P z ] =
        ((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    classical
    -- Expand the probability mass at `True`
    simp only [Bind.bind, PMF.bind, PMF.uniformOfFintype_apply, pure, PMF.pure_apply, eq_iff_iff,
      mul_ite, mul_one, mul_zero, ENNReal.coe_natCast]
    simp only [DFunLike.coe, true_iff]
    -- Reduce the infinite sum to the finite support
    rw [
      tsum_eq_sum (α := ENNReal) (β := F)
        (f := fun a => if P a then (↑(Fintype.card F))⁻¹ else 0)
        (s := Finset.filter P Finset.univ)
        (hf := fun b => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hb
          simp only [hb, if_false])
    ]
    -- Evaluate the resulting finite sum
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul']
    rw [mul_comm]
    conv_lhs =>
      rw [← div_eq_mul_inv]
    -- Filtering twice is the same as filtering once
    have h_card_eq : {x ∈ filter P univ | P x} = filter P univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [and_self_iff]
    rw [h_card_eq]

  -- restate the hypothesis using `P`
  have hprobP :
      Pr_{ let z ← $ᵖ F }[ P z ] > (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    simpa [P] using hprob

  -- rewrite the probability lower bound as a ratio comparison
  have hprobQ := hprobP
  rw [hPr] at hprobQ

  -- switch to `<` form
  have hlt :
      ((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal)
        < (((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal) :=
    (gt_iff_lt).1 hprobQ

  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ := by
    simpa using ENNReal.natCast_ne_top (Fintype.card F)

  have hcard_cast : (Fintype.card ι : ENNReal) < ((Finset.filter (α := F) P Finset.univ).card : ENNReal) := by
    -- rewrite both sides of `hlt` as ENNReal divisions and cancel
    have hlt' :
        (Fintype.card ι : ENNReal) / (Fintype.card F : ENNReal)
          < ((Finset.filter (α := F) P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal) := by
      have hq0' : (Fintype.card F : ℝ≥0) ≠ 0 := by
        simp [Fintype.card_ne_zero]
      simpa [ENNReal.coe_div (r := (Fintype.card F : ℝ≥0)) hq0', ENNReal.coe_natCast] using hlt
    exact (ENNReal.div_lt_div_iff_left (hc₀ := hq0) (hc := hqtop)).1 hlt'

  have hcard_nat : Fintype.card ι < (Finset.filter (α := F) P Finset.univ).card := by
    exact Nat.cast_lt.mp hcard_cast

  -- identify the filtered finset with `RS_goodCoeffs`
  simpa [RS_goodCoeffs, P, gt_iff_lt] using hcard_nat


open scoped BigOperators in
open Matrix in
theorem det_updateRow_eq_sum_mul_adjugate_col {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i : n) (b : n → R) :
    (A.updateRow i b).det = ∑ j : n, b j * A.adjugate j i := by
  classical
  -- Laplace expansion of the determinant along the updated row
  simpa [Matrix.updateRow_apply, adjugate_updateRow_same_col, mul_assoc] using
    (Matrix.det_eq_sum_mul_adjugate_row (A := A.updateRow i b) (i := i))


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_exists_nonzero_kernelVec_of_det_eq_zero_natDegree_le_one (e : ℕ)
    (K : Matrix (Fin (e + 1)) (Fin (e + 1)) F[X])
    (hdeg : ∀ i j, (K i j).natDegree ≤ 1)
    (hdet : Matrix.det K = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ 0

  have hP0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    simpa using (one_ne_zero : (1 : F[X]) ≠ 0)

  let r : ℕ := Nat.findGreatest P n
  have hPr : P r := by
    have h :=
      Nat.findGreatest_spec (P := P) (m := 0) (n := n) (Nat.zero_le n) hP0
    simpa [r] using h
  rcases hPr with ⟨I, J, hIJ⟩

  have hPn : ¬ P n := by
    intro h
    rcases h with ⟨I0, J0, hdet0⟩
    have hzero := RS_det_submatrix_eq_zero_of_det_eq_zero n K hdet I0 J0
    exact hdet0 hzero

  have hr_le : r ≤ n := by
    simpa [r] using (Nat.findGreatest_le (P := P) n)

  have hr_lt : r < n := by
    have hr_ne : r ≠ n := by
      intro hEq
      have : P n := by
        simpa [hEq] using (show P r from ⟨I, J, hIJ⟩)
      exact hPn this
    exact lt_of_le_of_ne hr_le hr_ne

  have hr_le_e : r ≤ e := by
    have : r < e + 1 := by
      simpa [n] using hr_lt
    exact (Nat.lt_succ_iff.mp this)

  have hnotP_succ : ¬ P (r + 1) := by
    have hr1_le : r + 1 ≤ n := Nat.succ_le_of_lt hr_lt
    have hk : Nat.findGreatest P n < r + 1 := by
      simpa [r] using (Nat.lt_succ_self (Nat.findGreatest P n))
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hr1_le

  have hcard_lt_I : (Finset.univ.map I).card < (Finset.univ : Finset (Fin n)).card := by
    simpa [Finset.card_map, Finset.card_univ, Fintype.card_fin] using hr_lt
  obtain ⟨i0, -, hi0_not_mem⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt_I
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨t, rfl⟩
    have : (I t) ∈ (Finset.univ.map I) := by
      simpa using (Finset.mem_map'.2 (Finset.mem_univ t))
    exact hi0_not_mem this

  have hcard_lt_J : (Finset.univ.map J).card < (Finset.univ : Finset (Fin n)).card := by
    simpa [Finset.card_map, Finset.card_univ, Fintype.card_fin] using hr_lt
  obtain ⟨j0, -, hj0_not_mem⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt_J
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨t, rfl⟩
    have : (J t) ∈ (Finset.univ.map J) := by
      simpa using (Finset.mem_map'.2 (Finset.mem_univ t))
    exact hj0_not_mem this

  let I' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0

  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'

  have hdetB : Matrix.det B = 0 := by
    by_contra h
    exact hnotP_succ ⟨I', J', h⟩

  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)

  have hBu : Matrix.mulVec B u = 0 := by
    simpa [u] using
      (RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB)

  have hu_last : u (Fin.last r) ≠ 0 := by
    have hAdj := RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)

    have hBsub : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
      ext i j
      simp [B, I', J', Fin.Embedding.snoc_castSucc]

    have hUL :
        u (Fin.last r) =
          (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) * Matrix.det (K.submatrix I J) := by
      dsimp [u]
      rw [hAdj]
      set_option maxHeartbeats 400000 in
      simpa [hBsub]

    have hsign :
        ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) ≠ 0 := by
      have hbase : (-1 : F[X]) ≠ 0 := by
        simpa using (neg_ne_zero.mpr (one_ne_zero : (1 : F[X]) ≠ 0))
      exact pow_ne_zero _ hbase

    rw [hUL]
    set_option maxHeartbeats 400000 in
    exact mul_ne_zero hsign hIJ

  have hu_ne : u ≠ 0 := by
    intro hu0
    have h := congrArg (fun f => f (Fin.last r)) hu0
    have : u (Fin.last r) = 0 := by
      simpa using h
    exact hu_last this

  have hu_deg : ∀ t, (u t).natDegree ≤ e := by
    intro t
    have hAdj :
        u t =
          (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
            Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
      dsimp [u]
      exact RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)

    let M : Matrix (Fin r) (Fin r) F[X] := B.submatrix Fin.castSucc t.succAbove

    have hdegM : ∀ i j, (M i j).natDegree ≤ 1 := by
      intro i j
      dsimp [M, B]
      exact hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))

    have hdetMdeg : (Matrix.det M).natDegree ≤ r :=
      RS_natDegree_det_le_of_entry_natDegree_le_one r M hdegM

    have hmuldeg : (u t).natDegree ≤ (Matrix.det M).natDegree := by
      rw [hAdj]
      dsimp [M]
      have hconst :
          (-1 : F[X]) ^ (r + (t : ℕ)) = Polynomial.C ((-1 : F) ^ (r + (t : ℕ))) := by
        simp
      rw [hconst]
      exact Polynomial.natDegree_C_mul_le _ _

    have : (u t).natDegree ≤ r := le_trans hmuldeg hdetMdeg
    exact le_trans this hr_le_e

  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)

  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := by
    intro t
    simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)

  have ha_ne : a ≠ 0 := by
    intro ha0
    have h := congrArg (fun f => f (J' (Fin.last r))) ha0
    have ha_last : a (J' (Fin.last r)) = 0 := by
      simpa using h
    have : u (Fin.last r) = 0 := by
      calc
        u (Fin.last r) = a (J' (Fin.last r)) := by
          symm
          exact ha_on (Fin.last r)
        _ = 0 := ha_last
    exact hu_last this

  have ha_deg : ∀ t, (a t).natDegree ≤ e := by
    intro t
    by_cases ht : ∃ s : Fin (r + 1), (J' s : Fin n) = t
    · rcases ht with ⟨s, rfl⟩
      simpa [ha_on s] using hu_deg s
    · have : a t = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := t) ht)
      simpa [this] using (Nat.zero_le e)

  have hmulVec_eq (i : Fin n) :
      (Matrix.mulVec K a) i = ∑ j : Fin (r + 1), K i (J' j) * u j := by
    classical
    have houtside :
        ∀ j : Fin n,
          j ∉ Set.range (J' : Fin (r + 1) → Fin n) → K i j * a j = 0 := by
      intro j hj
      have hj' : ¬ ∃ t : Fin (r + 1), (J' t : Fin n) = j := hj
      have ha0 : a j = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := j) hj')
      simp [ha0]

    have hsum :
        (∑ j : Fin n, K i j * a j) = ∑ t : Fin (r + 1), K i (J' t) * a (J' t) := by
      have h :=
        (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
          (f := fun t : Fin (r + 1) => K i (J' t) * a (J' t))
          (g := fun j : Fin n => K i j * a j) (h' := houtside) (h := fun t => rfl))
      exact h.symm

    calc
      (Matrix.mulVec K a) i = ∑ j : Fin n, K i j * a j := by
        rfl
      _ = ∑ t : Fin (r + 1), K i (J' t) * a (J' t) := hsum
      _ = ∑ t : Fin (r + 1), K i (J' t) * u t := by
        refine Fintype.sum_congr _ _ ?_
        intro t
        rw [ha_on t]

  have hKa : Matrix.mulVec K a = 0 := by
    funext i
    have hrewrite := hmulVec_eq i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hBu_t : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
        have := congrArg (fun f => f (Fin.castSucc t)) hBu
        simpa using this

      have hBsum :
          (Matrix.mulVec B u) (Fin.castSucc t) = ∑ j : Fin (r + 1), K (I t) (J' j) * u j := by
        simp [B, I', Matrix.mulVec, dotProduct, Fin.Embedding.snoc_castSucc]

      have hsum0 : (∑ j : Fin (r + 1), K (I t) (J' j) * u j) = 0 := by
        simpa [hBsum] using hBu_t

      exact hrewrite.trans hsum0

    · have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc I hi'
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)

      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        ext irow jcol
        cases irow using Fin.lastCases with
        | last =>
            simp [B, I', Ii, b, Matrix.updateRow, Fin.Embedding.snoc_last]
        | cast t =>
            simp [B, I', Ii, b, Matrix.updateRow, Fin.Embedding.snoc_castSucc]

      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra h
        exact hnotP_succ ⟨Ii, J', h⟩

      have hdetUpdate : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        simpa [hupdate] using hdetBi

      have hsum_eq_det :
          (∑ j : Fin (r + 1), K i (J' j) * u j) = Matrix.det (B.updateRow (Fin.last r) b) := by
        simpa [b, u] using
          (det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)).symm

      have hsum0 : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
        simpa [hsum_eq_det] using hdetUpdate

      exact hrewrite.trans hsum0

  refine ⟨a, ha_ne, ha_deg, ?_⟩
  simpa [a, n] using hKa

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one (e : ℕ)
    (K : Matrix ι (Fin (e + 1)) F[X])
    (hcard : e + 1 ≤ Fintype.card ι)
    (hdeg : ∀ i j, (K i j).natDegree ≤ 1)
    (hdet : ∀ r : Fin (e + 1) → ι, Matrix.det (K.submatrix r id) = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I : Fin r ↪ ι) (J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ (0 : F[X])
  letI : DecidablePred P := Classical.decPred _

  have P0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    simp [P]

  let r : ℕ := Nat.findGreatest P n
  have Pr : P r := by
    simpa [r] using
      (Nat.findGreatest_spec (P := P) (n := n) (m := 0) (Nat.zero_le n) P0)
  rcases Pr with ⟨I, J, hdetIJ⟩

  have hnotPn : ¬ P n := by
    intro hPn
    rcases hPn with ⟨I0, J0, hdet0⟩
    let A : Matrix (Fin n) (Fin n) F[X] := K.submatrix I0 id
    have hdetA : Matrix.det A = 0 := by
      simpa [A] using hdet I0
    have hdet_sub : Matrix.det (A.submatrix (Function.Embedding.refl _) J0) = 0 :=
      RS_det_submatrix_eq_zero_of_det_eq_zero n A hdetA (Function.Embedding.refl _) J0
    have hdetK : Matrix.det (K.submatrix I0 J0) = 0 := by
      simpa [A] using hdet_sub
    exact hdet0 hdetK

  have hrle : r ≤ n := by
    simpa [r] using (Nat.findGreatest_le (P := P) n)

  have hrne : r ≠ n := by
    intro hre
    have hEq : Nat.findGreatest P n = n := by
      simpa [r] using hre
    have hcond : n ≠ 0 → P n :=
      (Nat.findGreatest_eq_iff (P := P) (k := n) (m := n)).1 hEq |>.2.1
    have hn0 : n ≠ 0 := by
      simp [n]
    exact hnotPn (hcond hn0)

  have hrlt : r < n := Nat.lt_of_le_of_ne hrle hrne
  have hrle_e : r ≤ e := by
    have : r < e + 1 := by
      simpa [n] using hrlt
    exact Nat.lt_succ_iff.mp this

  have hcard' : n ≤ Fintype.card ι := by
    simpa [n] using hcard
  have hrltcardι : r < Fintype.card ι := lt_of_lt_of_le hrlt hcard'

  -- pick i0 ∉ range I
  let sI : Finset ι := Finset.univ.map I
  have hsIlt : sI.card < (Finset.univ : Finset ι).card := by
    simpa [sI] using hrltcardι
  obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨i, rfl⟩
    apply hi0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨i, by simp, rfl⟩

  -- pick j0 ∉ range J
  let sJ : Finset (Fin n) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin n)).card := by
    simpa [sJ] using hrlt
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨j, rfl⟩
    apply hj0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨j, by simp, rfl⟩

  let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'

  have hnotPr1 : ¬ P (r + 1) := by
    have hk : Nat.findGreatest P n < r + 1 := by
      simpa [r] using Nat.lt_succ_self r
    have hkb : r + 1 ≤ n := Nat.succ_le_of_lt hrlt
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hkb

  have hdetB : Matrix.det B = 0 := by
    by_contra hne
    have : P (r + 1) := ⟨I', J', by simpa [B] using hne⟩
    exact hnotPr1 this

  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 := by
    simpa [u] using
      RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB

  have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
    funext i
    funext j
    simp [B, I', J']

  have hu_last : u (Fin.last r) =
      (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
    simpa [u] using RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)

  have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
    have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) := by
      have hminus1 : (-1 : F[X]) ≠ (0 : F[X]) := by simp
      exact pow_ne_zero _ hminus1
    have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
      simpa [hsub_cast] using hdetIJ
    rw [hu_last]
    exact mul_ne_zero hsign hdetMinor

  -- degree bound on u
  have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ r := by
    intro t
    have hu_t : u t =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
      simpa [u] using RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)

    have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r := by
      apply RS_natDegree_det_le_of_entry_natDegree_le_one (n := r)
        (A := B.submatrix Fin.castSucc t.succAbove)
      intro i j
      -- entries come from K
      simpa [B] using hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))

    have hdeg_sign : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by
      simp

    have hmul_le :
        (u t).natDegree ≤
          ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree := by
      simpa [hu_t] using
        (Polynomial.natDegree_mul_le
          (p := (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)))
          (q := Matrix.det (B.submatrix Fin.castSucc t.succAbove)))

    have hdeg_rhs :
        ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r := by
      simpa [hdeg_sign] using hdeg_det

    exact le_trans hmul_le hdeg_rhs

  -- extend u to all columns
  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)

  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := by
    intro t
    simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)

  have ha_ne : a ≠ 0 := by
    intro ha0
    have hval : a (J' (Fin.last r)) = 0 := by
      simpa using congrArg (fun f : Fin n → F[X] => f (J' (Fin.last r))) ha0
    have : u (Fin.last r) = 0 := by
      simpa [ha_on (Fin.last r)] using hval
    exact hu_last_ne this

  have hdeg_a : ∀ j : Fin n, (a j).natDegree ≤ e := by
    intro j
    by_cases hj : ∃ t : Fin (r + 1), J' t = j
    · rcases hj with ⟨t, rfl⟩
      exact le_trans (by simpa [ha_on t] using hdeg_u t) hrle_e
    · have haj : a j = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := j) hj)
      simp [haj]

  have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
    have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin n, K i j * a j := by
      refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
        (f := fun t : Fin (r + 1) => K i (J' t) * u t)
        (g := fun j : Fin n => K i j * a j) ?_ ?_)
      · intro j hj
        have hb : ¬∃ t : Fin (r + 1), (J' t) = j := by
          simpa [Set.mem_range] using hj
        have haj : a j = 0 := by
          simpa [a] using
            (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
              (b := j) hb)
        simp [haj]
      · intro t
        simp [ha_on t]
    simpa [Matrix.mulVec] using hsum.symm

  have hmulVec : Matrix.mulVec K a = 0 := by
    funext i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hrow : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
        have := congrArg (fun v : Fin (r + 1) → F[X] => v (Fin.castSucc t)) hBu
        simpa using this
      have hrow' : (∑ x : Fin (r + 1), K (I t) (J' x) * u x) = 0 := by
        simpa [Matrix.mulVec, B, I', J'] using hrow
      rw [hmul_formula (i := I t)]
      simpa using hrow'
    · -- i ∉ range I
      have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra hne
        have : P (r + 1) := ⟨Ii, J', by simpa using hne⟩
        exact hnotPr1 this
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        funext x
        funext y
        refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
            (K.submatrix Ii J') x y) ?_ ?_ x
        · -- x = last
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
        · intro x
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
      have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        simpa [hupdate] using hdetBi
      have hdet_expr : Matrix.det (B.updateRow (Fin.last r) b) =
          ∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r) := by
        simpa using
          det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)
      have hsum0 : (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0 := by
        simpa [hdet_expr] using hdet_update
      have hsum0' : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
        simpa [b, u] using hsum0
      rw [hmul_formula (i := i)]
      simpa using hsum0'

  refine ⟨a, ha_ne, ?_, hmulVec⟩
  intro t
  simpa using hdeg_a t


open scoped BigOperators in
open Polynomial in
open Matrix in
open BerlekampWelch in
theorem RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F[X],
      ∃ b : Fin (e + deg) → F[X],
        Fin.append a b ≠ 0 ∧
          (∀ t, (a t).natDegree ≤ e) ∧
            (∀ s, (b s).natDegree ≤ e + 1) ∧
              Matrix.mulVec
                  (BW_homMatrix (ι := ι) e deg
                    (fun i => (Polynomial.C (domain i) : F[X]))
                    (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
                  (Fin.append a b) = 0 := by
  classical
  -- unfold the initial `let e := ...`
  simp (config := { zeta := true })
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  let m : ℕ := e + 1
  let n : ℕ := e + deg
  let N : ℕ := m + n
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))

  have hdetM : ∀ r : Fin N → ι, Matrix.det (Matrix.submatrix M r id) = 0 := by
    intro r
    simpa [M, N, m, n, he] using
      (RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt_fun (deg := deg)
        (domain := domain) (δ := δ) (u := u) hdeg hδ hS r)

  have hcard_n : n ≤ Fintype.card ι := by
    simpa [n, e, he] using
      (RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) hdeg hδ)

  obtain ⟨rB⟩ : Nonempty (Fin n ↪ ι) := by
    classical
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hcard_n

  let cL : Fin m → Fin N := fun j => Fin.castAdd n j
  let cR : Fin n → Fin N := fun j => Fin.natAdd m j
  let L : Matrix ι (Fin m) F[X] := Matrix.submatrix M id cL
  let R : Matrix ι (Fin n) F[X] := Matrix.submatrix M id cR
  let A21 : Matrix (Fin n) (Fin m) F[X] := Matrix.submatrix M rB cL
  let D : Matrix (Fin n) (Fin n) F[X] := Matrix.submatrix M rB cR

  have hD : D = -Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])) := by
    funext i j
    have hj' : ¬ e + 1 + (j : ℕ) ≤ e := by
      omega
    simp [D, M, BW_homMatrix, cR, Matrix.vandermonde, m, hj', Nat.add_sub_cancel_left]

  have hvB : Function.Injective (fun i : Fin n => domain (rB i)) := by
    intro i1 i2 h
    apply rB.injective
    apply domain.injective
    exact h

  have hdetV : IsUnit
      (Matrix.det
        (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])))) := by
    simpa using
      (RS_isUnit_det_vandermonde_C_of_injective (F := F) n (fun i : Fin n => domain (rB i)) hvB)

  have hdetD : IsUnit (Matrix.det D) := by
    have hunitNeg : IsUnit ((-1 : F[X]) ^ Fintype.card (Fin n)) := by
      simpa using (isUnit_neg_one (α := F[X])).pow (Fintype.card (Fin n))
    have hdetD' : Matrix.det D = (-1 : F[X]) ^ Fintype.card (Fin n) *
        Matrix.det (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X]))) := by
      simpa [hD, Matrix.det_neg]
    refine hdetD'.symm ▸ (hunitNeg.mul hdetV)

  letI : Invertible D := Matrix.invertibleOfIsUnitDet D hdetD
  let K0 : Matrix ι (Fin m) F[X] := L - R * (⅟D * A21)

  have hdetK0 : ∀ rA : Fin m → ι, Matrix.det (K0.submatrix rA id) = 0 := by
    intro rA
    let r : Fin N → ι := Fin.append rA rB
    have hdetA : Matrix.det (M.submatrix r id) = 0 := hdetM r
    let eSum : (Fin m ⊕ Fin n) ≃ Fin N := finSumFinEquiv (m := m) (n := n)
    let Ablocks : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) F[X] :=
      (M.submatrix r id).submatrix eSum eSum

    have hdetAblocks : Matrix.det Ablocks = 0 := by
      have hdetEq : Matrix.det Ablocks = Matrix.det (M.submatrix r id) := by
        simpa [Ablocks] using (Matrix.det_submatrix_equiv_self (e := eSum) (M.submatrix r id))
      simpa [hdetEq] using hdetA

    have hAblocks_eq :
        Ablocks = Matrix.fromBlocks (L.submatrix rA id) (R.submatrix rA id) A21 D := by
      funext i j
      cases i <;> cases j <;>
        simp (config := { zeta := true })
          [Ablocks, eSum, L, R, A21, D, r, cL, cR, Matrix.fromBlocks, N, m, n]

    have hmul :
        Matrix.det D *
            Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) =
          0 := by
      have hformula :=
        (Matrix.det_fromBlocks₂₂ (A := L.submatrix rA id) (B := R.submatrix rA id)
          (C := A21) (D := D))
      simpa [hAblocks_eq, hformula, Matrix.mul_assoc] using hdetAblocks

    have hdetSchur :
        Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) = 0 := by
      exact (IsUnit.mul_right_eq_zero (a := Matrix.det D)
        (b := Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21)) hdetD).1 hmul

    simpa [K0, Matrix.submatrix_sub, Matrix.submatrix_mul, Matrix.submatrix_submatrix,
      Matrix.mul_assoc, Function.comp, L, R] using hdetSchur

  have hdegL : ∀ i j, (L i j).natDegree ≤ 1 := by
    intro i j
    simpa [L, cL, M] using
      (BW_homMatrix_entry_natDegree_le_one (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) i (cL j))

  have hdegA21 : ∀ i j, (A21 i j).natDegree ≤ 1 := by
    intro i j
    simpa [A21, cL, M] using
      (BW_homMatrix_entry_natDegree_le_one (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) (rB i) (cL j))

  have hdegR0 : ∀ i j, (R i j).natDegree = 0 := by
    intro i j
    have hj : e + 1 ≤ (cR j).1 := by
      have : e + 1 ≤ (e + 1) + (j : ℕ) := Nat.le_add_right (e + 1) (j : ℕ)
      simpa [cR, m] using this
    simpa [R, cR, M] using
      (BW_homMatrix_entry_natDegree_eq_zero_of_ge (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) i (cR j) hj)

  have hdegInvD0 : ∀ i j : Fin n, (D⁻¹ i j).natDegree = 0 := by
    intro i j
    simpa [hD] using
      (RS_natDegree_inv_neg_vandermonde_C_eq_zero (F := F) n (fun t : Fin n => domain (rB t)) hvB i j)

  have hdegInvDA21 : ∀ i j, ((⅟D * A21) i j).natDegree ≤ 1 := by
    intro i j
    classical
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        ((⅟D i k) * (A21 k j)).natDegree ≤ 1 := by
      intro k hk
      have hInv' : (D⁻¹ i k).natDegree = 0 := hdegInvD0 i k
      calc
        ((⅟D i k) * (A21 k j)).natDegree ≤ (⅟D i k).natDegree + (A21 k j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + (A21 k j).natDegree := by
          simp [Matrix.invOf_eq_nonsing_inv, hInv']
        _ = (A21 k j).natDegree := by simp
        _ ≤ 1 := hdegA21 k j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := 1) (f := fun k : Fin n => (⅟D i k) * (A21 k j)) hterm
    simpa [Matrix.mul_apply] using hsum

  have hdegRInvDA21 : ∀ i j, ((R * (⅟D * A21)) i j).natDegree ≤ 1 := by
    intro i j
    classical
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (R i k * ((⅟D * A21) k j)).natDegree ≤ 1 := by
      intro k hk
      have hR : (R i k).natDegree = 0 := hdegR0 i k
      calc
        (R i k * ((⅟D * A21) k j)).natDegree ≤ (R i k).natDegree + ((⅟D * A21) k j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + ((⅟D * A21) k j).natDegree := by simp [hR]
        _ = ((⅟D * A21) k j).natDegree := by simp
        _ ≤ 1 := hdegInvDA21 k j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := 1) (f := fun k : Fin n => R i k * ((⅟D * A21) k j)) hterm
    simpa [Matrix.mul_apply] using hsum

  have hdegK0 : ∀ i j, (K0 i j).natDegree ≤ 1 := by
    intro i j
    have hsub : (L i j - (R * (⅟D * A21)) i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree :=
      Polynomial.natDegree_sub_le (L i j) ((R * (⅟D * A21)) i j)
    have hmax :
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree ≤ 1 := by
      exact max_le_iff.mpr ⟨hdegL i j, hdegRInvDA21 i j⟩
    have : (K0 i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree := by
      simpa [K0] using hsub
    exact le_trans this hmax

  have hcard_m : m ≤ Fintype.card ι := by
    simpa [m, e, he] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) hdeg hδ)

  obtain ⟨a, ha0, ha_deg, haKer⟩ :=
    RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one (ι := ι) (F := F) e K0
      (by simpa [m] using hcard_m) hdegK0 (by
        intro rA
        simpa [m, K0] using hdetK0 rA)

  let b : Fin n → F[X] := -(⅟D).mulVec (A21.mulVec a)

  refine ⟨a, b, ?_, ha_deg, ?_, ?_⟩

  · intro happ
    apply ha0
    funext t
    have := congrArg (fun f : Fin N → F[X] => f (Fin.castAdd n t)) happ
    simpa [Fin.append_left, m, n, N, b] using this

  · intro s
    classical

    have hdegA21mulVec : ∀ i : Fin n, ((A21.mulVec a) i).natDegree ≤ e + 1 := by
      intro i
      have hterm : ∀ t ∈ (Finset.univ : Finset (Fin m)),
          (A21 i t * a t).natDegree ≤ e + 1 := by
        intro t ht
        have hA : (A21 i t).natDegree ≤ 1 := hdegA21 i t
        have ha : (a t).natDegree ≤ e := ha_deg t
        have hmul : (A21 i t * a t).natDegree ≤ (A21 i t).natDegree + (a t).natDegree :=
          Polynomial.natDegree_mul_le
        have hadd : (A21 i t).natDegree + (a t).natDegree ≤ 1 + e := Nat.add_le_add hA ha
        have : (A21 i t * a t).natDegree ≤ 1 + e := le_trans hmul hadd
        simpa [Nat.add_comm] using this
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin m)))
          (n := e + 1) (f := fun t : Fin m => A21 i t * a t) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum

    have hdegInvDmulVec : ∀ i : Fin n, ((⅟D).mulVec (A21.mulVec a) i).natDegree ≤ e + 1 := by
      intro i
      have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          ((⅟D i k) * (A21.mulVec a k)).natDegree ≤ e + 1 := by
        intro k hk
        have hInv' : (D⁻¹ i k).natDegree = 0 := hdegInvD0 i k
        have hA : ((A21.mulVec a) k).natDegree ≤ e + 1 := hdegA21mulVec k
        calc
          ((⅟D i k) * (A21.mulVec a k)).natDegree ≤ (⅟D i k).natDegree + (A21.mulVec a k).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + (A21.mulVec a k).natDegree := by
            simp [Matrix.invOf_eq_nonsing_inv, hInv']
          _ = (A21.mulVec a k).natDegree := by simp
          _ ≤ e + 1 := hA
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
          (n := e + 1) (f := fun k : Fin n => (⅟D i k) * (A21.mulVec a k)) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum

    simpa [b] using hdegInvDmulVec s

  · -- kernel equation
    have hRb : Matrix.mulVec R b = -Matrix.mulVec (R * (⅟D * A21)) a := by
      ext i
      simp [b, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc]

    have hLR : Matrix.mulVec L a + Matrix.mulVec R b = 0 := by
      have haKer' : Matrix.mulVec (L - R * (⅟D * A21)) a = 0 := by
        simpa [K0] using haKer
      have haKer'' : Matrix.mulVec L a - Matrix.mulVec (R * (⅟D * A21)) a = 0 := by
        simpa [Matrix.sub_mulVec] using haKer'
      simpa [sub_eq_add_neg, hRb] using haKer''

    have hsplit : Matrix.mulVec M (Fin.append a b) = Matrix.mulVec L a + Matrix.mulVec R b := by
      simpa [L, R, cL, cR, N] using
        (RS_mulVec_append_castAdd_natAdd (ι := ι) (R := F[X]) m n M a b)

    -- rewrite the goal matrix to `M` using commutativity in `F[X]`
    have hmulX : (fun i : ι => (Polynomial.C (u 0 i) : F[X]) + Polynomial.C (u 1 i) * Polynomial.X) =
        fun i : ι => (Polynomial.C (u 0 i) : F[X]) + Polynomial.X * Polynomial.C (u 1 i) := by
      funext i
      -- commute the factors in the second summand
      simpa using
        congrArg (fun t : F[X] => (Polynomial.C (u 0 i) : F[X]) + t)
          (mul_comm (Polynomial.C (u 1 i) : F[X]) Polynomial.X)

    have hMgoal :
        BW_homMatrix (ι := ι) e deg (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => (Polynomial.C (u 0 i) : F[X]) + Polynomial.C (u 1 i) * Polynomial.X) =
          M := by
      -- unfold `M` and rewrite the polynomial argument
      simpa [M, hmulX]

    rw [hMgoal]
    rw [hsplit]
    exact hLR


open scoped BigOperators in
open Polynomial in
open BerlekampWelch in
theorem RS_exists_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F[X],
      ∃ b : Fin (e + deg) → F[X],
        a ≠ 0 ∧
          (∀ t, (a t).natDegree ≤ e) ∧
            (∀ s, (b s).natDegree ≤ e + 1) ∧
              Matrix.mulVec
                  (BW_homMatrix (ι := ι) e deg
                    (fun i => (Polynomial.C (domain i) : F[X]))
                    (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
                  (Fin.append a b) = 0 := by
  classical
  -- unfold the outer `let e := ...` in the goal
  dsimp

  -- obtain a nonzero kernel vector from the stronger existence lemma
  have h :=
    RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt
      (deg := deg) (domain := domain) (δ := δ) (u := u) hdeg hδ hS
  -- unfold the `let e := ...` in the hypothesis
  dsimp at h

  rcases h with ⟨a, b, happend, ha_deg, hb_deg, hMul⟩

  have hdeg' : Nat.floor (δ * Fintype.card ι) + deg ≤ Fintype.card ι :=
    RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR
      (deg := deg) (domain := domain) (δ := δ) (hdeg := hdeg) (hδ := hδ)

  have ha0 : a ≠ 0 :=
    RS_a_ne_zero_of_BW_homMatrix_mulVec_eq_zero
      (deg := deg) (domain := domain) (e := Nat.floor (δ * Fintype.card ι))
      (u := u) (a := a) (b := b) hdeg' happend hMul

  refine ⟨a, b, ha0, ha_deg, hb_deg, hMul⟩


open scoped BigOperators in
open scoped Polynomial.Bivariate in
open Polynomial in
open Polynomial.Bivariate in
open BerlekampWelch in
theorem RS_exists_bivariate_AB_of_goodCoeffs_card_gt {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (u : WordStack F (Fin 2) ι)
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    ∃ A B : F[X][Y],
      A ≠ 0 ∧
      Polynomial.Bivariate.degreeX A ≤ Nat.floor (δ * Fintype.card ι) ∧
      Polynomial.Bivariate.natDegreeY A ≤ Nat.floor (δ * Fintype.card ι) ∧
      Polynomial.Bivariate.degreeX B ≤ Nat.floor (δ * Fintype.card ι) + deg - 1 ∧
      Polynomial.Bivariate.natDegreeY B ≤ Nat.floor (δ * Fintype.card ι) + 1 ∧
      (∀ i : ι,
        Polynomial.Bivariate.evalX (domain i) B =
          (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalX (domain i) A) := by
  classical
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hker :
      ∃ a : Fin (e + 1) → F[X],
        ∃ b : Fin (e + deg) → F[X],
          a ≠ 0 ∧
            (∀ t, (a t).natDegree ≤ e) ∧
              (∀ s, (b s).natDegree ≤ e + 1) ∧
                Matrix.mulVec
                    (BW_homMatrix (ι := ι) e deg
                      (fun i => (Polynomial.C (domain i) : F[X]))
                      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
                    (Fin.append a b) = 0 := by
    simpa [e] using
      (RS_exists_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt (deg := deg) (domain := domain)
        (δ := δ) u hdeg hδ hS)
  rcases hker with ⟨a, b, ha_ne, ha_deg, hb_deg, hMul⟩
  let A0 : F[X][Y] := ∑ t : Fin (e + 1), Polynomial.monomial t.1 (a t)
  let B0 : F[X][Y] := ∑ s : Fin (e + deg), Polynomial.monomial s.1 (b s)
  let A : F[X][Y] := (Polynomial.Bivariate.swap (R := F)) A0
  let B : F[X][Y] := (Polynomial.Bivariate.swap (R := F)) B0

  have hcoeffA0 : ∀ n : ℕ, ∀ hn : n < e + 1, A0.coeff n = a ⟨n, hn⟩ := by
    intro n hn
    classical
    simp [A0, Polynomial.coeff_monomial]
    have hsum : (∑ t : Fin (e + 1), (if t = ⟨n, hn⟩ then a t else (0 : F[X]))) = a ⟨n, hn⟩ := by
      simpa using (Fintype.sum_ite_eq ⟨n, hn⟩ (fun t : Fin (e + 1) => a t))
    simpa [Fin.ext_iff] using hsum

  have hcoeffB0 : ∀ n : ℕ, ∀ hn : n < e + deg, B0.coeff n = b ⟨n, hn⟩ := by
    intro n hn
    classical
    simp [B0, Polynomial.coeff_monomial]
    have hsum : (∑ t : Fin (e + deg), (if t = ⟨n, hn⟩ then b t else (0 : F[X]))) = b ⟨n, hn⟩ := by
      simpa using (Fintype.sum_ite_eq ⟨n, hn⟩ (fun t : Fin (e + deg) => b t))
    simpa [Fin.ext_iff] using hsum

  have hcoeffA0_big : ∀ N : ℕ, e < N → A0.coeff N = 0 := by
    intro N hN
    classical
    have hN' : e + 1 ≤ N := Nat.succ_le_of_lt hN
    have hne : ∀ t : Fin (e + 1), (t : ℕ) ≠ N := by
      intro t
      have ht : (t : ℕ) < N := lt_of_lt_of_le t.2 hN'
      exact Nat.ne_of_lt ht
    simp [A0, Polynomial.coeff_monomial, hne]

  have hcoeffB0_big : ∀ N : ℕ, e + deg - 1 < N → B0.coeff N = 0 := by
    intro N hN
    classical
    have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
    have hpos : 1 ≤ e + deg := Nat.succ_le_of_lt (Nat.add_pos_right e hdegpos)
    have hN' : e + deg ≤ N := by
      have : (e + deg - 1) + 1 ≤ N := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hN
      simpa [Nat.sub_add_cancel hpos, Nat.add_assoc] using this
    have hne : ∀ t : Fin (e + deg), (t : ℕ) ≠ N := by
      intro t
      have ht : (t : ℕ) < N := lt_of_lt_of_le t.2 hN'
      exact Nat.ne_of_lt ht
    simp [B0, Polynomial.coeff_monomial, hne]

  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A ≠ 0
    have hex : ∃ t : Fin (e + 1), a t ≠ 0 := by
      by_contra h
      apply ha_ne
      funext t
      have : a t = 0 := by
        by_contra ht
        exact h ⟨t, ht⟩
      simpa using this
    rcases hex with ⟨t0, ht0⟩
    have hcoeff : A0.coeff t0.1 = a t0 := by
      simpa using (hcoeffA0 t0.1 t0.2)
    have hA0 : A0 ≠ 0 := by
      intro hzero
      apply ht0
      have : A0.coeff t0.1 = 0 := by simpa [hzero]
      simpa [hcoeff] using this
    intro hzero
    apply hA0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simpa [A, hzero])
  · -- degreeX A bound
    have hnatY_A0 : Polynomial.Bivariate.natDegreeY A0 ≤ e := by
      unfold Polynomial.Bivariate.natDegreeY
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero).2 hcoeffA0_big
    have hdegX : Polynomial.Bivariate.degreeX A = Polynomial.Bivariate.natDegreeY A0 := by
      simpa [A] using (ps_degree_x_swap (F := F) (f := A0))
    simpa [hdegX] using hnatY_A0
  · -- natDegreeY A bound
    have hdegX_A0 : Polynomial.Bivariate.degreeX A0 ≤ e := by
      classical
      unfold Polynomial.Bivariate.degreeX
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      by_cases hnlt : n < e + 1
      · have : (A0.coeff n).natDegree = (a ⟨n, hnlt⟩).natDegree := by
          simpa [hcoeffA0 n hnlt]
        simpa [this] using ha_deg ⟨n, hnlt⟩
      · have hnle : e < n := by
          have : e + 1 ≤ n := Nat.le_of_not_gt hnlt
          exact lt_of_lt_of_le (Nat.lt_succ_self e) this
        have hcoeff0 : A0.coeff n = 0 := hcoeffA0_big n hnle
        have : A0.coeff n ≠ 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        exact (this hcoeff0).elim
    have hnatY : Polynomial.Bivariate.natDegreeY A = Polynomial.Bivariate.degreeX A0 := by
      simpa [A] using (ps_nat_degree_y_swap (F := F) (f := A0))
    simpa [hnatY] using hdegX_A0
  · -- degreeX B bound
    have hnatY_B0 : Polynomial.Bivariate.natDegreeY B0 ≤ e + deg - 1 := by
      unfold Polynomial.Bivariate.natDegreeY
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero).2 hcoeffB0_big
    have hdegX : Polynomial.Bivariate.degreeX B = Polynomial.Bivariate.natDegreeY B0 := by
      simpa [B] using (ps_degree_x_swap (F := F) (f := B0))
    simpa [hdegX] using hnatY_B0
  · -- natDegreeY B bound
    have hdegX_B0 : Polynomial.Bivariate.degreeX B0 ≤ e + 1 := by
      classical
      unfold Polynomial.Bivariate.degreeX
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      by_cases hnlt : n < e + deg
      · have : (B0.coeff n).natDegree = (b ⟨n, hnlt⟩).natDegree := by
          simpa [hcoeffB0 n hnlt]
        simpa [this] using hb_deg ⟨n, hnlt⟩
      · have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
        have hpos : 0 < e + deg := Nat.add_pos_right e hdegpos
        have hnge : e + deg ≤ n := (Nat.not_lt).1 hnlt
        have hnle : e + deg - 1 < n := Nat.sub_one_lt_of_le hpos hnge
        have hcoeff0 : B0.coeff n = 0 := hcoeffB0_big n hnle
        have : B0.coeff n ≠ 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        exact (this hcoeff0).elim
    have hnatY : Polynomial.Bivariate.natDegreeY B = Polynomial.Bivariate.degreeX B0 := by
      simpa [B] using (ps_nat_degree_y_swap (F := F) (f := B0))
    simpa [hnatY] using hdegX_B0
  · -- main identity
    intro i
    have hEvalX_A : Polynomial.Bivariate.evalX (domain i) A = Polynomial.Bivariate.evalY (domain i) A0 := by
      simpa [A] using (ps_eval_y_eq_eval_x_swap (F := F) (y := domain i) (f := A0)).symm
    have hEvalX_B : Polynomial.Bivariate.evalX (domain i) B = Polynomial.Bivariate.evalY (domain i) B0 := by
      simpa [B] using (ps_eval_y_eq_eval_x_swap (F := F) (y := domain i) (f := B0)).symm
    rw [hEvalX_B, hEvalX_A]

    have hEq_all :
        ∀ i : ι,
          (∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1) *
              (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
            = ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 :=
      (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (R := F[X]) e deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
          a b).1 hMul

    have hEvalA :
        Polynomial.Bivariate.evalY (domain i) A0 =
          ∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1 := by
      classical
      simp [Polynomial.Bivariate.evalY, A0, Polynomial.eval_finset_sum]

    have hEvalB :
        Polynomial.Bivariate.evalY (domain i) B0 =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 := by
      classical
      simp [Polynomial.Bivariate.evalY, B0, Polynomial.eval_finset_sum]

    have hEq_eval :
        Polynomial.Bivariate.evalY (domain i) A0 *
            (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
          = Polynomial.Bivariate.evalY (domain i) B0 := by
      simpa [hEvalA, hEvalB] using (hEq_all i)

    calc
      Polynomial.Bivariate.evalY (domain i) B0
          = Polynomial.Bivariate.evalY (domain i) A0 *
              (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) := by
              simpa using hEq_eval.symm
      _ = (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalY (domain i) A0 := by
            -- commutativity in `F[X]`
            exact (mul_comm (Polynomial.Bivariate.evalY (domain i) A0)
              (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))


open scoped BigOperators in
open scoped Polynomial.Bivariate in
open Polynomial in
open Polynomial.Bivariate in
open BerlekampWelch in
theorem RS_jointAgreement_of_goodCoeffs_card_gt {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (u : WordStack F (Fin 2) ι)
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  sorry


theorem errorBound_eq_n_div_q_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    errorBound δ deg domain = Fintype.card ι / Fintype.card F := by
  classical
  let C : LinearCode ι F := ReedSolomon.code domain deg
  let n : ℕ := Fintype.card ι
  let kdim : ℕ := Module.finrank F C
  let d : ℕ := Code.dist (C : Set (ι → F))
  have hk : kdim ≤ n := by
    have hk' : Module.finrank F C ≤ Module.finrank F (ι → F) :=
      Submodule.finrank_le (R := F) (M := (ι → F)) C
    simpa [n, kdim, Module.finrank_pi] using hk'
  have hSB : kdim ≤ n - d + 1 := by
    simpa [n, d, kdim] using (LinearCode.singleton_bound_linear (LC := C))
  have hdle : d ≤ n := by
    simpa [d, n] using (Code.dist_le_card (C := (C : Set (ι → F))))
  have hdistNat : d - 1 ≤ n - kdim := by
    omega

  have hrel :
      relativeUniqueDecodingRadius (ι := ι) (F := F) (C := C) ≤
        ((1 - (↑(LinearCode.rate C) : ℝ≥0)) / 2) := by
    -- rewrite in terms of `d`, `kdim`, `n`
    have hUDR :
        relativeUniqueDecodingRadius (ι := ι) (F := F) (C := C) =
          (((d : ℝ≥0) - 1) / 2) / (n : ℝ≥0) := by
      simp [Code.relativeUniqueDecodingRadius, d, n]
    have hrate : (↑(LinearCode.rate C) : ℝ≥0) = (kdim : ℝ≥0) / (n : ℝ≥0) := by
      simp [LinearCode.rate, LinearCode.dim, LinearCode.length, kdim, n]

    -- cast the singleton-bound inequality into NNReal
    have hdistNN : ((d : ℝ≥0) - 1) ≤ (n - kdim : ℝ≥0) := by
      have hcast : (d - 1 : ℝ≥0) ≤ (n - kdim : ℝ≥0) := by
        exact_mod_cast hdistNat
      simpa [Nat.cast_tsub, Nat.cast_one] using hcast

    have hn0 : (n : ℝ≥0) ≠ 0 := by
      -- `n = card ι` and `ι` is nonempty
      apply Nat.cast_ne_zero.mpr
      simpa [n] using (Fintype.card_ne_zero (α := ι))

    -- rewrite RHS to match the normalization by `n`
    have hR :
        ((1 : ℝ≥0) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2 =
          ((n - kdim : ℝ≥0) / 2) / (n : ℝ≥0) := by
      -- `((n - k)/n)/2` equals `((n-k)/2)/n`
      -- and `((n-k)/n) = 1 - k/n` since `n/n = 1`
      calc
        ((1 : ℝ≥0) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2
            = (((n : ℝ≥0) / (n : ℝ≥0)) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2 := by
                -- rewrite `1` as `n/n`
                rw [← div_self hn0]
        _ = (((n : ℝ≥0) - (kdim : ℝ≥0)) / (n : ℝ≥0)) / 2 := by
              -- combine the two fractions
              rw [← NNReal.sub_div (a := (n : ℝ≥0)) (b := (kdim : ℝ≥0)) (c := (n : ℝ≥0))]
        _ = ((n - kdim : ℝ≥0) / (n : ℝ≥0)) / 2 := by
              -- rewrite `n - kdim` as a casted nat subtraction
              simp [Nat.cast_tsub, Nat.cast_one]
        _ = ((n - kdim : ℝ≥0) / 2) / (n : ℝ≥0) := by
              -- swap the order of divisions
              -- (a / n) / 2 = (a / 2) / n because multiplication is commutative
              simp [div_div, mul_comm, mul_left_comm, mul_assoc]

    -- finish
    -- goal becomes a monotonicity statement after rewriting
    rw [hUDR, hrate, hR]
    -- `gcongr` uses monotonicity of `/` and `(*)` on `ℝ≥0`
    gcongr

  have hmem : δ ∈ Set.Icc 0 ((1 - (↑(LinearCode.rate C) : ℝ≥0)) / 2) := by
    refine ⟨by simp, le_trans hδ hrel⟩

  -- now simplify errorBound
  simp [errorBound, C, hmem]


theorem RS_correlatedAgreement_affineLines_uniqueDecodingRegime {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    : δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementAffineLines
  intro u hprob
  have hprob' :
      Pr_{let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ]
        > (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    simpa [errorBound_eq_n_div_q_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hδ] using hprob
  have hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι :=
    card_RS_goodCoeffs_gt_of_prob_gt_n_div_q (deg := deg) (domain := domain) (δ := δ) u hprob'
  exact RS_jointAgreement_of_goodCoeffs_card_gt (deg := deg) (domain := domain) (δ := δ) hδ u hS

/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and two words `u₀` and `u₁`, such that the probability that a random affine
line passing through `u₀` and `u₁` is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u₀` and `u₁` have correlated agreement. -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  -- Do casing analysis on `hδ`
  if hδ_uniqueDecodingRegime :
    δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)
  then
    RS_correlatedAgreement_affineLines_uniqueDecodingRegime (hδ := hδ_uniqueDecodingRegime)
  else
    -- TODO: theorem 5.1 for list-decoding regime
    sorry


/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the  probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by sorry

open Affine in
/-- Theorem 1.6 (Correlated agreement over affine spaces) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space with origin `u₀` and affine generting set `u₁, ..., uκ`
such that the probability a random point in the affine space is `δ`-close to the Reed-Solomon
code is at most `ε`. Then the words `u₀, ..., uκ` have correlated agreement.

Note that we have `k+2` vectors to form the affine space. This an intricacy needed us to be
able to isolate the affine origin from the affine span and to form a generating set of the
correct size. The reason for taking an extra vector is that after isolating the affine origin,
the affine span is formed as the span of the difference of the rest of the vector set. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin (k + 1) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  : δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by sorry

end CoreResults

section BCIKS20ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan
open Polynomial.Bivariate
open RatFunc

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√rhon.
-/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

open Classical in
noncomputable def proximity_gap_degree_bound (rho : ℚ) (m n : ℕ) : ℕ :=
  let b := D_X rho m n
  if h : ∃ n : ℕ, b = n
  then h.choose - 1
  else Nat.floor b

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(rho, m) = 1 - √rho - √rho/2m.
-/
noncomputable def proximity_gap_johnson (rho : ℚ) (m : ℕ) : ℝ :=
  (1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m)


/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hm : 1 ≤ m) :
  ∃ Q, Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs f Q :=
  GuruswamiSudan.proximity_gap_existence (k + 1) n ωs f hm

open Polynomial in
/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, rho] such that δᵣ(w, P) ≤ δ₀(rho, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. Note that in F[X][Y], the term X actually refers to
    the outer variable, Y.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {w : Fin n → F}
  {Q : F[X][Y]}
  (hk : k + 2 ≤ n) (hm : 1 ≤ m)
  (cond : Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs w Q)
  {p : ReedSolomon.code ωs (k + 1)}
  (h : (↑Δ₀(w, fun i ↦ Polynomial.eval (ωs i) (ReedSolomon.codewordToPoly p)) : ℝ) / ↑n <
       _root_.proximity_gap_johnson (k + 1) n m)
  :
  (Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q :=
  GuruswamiSudan.proximity_gap_divisibility hk hm p cond h


section

open Polynomial
open Polynomial.Bivariate

/-- Following [BCIKS20] this the Y-degree of
    a trivariate polynomial `Q`.
-/
def D_Y (Q : F[Z][X][Y]) : ℕ := Bivariate.natDegreeY Q

/-- The YZ-degree of a trivariate polynomial.
-/
def D_YZ (Q : F[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
            (
              fun j =>
                Option.getD (
                  Finset.max (
                    Finset.image
                      (fun k => j + (Bivariate.coeff Q j k).natDegree)
                      (Q.coeff j).support
                  )
                ) 0
            )
            Q.support
    )

end

/-- The Guruswami-Sudan condition as it is stated in
    [BCIKS20].
-/
structure ModifiedGuruswami
  (m n k : ℕ)
  (ωs : Fin n ↪ F)
  (Q : F[Z][X][Y])
  (u₀ u₁ : Fin n → F)
  where
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : natWeightedDegree Q 1 k < D_X ((k + 1) / (n : ℚ)) n m
  /-- Multiplicity of the roots is at least `m`. -/
  Q_multiplicity : ∀ i, rootMultiplicity Q
              (Polynomial.C <| ωs i)
              ((Polynomial.C <| u₀ i) + Polynomial.X * (Polynomial.C <| u₁ i))
            ≥ m
  /-- The X-degree bound. -/
  Q_deg_X :
    degreeX Q < D_X ((k + 1) / (n : ℚ)) n m
  /-- The Y-degree bound. -/
  Q_D_Y :
    D_Y Q < D_X (k + 1 / (n : ℚ)) n m / k
  /-- The YZ-degree bound. -/
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

/-- The claim 5.4 from [BCIKS20].
    It essentially claims that there exists
    a soultion to the Guruswami-Sudan constraints above.
-/
lemma modified_guruswami_has_a_solution
  {m n k : ℕ}
  {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
  :
  ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁
    := by sorry

end

variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

noncomputable instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s := Fintype.ofFinite _

/-- The set `S` (equation 5.2 of [BCIKS20]). -/
noncomputable def coeffs_of_close_proximity (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
  : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
/-- There exists a `δ`-close polynomial `P_z` for each `z`
    from the set `S`.
-/
lemma exists_Pz_of_coeffs_of_close_proximity
  {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁)
  :
  ∃ Pz : F[X], Pz.natDegree ≤ k ∧ δᵣ(u₀ + z • u₁, Pz.eval ∘ ωs) ≤ δ := by
    unfold coeffs_of_close_proximity at hS
    obtain ⟨w, hS, dist⟩ : ∃ a ∈ ReedSolomon.code ωs (k + 1), ↑δᵣ(u₀ + z • u₁, a) ≤ δ := by
      simpa using hS
    obtain ⟨p, hS⟩ : ∃ y ∈ degreeLT F (k + 1), (ReedSolomon.evalOnPoints ωs) y = w := by
      simpa using hS
    exact ⟨p, ⟨
      by if h : p = 0
         then simp [h]
         else rw [mem_degreeLT, degree_eq_natDegree h, Nat.cast_lt] at hS; grind,
      by convert dist; rw [←hS.2]; rfl
    ⟩⟩

/-- The `δ`-close polynomial `Pz` for each `z`
    from the set `S` (`coeffs_of_close_proximity`).
-/
noncomputable def Pz
  {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
  :
  F[X]
  := (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose

/-- Proposition 5.5 from [BCIKS20].
    There exists a subset `S'` of the set `S` and
    a bivariate polynomial `P(X, Z)` that matches
    `Pz` on that set.
-/
lemma exists_a_set_and_a_matching_polynomial
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ S', ∃ (h_sub : S' ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁), ∃ P : F[Z][X],
    #S' > #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (2 * D_Y Q) ∧
    ∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1) ∧
    P.natDegree ≤ k ∧
    Bivariate.degreeX P ≤ 1 := by sorry

/-- The subset `S'` extracted from the proprosition 5.5.
-/
noncomputable def matching_set
  (ωs : Fin n ↪ F)
  (δ : ℚ)
  (u₀ u₁ : Fin n → F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : Finset F := (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose

/-- `S'` is indeed a subset of `S` -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : matching_set k ωs δ u₀ u₁ h_gs ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁ :=
  (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose_spec.choose

/-- The equation 5.12 from [BCIKS20]. -/
lemma irreducible_factorization_of_gs_solution
  {k : ℕ}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (C : F[Z][X]) (R : List F[Z][X][Y]) (f : List ℕ) (e : List ℕ),
    R.length = f.length ∧
    f.length = e.length ∧
    ∀ eᵢ ∈ e, 1 ≤ eᵢ ∧
    ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
    ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
    Q = (Polynomial.C C) *
        ∏ (Rᵢ ∈ R.toFinset) (fᵢ ∈ f.toFinset) (eᵢ ∈ e.toFinset),
          (Rᵢ.comp ((Y : F[Z][X][Y]) ^ fᵢ))^eᵢ
  := sorry

/-- Claim 5.6 of [BCIKS20]. -/
lemma discr_of_irred_components_nonzero
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∃ x₀,
      ∀ R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose,
      Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

open Trivariate in
open Bivariate in
/-- Claim 5.7 of [BCIKS20]. -/
lemma exists_factors_with_large_common_root_set
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0} sorry)
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- Claim 5.7 establishes existens of a polynomial `R`.
    This is the extraction of this polynomial.
-/
noncomputable def R
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X][Y] := (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose

/-- Claim 5.7 establishes existens of a polynomial `H`.
    This is the extraction of this polynomial.
-/
noncomputable def H
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X] := (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose

/-- An important property of the polynomial
    `H` extracted from claim 5.7 is that it is
    irreducible.
-/
lemma irreducible_H
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  Irreducible (H k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.1

open BCIKS20AppendixA.ClaimA2 in
/-- The claim 5.8 from [BCIKS20].
    States that the approximate solution is
    actually a solution.
    This version of the claim is stated in terms
    of coefficients.
-/
lemma approximate_solution_is_exact_solution_coeffs
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∀ t ≥ k,
  α'
    x₀
    (R k δ x₀ h_gs)
    (irreducible_H k h_gs)
    t
  =
  (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
  := by sorry

open BCIKS20AppendixA.ClaimA2 in
/-- The claim 5.8 from [BCIKS20].
    States that the approximate solution is
    actually a solution.
    This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs))) := by
   sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.9 from [BCIKS20].
    States that the solution `γ` is linear in
    the variable `Z`.
-/
lemma solution_gamma_is_linear_in_Z
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear represenation of the solution `γ`
    extracted from the claim 5.9.
-/
noncomputable def P
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  F[Z][X] :=
  let v₀ := Classical.choose (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  let v₁ := Classical.choose
    (Classical.choose_spec <| solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open BCIKS20AppendixA.ClaimA2 in
/-- The extracted `P` from claim 5.9 equals `γ`.
-/
lemma gamma_eq_P
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
  BCIKS20AppendixA.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs) :=
  Classical.choose_spec
    (Classical.choose_spec (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs))

/-- The set `S'_x` from [BCIKS20] (just before claim 5.10).
    The set of all `z∈S'` such that `w(x,z)` matches `P_z(x)`.
-/
noncomputable def matching_set_at_x
  (δ : ℚ)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (x : Fin n)
  : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs,
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h)).eval (ωs x)} sorry

/-- Claim 5.10 of [BCIKS20].
    Needed to prove the claim 5.9.
    This claim states that `γ(x)=w(x,Z)` if
    the cardinality |S'_x| is big enough.
-/
lemma solution_gamma_matches_word_if_subset_large
  {ωs : Fin n ↪ F}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {x : Fin n}
  {D : ℕ}
  (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
  (hx : (matching_set_at_x k δ h_gs x).card >
    (2 * k + 1)
      * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
      * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
      * D)
  : (P k δ x₀ h_gs).eval (Polynomial.C (ωs x)) =
    (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X
  := by sorry

/-- Claim 5.11 from [BCIKS20].
    There exists a set of points `{x₀,...,x_{k+1}}`
    such that the sets S_{x_j} satisfy the condition
    in the claim 5.10.
-/
lemma exists_points_with_large_matching_subset
  {ωs : Fin n ↪ F}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {x : Fin n}
  {D : ℕ}
  (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
  :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by sorry

end BCIKS20ProximityGapSection5

section BCIKS20ProximityGapSection6
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ} [NeZero n]

/-- An affine curve parameterized by the field
    and whose defining vectors are the vectors
    `u 0, ..., u (n - 1)`.
-/
def curve {l : ℕ} (u : Fin l → Fin n → F) (z : F) : Fin n → F :=
    ∑ i, z ^ i.1 • u i

/-- The parameters for which the curve points are
    `δ`-close to a set `V` (typically, a linear code).
    The set `S` from the proximity gap paper.
-/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
  (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(curve u z, V) ≤ δ} := by infer_instance
  @Set.toFinset _ { z | δᵣ(curve u z, V) ≤ δ} this

/-- If the set of points `δ`-close to the code `V` has
    at least `n * l + 1` points then
    there exists a curve defined by vectors `v` from `V`
    such that the points of `curve u` and `curve v`
    are `δ`-close with the same parameters.
    Moreover, `u` and `v` differ at at most `δ * n`
    positions.
-/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ}
  {rho : ℚ≥0}
  {δ : ℚ≥0}
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ (1 - rho) / 2)
  {u : Fin l → Fin n → F}
  (hS : n * l < (coeffs_of_close_proximity_curve δ u V).card)
  :
  coeffs_of_close_proximity_curve δ u V = F ∧
  ∃ (v : Fin l → Fin n → F),
    ∀ z, δᵣ(curve u z, curve v z) ≤ δ ∧
    ({ x : Fin n | Finset.image u ≠ Finset.image v } : Finset _).card ≤ δ * n := by
  sorry

/-- The distance bound from the proximity gap paper.
-/
noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- If the set of points on the curve defined by `u`
    close to `V` has at least
    `((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ)))
    * n ^ 2 * l + 1` points then
    there exist vectors `v` from `V` that
    `(1 - δ) * n` close to vectors `u`.
-/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l : ℕ}
  [Finite F]
  {m : ℕ}
  {rho : ℚ≥0}
  {δ : ℚ≥0}
  (hm : 3 ≤ m)
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ δ₀ rho m)
  {u : Fin l → Fin n → F}
  (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ)))
    * n ^ 2 * l < (coeffs_of_close_proximity_curve δ u V).card)
  :
  ∃ (v : Fin l → Fin n → F),
  ∀ i, v i ∈ V ∧
  (1 - δ) * n ≤ ({x : Fin n | ∀ i, u i x = v i x} : Finset _).card := sorry

section
open NNReal Finset Function

open scoped BigOperators
open scoped ReedSolomonCode

variable {l : ℕ} [NeZero l]
         {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]


theorem exists_of_weighted_avg_gt {α : Type} (p : PMF α) (f : α → ENNReal) (ε : ENNReal) :
  (∑' a, p a * f a) > ε → ∃ a, f a > ε := by
  intro hgt
  by_contra hno
  have hle : ∀ a, f a ≤ ε := by
    intro a
    have : ¬ f a > ε := by
      intro ha
      exact hno ⟨a, ha⟩
    exact le_of_not_gt this
  have hmul : ∀ a, p a * f a ≤ p a * ε := by
    intro a
    exact mul_le_mul_of_nonneg_left (hle a) (by simpa using (zero_le (p a)))
  have htsum : (∑' a, p a * f a) ≤ ∑' a, p a * ε := by
    exact ENNReal.tsum_le_tsum hmul
  have htsum' : (∑' a, p a * f a) ≤ ε := by
    refine le_trans htsum ?_
    simpa [ENNReal.tsum_mul_right, p.tsum_coe] using (le_rfl : (∑' a, p a * ε) ≤ (∑' a, p a * ε))
  exact (not_lt_of_ge htsum') hgt

theorem jointAgreement_implies_second_proximity {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [DecidableEq F]
    {C : Set (ι → F)} {δ : ℝ≥0} {W : Fin 2 → ι → F} :
    jointAgreement (C := C) (δ := δ) (W := W) → δᵣ(W 1, C) ≤ δ := by
  intro h
  rcases h with ⟨S, hS_card, v, hv⟩
  have hv1 : v 1 ∈ C := (hv 1).1
  have hSsub : S ⊆ Finset.filter (fun j => v 1 j = W 1 j) Finset.univ := (hv 1).2
  have hdist : δᵣ(W 1, v 1) ≤ δ := by
    rw [Code.relCloseToWord_iff_exists_agreementCols (u := W 1) (v := v 1) (δ := δ)]
    refine ⟨S, ?_, ?_⟩
    · have hS' : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
        simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using hS_card
      exact (Code.relDist_floor_bound_iff_complement_bound (n := Fintype.card ι)
        (upperBound := S.card) (δ := δ)).2 hS'
    · intro j
      constructor
      · intro hj
        have hj' : j ∈ Finset.filter (fun j => v 1 j = W 1 j) Finset.univ := hSsub hj
        have : v 1 j = W 1 j := by
          simpa [Finset.mem_filter] using hj'
        exact this.symm
      · intro hj_ne
        intro hj
        have hj' : j ∈ Finset.filter (fun j => v 1 j = W 1 j) Finset.univ := hSsub hj
        have : v 1 j = W 1 j := by
          simpa [Finset.mem_filter] using hj'
        exact hj_ne this.symm
  have hclose : ∃ v' ∈ C, δᵣ(W 1, v') ≤ δ := by
    exact ⟨v 1, hv1, hdist⟩
  exact (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (u := W 1) (C := C) (δ := δ)).2 hclose

theorem prob_uniform_congr_equiv {α : Type} [Fintype α] [Nonempty α]
  (e : α ≃ α) (P : α → Prop) [DecidablePred P] :
  Pr_{let x ←$ᵖ α}[P (e x)] = Pr_{let x ←$ᵖ α}[P x] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card (F := α) (P := fun x => P (e x))]
  rw [prob_uniform_eq_card_filter_div_card (F := α) (P := P)]
  have hcard : (Finset.filter (fun x : α => P (e x)) Finset.univ).card =
      (Finset.filter (fun x : α => P x) Finset.univ).card := by
    classical
    refine Finset.card_bij (s := Finset.filter (fun x : α => P (e x)) Finset.univ)
      (t := Finset.filter (fun x : α => P x) Finset.univ)
      (i := fun a ha => e a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp [Finset.mem_filter, ha]
    · intro a1 ha1 a2 ha2 h
      exact e.injective h
    · intro b hb
      refine ⟨e.symm b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        simpa [Finset.mem_filter, hb]
      · simp
  simp [hcard]

theorem prob_uniform_shift_invariant {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {U : Finset (ι → F)} [Nonempty U]
  (dir : ι → F)
  (hshift : ∀ a ∈ (U : Finset (ι → F)), ∀ z : F, a + z • dir ∈ (U : Finset (ι → F)))
  {V : Set (ι → F)} {δ : ℝ≥0} :
  ∀ z : F,
    Pr_{let a ←$ᵖ U}[δᵣ((a.1 + z • dir), V) ≤ δ] = Pr_{let a ←$ᵖ U}[δᵣ(a.1, V) ≤ δ] := by
  intro z
  classical
  let shiftEquiv : (U : Type) ≃ (U : Type) :=
    { toFun := fun a => ⟨a.1 + z • dir, hshift a.1 a.2 z⟩
      invFun := fun a => ⟨a.1 + (-z) • dir, hshift a.1 a.2 (-z)⟩
      left_inv := by
        intro a
        apply Subtype.ext
        ext i
        simp [add_assoc, add_left_comm, add_comm, add_smul]
      right_inv := by
        intro a
        apply Subtype.ext
        ext i
        simp [add_assoc, add_left_comm, add_comm, add_smul] }
  simpa [shiftEquiv] using
    (prob_uniform_congr_equiv (α := (U : Type)) (e := shiftEquiv)
      (P := fun a : (U : Type) => δᵣ(a.1, V) ≤ δ))

theorem exists_basepoint_with_large_line_prob_aux {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {U : Finset (ι → F)} [Nonempty U]
  (dir : ι → F)
  (hshift : ∀ a ∈ (U : Finset (ι → F)), ∀ z : F, a + z • dir ∈ (U : Finset (ι → F)))
  {V : Set (ι → F)} {δ ε : ℝ≥0} :
  Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε →
    ∃ a : U, Pr_{let z ←$ᵖ F}[δᵣ(a.1 + z • dir, V) ≤ δ] > ε := by
  intro hprob
  classical
  let good : (ι → F) → Prop := fun w => δᵣ(w, V) ≤ δ
  let lineProb (a : U) : ENNReal := Pr_{ let z ←$ᵖ F }[ good (a.1 + z • dir) ]
  let P2 : ENNReal := Pr_{ let a ←$ᵖ U; let z ←$ᵖ F }[ good (a.1 + z • dir) ]

  have hP2 : P2 = ∑' a : U, ($ᵖ U) a * lineProb a := by
    simpa [P2, lineProb] using
      (prob_tsum_form_split_first (D := ($ᵖ U))
        (D_rest := fun a : U => (do
          let z ← $ᵖ F
          return good (a.1 + z • dir))))

  have hswap :
      (do
          let a ← $ᵖ U
          let z ← $ᵖ F
          return good (a.1 + z • dir) : PMF Prop) =
        (do
          let z ← $ᵖ F
          let a ← $ᵖ U
          return good (a.1 + z • dir) : PMF Prop) := by
    simpa [Bind.bind, PMF.bind] using
      (PMF.bind_comm ($ᵖ U) ($ᵖ F) (fun a z => (pure (good (a.1 + z • dir)) : PMF Prop)))

  have hP2_swap : P2 = Pr_{ let z ←$ᵖ F; let a ←$ᵖ U }[ good (a.1 + z • dir) ] := by
    have hswap' := congrArg (fun p : PMF Prop => (p True : ENNReal)) hswap
    simpa [P2] using hswap'

  have hP2_eq : P2 = Pr_{ let u ←$ᵖ U }[ good u.1 ] := by
    rw [hP2_swap]
    have hsplit :
        Pr_{ let z ←$ᵖ F; let a ←$ᵖ U }[ good (a.1 + z • dir) ] =
          ∑' z : F, ($ᵖ F) z * Pr_{ let a ←$ᵖ U }[ good (a.1 + z • dir) ] := by
      simpa using
        (prob_tsum_form_split_first (D := ($ᵖ F))
          (D_rest := fun z : F => (do
            let a ← $ᵖ U
            return good (a.1 + z • dir))))
    rw [hsplit]
    have hconst : ∀ z : F, Pr_{ let a ←$ᵖ U }[ good (a.1 + z • dir) ] = Pr_{ let a ←$ᵖ U }[ good a.1 ] := by
      intro z
      simpa [good] using
        (prob_uniform_shift_invariant (U := U) (dir := dir) (hshift := hshift)
          (V := V) (δ := δ) (z := z))
    have : (∑' z : F, ($ᵖ F) z * Pr_{ let a ←$ᵖ U }[ good (a.1 + z • dir) ]) =
        ∑' z : F, ($ᵖ F) z * Pr_{ let a ←$ᵖ U }[ good a.1 ] := by
      refine tsum_congr ?_
      intro z
      congr 1
      exact hconst z
    rw [this]
    simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

  have hP2_gt : P2 > ε := by
    simpa [hP2_eq] using hprob

  have hsum_gt : (∑' a : U, ($ᵖ U) a * lineProb a) > ε := by
    simpa [hP2] using hP2_gt

  rcases exists_of_weighted_avg_gt ($ᵖ U) lineProb (ε : ENNReal) hsum_gt with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [lineProb] using ha

theorem exists_basepoint_with_large_line_prob {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {U'_sub : Submodule F (ι → F)} {u0 dir : ι → F} (hdir : dir ∈ U'_sub)
  {V : Set (ι → F)} {δ ε : ℝ≥0} :
  letI U' : Finset (ι → F) := (U'_sub : Set (ι → F)).toFinset
  letI U : Finset (ι → F) := U'.image (fun x => u0 + x)
  haveI : Nonempty U := by
    classical
    apply Finset.Nonempty.to_subtype
    refine ⟨u0, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨0, ?_, by simp⟩
    simpa [U', Set.mem_toFinset] using (show (0 : ι → F) ∈ (U'_sub : Set (ι → F)) from U'_sub.zero_mem)
  Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε →
    ∃ a : U, Pr_{let z ←$ᵖ F}[δᵣ(a.1 + z • dir, V) ≤ δ] > ε := by
  classical
  let U' : Finset (ι → F) := (U'_sub : Set (ι → F)).toFinset
  let U : Finset (ι → F) := U'.image (fun x => u0 + x)
  haveI : Nonempty U := by
    classical
    apply Finset.Nonempty.to_subtype
    refine ⟨u0, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨0, ?_, by simp⟩
    simpa [U', Set.mem_toFinset] using (show (0 : ι → F) ∈ (U'_sub : Set (ι → F)) from U'_sub.zero_mem)
  intro hprob
  have hshift : ∀ a ∈ (U : Finset (ι → F)), ∀ z : F, a + z • dir ∈ (U : Finset (ι → F)) := by
    intro a ha z
    rcases Finset.mem_image.1 ha with ⟨x, hxU', rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨x + z • dir, ?_, ?_⟩
    · have hxsub : x ∈ U'_sub := by
        simpa [U', Set.mem_toFinset] using hxU'
      have hdir' : dir ∈ U'_sub := hdir
      have hxzsub : x + z • dir ∈ U'_sub := by
        exact U'_sub.add_mem hxsub (U'_sub.smul_mem z hdir')
      simpa [U', Set.mem_toFinset] using hxzsub
    · simpa [add_assoc]
  have := exists_basepoint_with_large_line_prob_aux (U := U) (dir := dir) hshift (V := V) (δ := δ) (ε := ε)
  simpa [U, U'] using (this (by simpa [U, U'] using hprob))


theorem average_proximity_implies_proximity_of_linear_subspace [DecidableEq ι] [DecidableEq F]
  {u : Fin (l + 2) → ι → F} {k : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ∈ Set.Ioo 0 (1 - (ReedSolomonCode.sqrtRate (k + 1) domain))) :
  letI U'_submodule : Submodule F (ι → F) :=
    Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F))
  letI U' : Finset (ι → F) := (U'_submodule : Set (ι → F)).toFinset
  letI U : Finset (ι → F) := U'.image (fun x => u 0 + x)
  haveI : Nonempty U := by
    classical
    apply Finset.Nonempty.to_subtype
    refine ⟨u 0, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨0, ?_, by simp⟩
    simpa [U', Set.mem_toFinset] using (show (0 : ι → F) ∈ (U'_submodule : Set (ι → F)) from
      U'_submodule.zero_mem)
  letI ε : ℝ≥0 := ProximityGap.errorBound δ (k + 1) domain
  letI V := ReedSolomon.code domain (k + 1)
  Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε → ∀ u' ∈ U', δᵣ(u', V) ≤ δ := by
  classical
  intro hprob
  intro u' hu'
  have hu'_sub :
      u' ∈ (Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)) :
        Submodule F (ι → F)) := by
    simpa [Set.mem_toFinset] using hu'
  have hδ_le : δ ≤ 1 - ReedSolomonCode.sqrtRate (k + 1) domain :=
    le_of_lt hδ.2
  rcases
      (exists_basepoint_with_large_line_prob
        (ι := ι) (F := F)
        (U'_sub :=
          (Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)) :
            Submodule F (ι → F)))
        (u0 := u 0) (dir := u') (hdir := hu'_sub)
        (V := ReedSolomon.code domain (k + 1))
        (δ := δ) (ε := ProximityGap.errorBound δ (k + 1) domain)
        hprob)
    with ⟨a, hline⟩
  have hCA :
      δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
        (C := ReedSolomon.code domain (k + 1)) (δ := δ)
        (ε := ProximityGap.errorBound δ (k + 1) domain) :=
    RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := k + 1) (domain := domain)
      (δ := δ) hδ_le
  have hJA :
      jointAgreement (C := ReedSolomon.code domain (k + 1)) (δ := δ)
        (W := Code.finMapTwoWords a.1 u') := by
    apply hCA
    simpa [Code.finMapTwoWords] using hline
  have :
      δᵣ((Code.finMapTwoWords a.1 u') 1, ReedSolomon.code domain (k + 1)) ≤ δ :=
    jointAgreement_implies_second_proximity
      (ι := ι) (F := F) (C := ReedSolomon.code domain (k + 1))
      (δ := δ) (W := Code.finMapTwoWords a.1 u') hJA
  simpa [Code.finMapTwoWords] using this

end

end BCIKS20ProximityGapSection6

section BCIKS20ProximityGapSection7

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ}

namespace WeightedAgreement

open NNReal Finset Function

open scoped BigOperators

section

variable {n : Type} [Fintype n] [DecidableEq n]

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]
         (μ : ι → Set.Icc (0 : ℚ) 1)

/-- Relative μ-agreement between words `u` and `v`. -/
noncomputable def agree (u v : ι → F) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ { i | u i = v i }, (μ i).1

/-- `μ`-agreement between a word and a set `V`. -/
noncomputable def agree_set (u : ι → F) (V : Finset (ι → F)) [Nonempty V] : ℝ :=
  (Finset.image (agree μ u) V).max' (nonempty_coe_sort.1 (by aesop))

/-- Weighted size of a subdomain. -/
noncomputable def mu_set (ι' : Finset ι) : ℝ :=
  1/(Fintype.card ι) * ∑ i ∈ ι', (μ i).1

/-- `μ`-weighted correlated agreement. -/
noncomputable def weightedCorrelatedAgreement
  (C : Set (ι → F)) [Nonempty C] {k : ℕ} (U : Fin k → ι → F) : ℝ :=
  sSup {x |
    ∃ D' ⊆ (Finset.univ (α := ι)),
      x = mu_set μ D' ∧
      ∃ v : Fin k → ι → F, ∀ i, v i ∈ C ∧ ∀ j ∈ D', v i j = U i j
  }

open ReedSolomonCode

instance {domain : ι ↪ F} {deg : ℕ} : Nonempty (finCarrier domain deg) := by
  unfold finCarrier
  apply Nonempty.to_subtype
  simp [ReedSolomon.code]
  exact Submodule.nonempty (Polynomial.degreeLT F deg)

open ProbabilityTheory in
/-- Weighted correlated agreement over curves.
    Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve generated by vectors `u`, such that the probability that a random
point on the curve is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.
-/
theorem weighted_correlated_agreement_for_parameterized_curves
  [DecidableEq ι] [Fintype ι] [DecidableEq F] [Fintype F]
  {l : ℕ}
  {k : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0}
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  letI ε := ProximityGap.errorBound δ deg domain
  letI pr :=
    let curve := Curve.polynomialCurveFinite (F := F) (A := F) u
    Pr_{let u ←$ᵖ curve}[agree_set μ u (finCarrier domain deg) ≥ α]
  (hproximity : pr > (l + 1 : NNReal) * ε) →
  (h_additionally : pr ≥
    ENNReal.ofReal (
      ((l + 1) * (M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
      *
      (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
    )
  ) →
  ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ ι' ≥ α ∧
    ∀ i, ∀ x ∈ ι', u i x = v i x := sorry

/-- Weighted correlated agreement over curves.
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve generated by vectors `u`, such that the probability that a random
point on the curve is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.

Version with different bounds.
-/
theorem weighted_correlated_agreement_for_parameterized_curves'
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M m : ℕ}
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI S : Finset F := {
    z : F | agree_set μ (fun i ↦ ∑ j, z ^ j.1 * u j i) (finCarrier domain deg) ≥ α
  }
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  (hS :
    Finset.card S >
      max ((1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2 * (l + 1) / (3 * sqrtRate^3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) / sqrtRate.toReal)
    ) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := sorry

open Uniform in
open scoped Pointwise in
open ProbabilityTheory in
/-- Weighted correlated agreement over affine spaces.
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space generated by vectors `u`, such that the probability that a random
point from the space is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.
-/
theorem weighted_correlated_agreement_over_affine_spaces
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {M : ℕ}
  {α : ℝ≥0} :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  (hα : sqrtRate < α) →
  (hα₁ : α < 1) →
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
  letI ε := ProximityGap.errorBound α deg domain
  letI pr :=
    Pr_{let u ←$ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
    }[agree_set μ u (finCarrier domain deg) ≥ α]
  pr > ε →
  pr ≥ ENNReal.ofReal (
         ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
         *
         (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
       ) →
  ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ ι' ≥ α ∧
    ∀ i, ∀ x ∈ ι', u i x = v i x := by sorry

open scoped ProbabilityTheory in
open scoped Pointwise in
open Uniform in
/-- Weighted correlated agreement over affine spaces.
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space generated by vectors `u`, such that the probability that a random
point from the space is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u` have weighted correlated agreement.

Version with different bounds.
-/
theorem weighted_correlated_agreement_over_affine_spaces'
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M m : ℕ}
  (hm : 3 ≤ m)
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) :
  letI sqrtRate := ReedSolomonCode.sqrtRate deg domain
  letI pr :=
    Pr_{let u ←$ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)
    }[agree_set μ u (finCarrier domain deg) ≥ α]
  (hα : sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α) →
  letI numeratorl : ℝ := (1 + 1 / (2 * m : ℝ))^7 * m^7 * (Fintype.card ι)^2
  letI denominatorl : ℝ := (3 * sqrtRate^3) * Fintype.card F
  letI numeratorr : ℝ := (2 * m + 1) * (M * Fintype.card ι + 1)
  letI denominatorr : ℝ := sqrtRate * Fintype.card F
  pr > ENNReal.ofReal (max (numeratorl / denominatorl) (numeratorr / denominatorr)) →
  ∃ v : Fin (l + 2) → ι → F,
    (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
    mu_set μ {i : ι | ∀ j, u j i = v j i} ≥ α := by sorry

/--
Lemma 7.5 in [BCIKS20].

This is the “list agreement on a curve implies correlated agreement” lemma.

We are given two lists of functions `u, v : Fin (l + 2) → ι → F`, where each `v i` is a
Reed–Solomon codeword of degree `deg` over the evaluation domain `domain`.  From these
lists we form the bivariate “curves”

* `w   x z = ∑ i, z^(i.1) * u i x`,
* `wtilde x z = ∑ i, z^(i.1) * v i x`.

Fix a finite set `S' ⊆ F` with `S'.card > l + 1`, and a (product) measure `μ` on the
evaluation domain `ι`.  Assume that for every `z ∈ S'` the one-dimensional functions
`w · z` and `wtilde · z` have agreement at least `α` with respect to `μ`.  Then the set
of points `x` on which *all* coordinates agree, i.e. `u i x = v i x` for every `i`,
has μ-measure strictly larger than

`α - (l + 1) / (S'.card - (l + 1))`.
-/
lemma list_agreement_on_curve_implies_correlated_agreement_bound
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {v : Fin (l + 2) → ι → F}
  (hv : ∀ i, v i ∈ (ReedSolomon.code domain deg))
  {S' : Finset F}
  (hS'_card : S'.card > l + 1) :
  letI w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  letI wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  (hS'_agree : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α) →
  mu_set μ {x : ι | ∀ i, u i x = v i x} >
  α - ((l + 1) : ℝ) / (S'.card - (l + 1)) := by sorry

/--
Lemma 7.6 in [BCIKS20].

This is the “integral-weight” strengthening of the list-agreement-on-a-curve ⇒
correlated-agreement bound.

We have two lists of functions `u, v : Fin (l + 2) → ι → F`, where each `v i` is a
Reed–Solomon codeword of degree `deg` over the evaluation domain `domain`.  From
these lists we form the bivariate “curves”
* `w x z     = ∑ i, z^(i.1) * u i x`,
* `wtilde x z = ∑ i, z^(i.1) * v i x`.

The domain `ι` is finite and is equipped with a weighted measure `μ`, where each
weight `μ i` is a rational with common denominator `M`.  Let `S' ⊆ F` be a set of
field points with
* `S'.card > l + 1`, and
* `S'.card ≥ (M * Fintype.card ι + 1) * (l + 1)`.

Assume that for every `z ∈ S'` the µ-weighted agreement between `w · z` and
`wtilde · z` is at least `α`.  Then the µ-measure of the set of points where *all*
coordinates agree, i.e. where `u i x = v i x` for every `i`, is at least `α`:

`mu_set μ {x | ∀ i, u i x = v i x} ≥ α`.
-/
lemma sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M : ℕ}
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  {v : Fin (l + 2) → ι → F}
  (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
  {S' : Finset F}
  (hS'_card : S'.card > l + 1)
  (hS'_card₁ : S'.card ≥ (M * Fintype.card ι + 1) * (l + 1)) :
  letI w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  letI wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  (hS'_agree : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α) →
  mu_set μ {x : ι | ∀ i, u i x = v i x} ≥ α := by sorry
end

end WeightedAgreement

end BCIKS20ProximityGapSection7

end ProximityGap
