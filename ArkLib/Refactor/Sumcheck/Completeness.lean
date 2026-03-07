/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.Defs
import ArkLib.Refactor.Sumcheck.SingleRound

/-!
# Perfect Completeness (Backend-Agnostic)

This file isolates the **perfect completeness** argument for Sumcheck from the concrete
implementation of the honest prover's round polynomial computation.

The only assumption we make about the prover backend in round `i` is that the polynomial it
sends agrees (as a function) with the *true* partial-sum function at:
- all domain points `D a`, needed for the verifier's sum check
- the verifier's challenge `r`, needed to relate the next-round target to the reduced claim

In particular, this file does **not** depend on Lagrange interpolation correctness.
-/

noncomputable section

open CompPoly CPoly ProtocolSpec

namespace Sumcheck

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
variable {n m deg : ℕ}

/-! ## “True” partial-sum target and round function -/

/-- The evaluation point obtained by fixing the first `i` variables to `fixed`
and the remaining `n - i` variables to `D ∘ z`. -/
def evalPoint {i : ℕ} (fixed : Vector R i) (D : Fin m → R)
    (z : Fin (n - i) → Fin m) : Fin n → R :=
  fun k =>
    if h : k.val < i then fixed[k.val]
    else
      let rem := k.val - i
      if h' : rem < n - i then D (z ⟨rem, h'⟩) else 0

/-- The “true” remaining-sum target after fixing the first `i` variables to `fixed`. -/
def trueTarget (poly : OStmt R deg n) {i : ℕ} (fixed : Vector R i) (D : Fin m → R) : R :=
  (Finset.univ : Finset (Fin (n - i) → Fin m)).sum (fun z =>
    CMvPolynomial.eval (evalPoint (n := n) (m := m) fixed D z) poly.val)

/-- The “true” round function in round `i`: fix the first `i` variables to `fixed`,
set the next variable to `t`, and sum over the remaining `n - i - 1` variables in `D`. -/
def trueRoundValue (poly : OStmt R deg n) {i : ℕ}
    (fixed : Vector R i) (D : Fin m → R) (t : R) : R :=
  (Finset.univ : Finset (Fin (n - i - 1) → Fin m)).sum (fun z =>
    CMvPolynomial.eval
      (fun k =>
        if h₁ : k.val < i then fixed[k.val]
        else if k.val = i then t
        else
          let rem := k.val - i - 1
          if h₂ : rem < n - i - 1 then D (z ⟨rem, h₂⟩) else 0)
      poly.val)

/-! ## Backend spec -/

/-- A backend for computing the round polynomial in round `i`. -/
structure RoundPolyBackend (poly : OStmt R deg n) (D : Fin m → R) (i : ℕ) where
  roundPoly : Vector R i → CDegreeLE R deg
  /-- Correctness as a *function*: the computed polynomial agrees with the true round function
  at all points in `R`. -/
  correct : ∀ (fixed : Vector R i) (t : R),
    CPolynomial.eval t (roundPoly fixed).val = trueRoundValue (n := n) (m := m)
      (poly := poly) fixed D t

/-! ## Single-round perfect completeness (assuming backend correctness) -/

/-- Single-round perfect completeness, stated on the concrete `SingleRound.verifier`:
if the incoming target equals the true remaining sum, and the prover sends any polynomial that
agrees with the true round function, then the verifier accepts. -/
theorem singleRoundVerifier_accept_of_backend
    (poly : OStmt R deg n) (D : Fin m → R) (i : ℕ)
    (backend : RoundPolyBackend (R := R) (n := n) (m := m) (deg := deg) poly D i)
    (fixed : Vector R i) (target : R)
    (hTarget : target = (Finset.univ : Finset (Fin m)).sum (fun a =>
      trueRoundValue (n := n) (m := m) (poly := poly) (i := i) fixed D (D a)))
    (chal : R) :
    ((Sumcheck.verifier (R := R) (deg := deg) D) target
        (backend.roundPoly fixed, (chal, PUnit.unit))).isSome := by
  let p : CDegreeLE R deg := backend.roundPoly fixed
  have hsum :
      (Finset.univ : Finset (Fin m)).sum (fun a =>
          CPolynomial.eval (D a) p.val) =
        (Finset.univ : Finset (Fin m)).sum (fun a =>
          trueRoundValue (n := n) (m := m) (poly := poly) (i := i) fixed D (D a)) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [p, backend.correct]
  have hcond :
      (Finset.univ : Finset (Fin m)).sum (fun j =>
          CPolynomial.eval (D j) p.val) = target := by
    -- `hsum` rewrites LHS to the true round sum; `hTarget` identifies that with `target`.
    simpa [hTarget] using hsum.trans rfl
  have hcond' :
      (Finset.univ : Finset (Fin m)).sum (fun j =>
          CPolynomial.eval (D j) (backend.roundPoly fixed).val) = target := by
    simpa [p] using hcond
  -- unfold the verifier and discharge the `if` using `hcond'`
  -- (we explicitly `simp` the `HVector.head`/`tail` projections from the transcript)
  simp [Sumcheck.verifier, HVector.head, HVector.tail, hcond']

/-! ## Lemmas relating trueTarget and trueRoundValue -/

omit [DecidableEq R] in
/-- The true target after pushing one challenge equals the true round value. -/
theorem trueTarget_push_eq_trueRoundValue
    (poly : OStmt R deg n) (D : Fin m → R) (i : ℕ) (fixed : Vector R i) (r : R) :
    trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := i + 1) (fixed.push r) D =
      trueRoundValue (R := R) (n := n) (m := m) (poly := poly) (i := i) fixed D r := by
  unfold trueTarget trueRoundValue
  refine Finset.sum_congr rfl ?_
  intro z _
  congr 1
  funext k
  by_cases hk : k.1 < i
  · have hk' : k.1 < i + 1 := Nat.lt_trans hk (Nat.lt_succ_self i)
    simp [evalPoint, hk, hk']
  · by_cases hEq : k.1 = i
    · simp [evalPoint, hEq]
    · have hlt : ¬ k.1 < i + 1 := by omega
      have hsub : k.1 - (i + 1) = k.1 - i - 1 := by omega
      have hsubN : n - (i + 1) = n - i - 1 := by omega
      simp [evalPoint, hk, hEq, hlt, hsub, hsubN]

omit [DecidableEq R] in
/-- At round index `0`, `trueTarget` is exactly the full-domain sum. -/
theorem trueTarget_at_zero
    (poly : OStmt R deg n) (D : Fin m → R) (empty : Vector R 0) :
    trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := 0) empty D =
      (Finset.univ : Finset (Fin n → Fin m)).sum (fun z =>
        CMvPolynomial.eval (D ∘ z) poly.val) := by
  unfold trueTarget
  refine Finset.sum_congr rfl ?_
  intro z _
  congr 1
  funext k
  simp [evalPoint]

omit [DecidableEq R] in
/-- At the terminal round (`i = n`), `trueTarget` is just direct evaluation at the
fixed challenge point. -/
theorem trueTarget_at_n
    (poly : OStmt R deg n) (D : Fin m → R) (fixed : Vector R n) :
    trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := n) fixed D =
      CMvPolynomial.eval (fun j : Fin n => fixed.get j) poly.val := by
  classical
  unfold trueTarget
  have hcard : Fintype.card (Fin (n - n) → Fin m) = 1 := by simp
  rcases (Fintype.card_eq_one_iff.mp hcard) with ⟨z0, hz0⟩
  have huniv : (Finset.univ : Finset (Fin (n - n) → Fin m)) = {z0} := by
    ext z; simp [hz0 z]
  rw [huniv]
  have heval :
      evalPoint (R := R) (n := n) (m := m) fixed D z0 =
        fun j : Fin n => fixed.get j := by
    funext j; simp [evalPoint, Vector.get_eq_getElem]
  simp [heval]

end Sumcheck

