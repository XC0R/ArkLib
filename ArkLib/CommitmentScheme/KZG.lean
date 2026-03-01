/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann and Quang Dao
-/


import ArkLib.CommitmentScheme.Basic
import ArkLib.CommitmentScheme.HardnessAssumptions
import ArkLib.AGM.Basic
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import ArkLib.ToVCVio.DistEq
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimOracle
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.CachingOracle

/-! ## The KZG Polynomial Commitment Scheme

In this file, we define the KZG polynomial commitment scheme, and prove its correctness and
straightline extraction in the AGM. -/

open CompPoly.CPolynomial
open Polynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [Fact (0 < p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

omit [DecidableEq Gₜ] [DecidableEq G₁] in
lemma lin_fst (g₁ : G₁) (g₂ : G₂) (a : ℤ) : a • (pairing g₁ g₂) =  pairing (g₁ ^ a) (g₂) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul (g₁ ^ a)) (Additive.ofMul g₂)
  simp [ofMul_zpow]

omit [DecidableEq Gₜ] [DecidableEq G₁] in
lemma lin_snd (g₁ : G₁) (g₂ : G₂) (a : ℤ) : a • (pairing g₁ g₂) =  pairing (g₁) (g₂ ^ a) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul g₁) (Additive.ofMul (g₂ ^ a))
  simp [ofMul_zpow]

lemma modp_eq (x y : ℤ) (g : G) (hxy : x ≡ y [ZMOD p]) : g ^ x = g ^ y := by
  have hordg : g = 1 ∨ orderOf g = p := by
    have ord_g_dvd : orderOf g ∣ p := by
      have hc : Nat.card G = p := (PrimeOrderWith.hCard : Nat.card G = p)
      simpa [hc] using (orderOf_dvd_natCard g)
    have hdisj : orderOf g = 1 ∨ orderOf g = p := (Nat.dvd_prime hp.out).1 ord_g_dvd
    simpa [orderOf_eq_one_iff] using hdisj
  rcases hordg with ord1 | ordp
  · simp [ord1]
  · have hxmy : (orderOf g : ℤ) ∣ x - y := by
      have hxmy_p : (p : ℤ) ∣ x - y := by
        simpa using (Int.modEq_iff_dvd.mp hxy.symm)
      simpa [ordp] using hxmy_p
    exact (orderOf_dvd_sub_iff_zpow_eq_zpow).1 hxmy

lemma modp_eq_additive (x y : ℤ) (g : Additive G) (hxy : x ≡ y [ZMOD p]) : x • g = y • g := by
  have hxyeq : (Additive.toMul g) ^ x = (Additive.toMul g) ^ y :=
    modp_eq (G:=G) (p:=p) (g:=(Additive.toMul g)) x y hxy
  simpa [ofMul_toMul, ofMul_zpow] using congrArg Additive.ofMul hxyeq

/-- The vector of length `n + 1` that consists of powers:
  `#v[1, g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)` -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

variable {n : ℕ} -- the maximal degree of polynomials that can be commited to/opened.

/-- The `srs` (structured reference string) for the KZG commitment scheme with secret exponent `a`
    is defined as `#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ (n - 1))], #v[g₂, g₂ ^ a]` -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- One can verify that the `srs` is valid via using the pairing -/
def checkSrs (proveSrs : Vector G₁ (n + 1)) (verifySrs : Vector G₂ 2) : Prop :=
  ∀ i : Fin n,
    pairing (proveSrs[i.succ]) (verifySrs[0]) = pairing (proveSrs[i.castSucc]) (verifySrs[1])

/-- To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of
maximum degree `n`), we compute: `∏ i : Fin (n+1), srs[i] ^ (p.coeff i)` -/
def commit (srs : Vector G₁ (n + 1)) (coeffs : Fin (n + 1) → ZMod p) : G₁ :=
  ∏ i : Fin (n + 1), srs[i] ^ (coeffs i).val

omit [Module (ZMod p) (Additive G₁)] [DecidableEq G₁] in
/-- The commitment to a mathlib polynomial `poly` of maximum degree `n` is equal to
`g₁ ^ (poly.1.eval a).val` -/
theorem commit_eq {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : degreeLT (ZMod p) (n + 1)) :
    commit (towerOfExponents g₁ a n) (degreeLTEquiv _ _ poly) = g₁ ^ (poly.1.eval a).val := by
  have {g₁ : G₁} (a b : ℕ) : g₁^a = g₁^b ↔ g₁^(a : ℤ) = g₁^(b : ℤ) := by
    simp only [zpow_natCast]
  simp only [commit, towerOfExponents, Fin.getElem_fin, Vector.getElem_ofFn]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum,
    eval_eq_sum_degreeLTEquiv poly.property,
      this,
      ←orderOf_dvd_sub_iff_zpow_eq_zpow]

  have hordg₁ : g₁ = 1 ∨ orderOf g₁ = p := by
    have ord_g₁_dvd : orderOf g₁ ∣ p := by rw [← hpG1]; apply orderOf_dvd_natCard
    rw [Nat.dvd_prime hp.out, orderOf_eq_one_iff] at ord_g₁_dvd
    exact ord_g₁_dvd

  rcases hordg₁ with ord1 | ordp
  · simp [ord1]
  · simp [ordp, ←ZMod.intCast_eq_intCast_iff_dvd_sub]
    apply Fintype.sum_congr
    intro x
    exact mul_comm _ _

omit [Module (ZMod p) (Additive G₁)] [DecidableEq G₁] in
/-- The commitment to a computable polynomial (CPolynomial) `poly` of maximum degree `n+1` is equal to
`g₁ ^ (poly.eval a).val`.
Note that the degree of a CPolynomial is the mathematical degree + 1 for non-zero polynomials. -/
theorem commit_eq_UniPoly {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : CPolynomial (ZMod p)) (hn : poly.degree ≤ n + 1) :
    commit (towerOfExponents g₁ a n)
    ((coeff poly) ∘ Fin.val)
  = g₁ ^ (poly.eval a).val := by
  have {g₁ : G₁} (a b : ℕ) : g₁^a = g₁^b ↔ g₁^(a : ℤ) = g₁^(b : ℤ) := by
    simp only [zpow_natCast]
  simp only [commit, towerOfExponents, Fin.getElem_fin, Vector.getElem_ofFn]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum,
      ←eval_toPoly_eq_eval,
      eval_eq_sum,
      this,
      ←orderOf_dvd_sub_iff_zpow_eq_zpow]

  have hordg₁ : g₁ = 1 ∨ orderOf g₁ = p := by
    have ord_g₁_dvd : orderOf g₁ ∣ p := by rw [← hpG1]; apply orderOf_dvd_natCard
    rw [Nat.dvd_prime hp.out, orderOf_eq_one_iff] at ord_g₁_dvd
    exact ord_g₁_dvd

  let f := fun e a_1 ↦ a_1 * a ^ e
  have hf : ∀ (i : ℕ), f i 0 = 0 := by
    intro i
    simp_all only [zero_mul, f]
  have hs : poly.toPoly.support ⊆ Finset.range (n + 1) := by
    have hnatDeg : poly.toPoly.natDegree < (n+1) := by
      by_cases hcoeff: ∃ i, poly.coeff i ≠ 0
      · calc poly.toPoly.natDegree = poly.degree - 1 := by simp_rw [degree_toPoly' hcoeff]
        _ ≤ n := by exact Nat.sub_le_sub_right hn 1
        _ < n + 1 := Nat.lt_succ_self n
      · have hcoeff: ∀i, poly.toPoly.coeff i = 0 := by
          simp_all [coeff_toPoly]
        have hpoly: poly.toPoly = 0 := by
          ext n; exact hcoeff n
        simp [hpoly]
    simp_rw [Polynomial.supp_subset_range hnatDeg]

  rcases hordg₁ with ord1 | ordp
  · simp [ord1]
  · simp [ordp, ←ZMod.intCast_eq_intCast_iff_dvd_sub]
    rw [Polynomial.sum_eq_of_subset
      (R := ZMod p) (S := ZMod p) (p := poly.toPoly)
      f hf (s := Finset.range (n + 1)) hs]
    simp_rw [f, coeff_toPoly, Array.getD_eq_getD_getElem?]
    simp only [mul_comm]
    rw [Fin.sum_univ_eq_sum_range (fun x => a ^ x * poly[x]?.getD 0) (n+1)]


/-- To generate an opening proving that a polynomial `poly` has a certain evaluation at `z`,
  we return the commitment to the polynomial `q(X) = (poly(X) - poly.eval z) / (X - z)` -/
def generateOpening [Fact (Nat.Prime p)] (srs : Vector G₁ (n + 1))
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) : G₁ :=
    letI poly : CPolynomial (ZMod p) := mk (Array.ofFn coeffs)
    letI q : CPolynomial (ZMod p) := divByMonic (poly - C (poly.eval z))
      (X - C z)
    commit srs (fun i : Fin (n + 1) => q.coeff i)

/-- To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed
evaluation `v`, we use the pairing to check "in the exponent" that `p(a) - p(z) = q(a) * (a - z)`,
  where `p` is the polynomial and `q` is the quotient of `p` at `z` -/
def verifyOpening (verifySrs : Vector G₂ 2) (commitment : G₁) (opening : G₁)
    (z : ZMod p) (v : ZMod p) : Bool :=
  pairing (commitment / g₁ ^ v.val) (verifySrs[0]) =
    pairing opening (verifySrs[1] / g₂ ^ z.val)

-- p(a) - p(z) = q(a) * (a - z)
-- e ( C / g₁ ^ v , g₂ ) = e ( O , g₂ ^ a / g₂ ^ z)
omit [DecidableEq G₁] in
theorem correctness (hpG1 : Nat.card G₁ = p) (n : ℕ) (a : ZMod p)
  (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) :
  let poly : CPolynomial (ZMod p) := mk (Array.ofFn coeffs)
  let v : ZMod p := poly.eval z
  let srs : Vector G₁ (n + 1) × Vector G₂ 2 := generateSrs (g₁:=g₁) (g₂:=g₂) n a
  let C : G₁ := commit srs.1 coeffs
  let opening: G₁ := generateOpening srs.1 coeffs z
  verifyOpening pairing (g₁:=g₁) (g₂:=g₂) srs.2 C opening z v := by
  intro poly v
  unfold verifyOpening generateSrs
  simp only [decide_eq_true_eq]

  -- helper facts for the proof

  -- coeffs is the finite coefficients map of poly
  have hcoeffs : coeffs = (coeff poly) ∘ Fin.val := by
    simp_all only [poly]
    ext x : 1
    simp only [Function.comp_apply]
    simp only [Array.getD_eq_getD_getElem?, Array.size_ofFn, Fin.is_lt, getElem?_pos,
    Array.getElem_ofFn, Fin.eta, Option.getD_some]

  -- the (mathematical) degree of poly is less than n+1
  have hpdeg : degree poly ≤ n+1 := by
    simp_rw [←Trim.size_eq_degree]
    apply le_trans (Trim.size_le_size (p := poly))
    simp_rw [poly]
    simp

  -- expansion of (a-z) to Polynomial form
  have haz : (a-z) = eval a (X - C z) := by
    simp_rw [←eval_toPoly_eq_eval, toPoly_sub, eval_sub,
    eval_toPoly_eq_eval]
    simp only [eval_X, eval_C]

  -- the polynomial form of (a-z) is monic
  have hmonic : monic (X - C z) := by
    simp only [monic_X_sub_C]

  -- the proof

  -- restate the commitment as the evaluation of poly at a (C => g₁^poly(a))
  simp_rw [hcoeffs, commit_eq_UniPoly hpG1 poly hpdeg]

  -- define q(X) := (poly(X) - poly(z)) / (X-z)
  -- and restate the opening as the evaluation of q at a (opening => g₁^q(a))
  simp_rw [generateOpening, ←hcoeffs]
  set q := (mk poly - C (eval z (mk poly))).divByMonic (X - C z)
  have hqdeg : degree q ≤ n+1 := by
    calc
      degree q ≤ degree (mk poly - C (eval z (mk poly))) := by
        simp [q, degree_divByMonic hmonic]
      _ ≤ max (degree (mk poly)) (degree (C (eval z (mk poly)))) :=
        degree_sub _ _
      _ ≤ max (n+1) 1 := by
        apply max_le_max
        · exact hpdeg
        · by_cases h0 : eval z (mk poly) = 0
          · simp only [h0, degree_C_zero, zero_le]
          · simp [degree_C (x := eval z (mk poly)) (by simpa using h0)]
      _ = n+1 := by
        simp only [Nat.succ_le_succ (Nat.zero_le n), sup_of_le_left]
  have hfun: (fun i ↦ q.coeff ↑i : Fin (n+1) → ZMod p) = (coeff q) ∘ Fin.val := by rfl
  simp_rw [hfun, commit_eq_UniPoly hpG1 q hqdeg]

  -- evaluate the pairing linearly.
  -- e (g₁^poly(a) / g₂^poly(z), g₂)= e (g₁^q(a), g₂^a / g₂^(z))
  -- => (poly(a) - poly(z)) • e (g₁,g₂) = (q(a) * (a-z)) • e (g₁,g₂)
  simp only [towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn, pow_zero, pow_one]
  simp_rw [←zpow_natCast_sub_natCast, ←zpow_natCast, ←lin_snd, ←lin_fst, smul_smul]

  -- eliminate the pairing and reason only about the exponents: poly(a) - poly(z) = q(a) * (a-z)
  apply modp_eq_additive
  refine (Int.modEq_iff_dvd).2 ?_
  let x : ℤ := (↑(eval a poly).val) - (↑v.val)
  let y : ℤ := (↑(a.val) - ↑(z.val)) * ↑(eval a q).val
  refine (Iff.mp (ZMod.intCast_eq_intCast_iff_dvd_sub (a := x) (b := y) (c := p))) ?_
  subst x y; simp

  -- unfold q to obtain the self canceling goal:
  -- poly(a) - poly(z) = (poly(a) - poly(z)) / (a-z) * (a-z)
  -- prove the goal using the eval isomorphism to mathlib Polynomials
  subst v q
  simp_rw [haz]
  simp_rw [←eval_toPoly_eq_eval, toPoly_divByMonic hmonic,toPoly_sub, ←eval_mul, toPoly_C, toPoly_X]
  simp_rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval]
  simp only [eval_sub, Polynomial.eval_C, sub_self, map_zero, sub_zero]

open Commitment

-- TODO this should be a fact in VCV-io I think..

local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  Response := ZMod p
  answer := fun coeffs z =>
    let poly : CPolynomial (ZMod p) := mk (Array.ofFn coeffs)
    poly.eval z

open scoped NNReal

namespace CommitmentScheme

/-- The KZG instantiated as a **(functional) commitment scheme**.

  The scheme takes a pregenerated srtuctured reference string (srs) for the
  commiter and the verifier (generated by `generateSrs`).

  - `commit` : a function that commits to an `n + 1`-tuple of coefficients `coeffs`
  (corresponding to a polynomial of maximum degree `n`)
  - `opening` : a non-interactive reduction (i.e. soly the committer sends a single
  message) to prove the evaluation of the commited polynomial at a point `z`. The
  message from the prover is the witness for the evaluation.
-/
def KZG :
    Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁ (Vector G₁ (n + 1) × Vector G₂ 2)
    (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩ where
  keygen := do
    let a ← $ᵗ(ZMod p)
    let srs := generateSrs (g₁:=g₁) (g₂:=g₂) n a
    return (srs,srs)
  commit := fun ck coeffs _ => return commit ck.1 coeffs
  opening := fun (ck,vk) => {
    prover := {
      PrvState := fun
        | 0 => (Fin (n + 1) → ZMod p) × ZMod p
        | _ => Unit

      input := fun ⟨⟨commitment, z, v⟩, ⟨coefficients, _⟩⟩ =>
        (coefficients, z)

      sendMessage := fun ⟨0, _⟩ => fun (coefficients, z) => do
        let opening := generateOpening ck.1 coefficients z
        return (opening, ())

      receiveChallenge := fun ⟨i, h⟩ => by
        have : i = 0 := Fin.eq_zero i
        subst this
        nomatch h

      output := fun _ => return (true, ())
    }

    verifier := {
      verify := fun ⟨commitment, z, v⟩ transcript => do
        let opening : G₁ := transcript ⟨0, by decide⟩
        return verifyOpening (g₁:=g₁) (g₂:=g₂) pairing vk.2 commitment opening z v
    }
  }

open OracleSpec OracleComp SubSpec ProtocolSpec SimOracle

section Correctness

-- TODO next two lemmas should be in VCV-io
/-- randomOracle never fails on any query.
    The proof follows from the fact that randomOracle either returns a cached value (pure)
    or samples uniformly (which never fails). -/
lemma neverFails_randomOracle_impl {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [spec.DecidableEq] [∀ i, SelectableType (spec.range i)]
    (β : Type) (q : OracleQuery spec β) (s : spec.QueryCache) :
    ((randomOracle.impl q).run s).neverFails := by
  cases q with
  | query i t =>
    simp only [randOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind]
    cases h : s i t with -- case split on whether the query is cached
    | some u =>
      simp only [StateT.run_pure]
      exact neverFails_pure _
    | none =>
      simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_modifyGet]
      rw [neverFails_bind_iff]
      constructor
      · rw [neverFails_bind_iff]
        refine ⟨neverFails_uniformOfFintype _, ?_⟩
        intro u _
        exact neverFails_pure _
      · intro ⟨u, s'⟩ _
        exact neverFails_pure _

lemma neverFails_stateT_run_simulateQ {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α σ : Type}
    (so : QueryImpl spec (StateT σ (OracleComp spec'))) (oa : OracleComp spec α) (s : σ)
    (hso : ∀ (β : Type) (q : OracleQuery spec β) (s' : σ), ((so.impl q).run s').neverFails)
    (h : oa.neverFails) : ((simulateQ so oa).run s).neverFails := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure, neverFails_pure]
  | query_bind i t oa ih =>
    simp only [neverFails_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, neverFails_bind_iff]
    refine ⟨hso _ (query i t) s, ?_⟩
    intro ⟨r, s'⟩ _
    exact ih r s' (h r)
  | failure => simp [neverFails] at h

/- the KZG satisfies perfect correctness as defined in `CommitmentScheme` -/
omit [DecidableEq G₁] in
theorem correctness (hpG1 : Nat.card G₁ = p) (_a : ZMod p) {g₁ : G₁} {g₂ : G₂}
    [SelectableType G₁] :
    Commitment.perfectCorrectness (pure ∅) (randomOracle)
    (KZG (n:=n) (g₁:=g₁) (g₂:=g₂) (pairing:=pairing)) := by
    intro data randomness query
    have hpSpec : ProverOnly ⟨!v[.P_to_V], !v[G₁]⟩ := by
      refine { prover_first' := ?_ }; simp
    simp only [Reduction.run_of_prover_first]
    simp [KZG]
    constructor
    · apply neverFails_stateT_run_simulateQ
      · -- The oracle implementation (randomOracle ++ₛₒ challengeQueryImpl) never fails
        intro β q s'
        cases q with
        | query i t =>
          cases i with
          | inl i₁ => exact neverFails_randomOracle_impl _ (OracleQuery.query i₁ t) s'
          | inr i₂ => fin_cases i₂
      · -- liftComp of uniform sampling never fails
        simp only [neverFails_lift_comp_iff, neverFails_uniformOfFintype]
    · intro a_sample _ _
      constructor
      · simp [acceptRejectRel]
        exact KZG.correctness (g₁:=g₁) (g₂:=g₂) (pairing:=pairing) hpG1 n a_sample data query
      · exact KZG.correctness (g₁:=g₁) (g₂:=g₂) (pairing:=pairing) hpG1 n a_sample data query

end Correctness

section FunctionBinding
/- In this section prove that the KZG is function binding under the ARSDH assumption. The proof is a
reduction to ARSDH following "Proof of Lemma 9.1" from Chiesa, Guan, Knabenhans, and Yu's "On the
Fiat–Shamir Security of Succinct Arguments from Functional Commitments"
(https://eprint.iacr.org/2025/902.pdf).
The paper proof is structured into 5 steps (with substeps), we note each step/substep accordingly in
our definitions.
-/

variable {η : Type} (advSpec : OracleSpec η)

/-- used to decide which strategy the adversary will take
(breaking ARSDH based on a conflict or breaking ARSDH based on lagrange interpolation) -/
def find_conflict (points : List (ZMod p × ZMod p × G₁))
  : Option ((ZMod p × ZMod p × G₁) × (ZMod p × ZMod p × G₁)) :=
  points.findSome? fun (α₁,β₁,pf₁) =>
    points.findSome? fun (α₂,β₂,pf₂) =>
      if α₁ == α₂ && β₁ != β₂ then some ((α₁,β₁, pf₁), (α₂,β₂, pf₂)) else none

-- case 1: there's conflicting evaluations (binding failure)

/- step 3 a) Choose S to be a size-(D + 1) subset of 𝔽 such that αᵢ∈ S and [Zₛ(τ)]₁ ≠ [0]₁
Note the reduction works mostly with S \ {αᵢ}, so this function only returns S \ {αᵢ}. -/
def choose_S_conflict (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hn : 1 ≤ n) : Finset (ZMod p) :=
  let arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x else none
    else none
  arr.take n |>.toList.toFinset -- ∪ {αᵢ} to be the S referenced in the paper

-- case 2: there's no conflicting evaluation, but more than D distinct evaluations (degree failure)

/-- needed to satisfy #S = D+1 -/
def erase_duplicates : List (ZMod p × ZMod p × G₁) → List (ZMod p × ZMod p × G₁)
  | [] => []
  | (αᵢ,βᵢ,pfᵢ)::xs => if xs.any (fun (αⱼ,_,_) => αⱼ = αᵢ) then erase_duplicates xs
    else (αᵢ,βᵢ,pfᵢ)::erase_duplicates xs

/-- step 4 b) Find i∗ ∈ {D + 2,...,L} such that βi∗ ≠ Lₒ(αi∗) -/
def find_diversion (L₀ : CPolynomial (ZMod p))
  : List (ZMod p × ZMod p × G₁) → Option (ZMod p × ZMod p × G₁)
  | [] => none
  | (αᵢ,βᵢ,pfᵢ)::xs => if eval αᵢ L₀ ≠ βᵢ then some (αᵢ,βᵢ,pfᵢ) else find_diversion L₀ xs

/-- Step 4 c) Find S := {αij}j∈[D+1] from {αi}i∈[D+1]∪{αi∗} such that [Lagrange(S)]₁ ≠ cm
Try replacing each element in the list with `diversion` and check if the interpolated
polynomial's commitment differs from `cm`. Returns the first such replacement as a Finset. -/
def find_S (srs : Vector G₁ (n + 1) × Vector G₂ 2) (cm : G₁) (diversion : ZMod p × ZMod p × G₁)
  : List (ZMod p × ZMod p × G₁) → List (ZMod p × ZMod p × G₁) →
    Option (Finset (ZMod p × ZMod p × G₁))
  | [], _ => none
  | x::xs, prefix_acc =>
    let candidate := prefix_acc ++ [diversion] ++ xs
    let L : CPolynomial (ZMod p) := sorry -- interpolate candidate
    if commit srs.1 (fun i : Fin (n + 1) => L.coeff i) ≠ cm
    then some candidate.toFinset
    else find_S srs cm diversion xs (prefix_acc ++ [x])

-- put it together

/-- These are steps 3 and 4 of the reduction listed in the paper (Proof of Lemma 9.1 in https://eprint.iacr.org/2025/902.pdf) -/
def map_FB_instance_to_ARSDH_inst' {L : ℕ}
  (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ × Vector (ZMod p × ZMod p × Bool × G₁) L)
  : Option (Finset (ZMod p) × G₁ × G₁) :=
  do
  let (srs, cm, fb_instance) := val
  let points := fb_instance.toList.map (fun (αᵢ,βᵢ,bᵢ,pfᵢ) => (αᵢ,βᵢ,pfᵢ))
  if let some ((α₁,β₁,pf₁),(α₂,β₂,pf₂)) := find_conflict points then
    -- step 3
    let S := choose_S_conflict α₁ srs sorry
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (pf₁ / pf₂) ^ (1 /(β₂ - β₁).val)
    return (S ∪ {α₁}, h₁, h₂)
  else
    -- step 4
    let distinct_points := erase_duplicates points
    let L₀ : CPolynomial (ZMod p) := sorry -- interpolate distinct_points.take (D+1)
    let diversion ← find_diversion L₀ (distinct_points.take (n+1))
    let S_points ← find_S srs cm diversion (distinct_points.drop (n+1)) []
    let S := S_points.image Prod.fst
    let Zₛ := ∏ s ∈ S, (X - C s)
    let Lₛ : CPolynomial (ZMod p):= sorry -- interpolate S
    let h₁ := cm / KZG.commit srs.1 (Lₛ.coeff ∘ Fin.val)
    let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
      -- 1/(Z_{S \ {α}}(α))
    let h₂ : G₁ := ∏ ⟨α, β,pf⟩ ∈ S_points, pf ^ (d α).val
    return (S, h₁, h₂)

def map_FB_instance_to_ARSDH_inst {L : ℕ}
  (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ × Vector (ZMod p × ZMod p × Bool × G₁) L)
  : (Finset (ZMod p) × G₁ × G₁)
  -- for instances that break function binding map_FB_instance_to_ARSDH_inst' should always
  -- be 'Some'
  := Option.getD (map_FB_instance_to_ARSDH_inst' val) (∅, 1, 1)

def map_FB_to_ARSDH {L : ℕ}
  (val : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ × Vector (ZMod p × ZMod p × Bool × G₁) L)
  : (ZMod p × Finset (ZMod p) × G₁ × G₁)
  := (val.1, map_FB_instance_to_ARSDH_inst val.2)
    -- val.1 = τ, val.2 = (srs, cm, fb_instance)

/-- Abbreviation for a function binding adversary for KZG. -/
abbrev KZGFunctionBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (L : ℕ) (AuxState : Type) :=
  Commitment.FunctionBindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState L
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

include g₁ g₂ pairing in
/-- The reduction breaking ARSDH using a (successful) Function Binding Adversary.
The redution follows the proof of lemma 9.1 (under Def. 9.6) in https://eprint.iacr.org/2025/902.pdf -/
def reduction (L : ℕ) (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.ARSDHAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs =>
    letI kzgScheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    -- designed such that ProbEvent_comp can be applied and thus the main task of reasoning
    -- is discharged to the predicate level.
    map_FB_instance_to_ARSDH_inst <$> -- TODO replace this option wrapper and use monad instead?
    -- map_FB_instance_to_ARSDH_inst (Step 3 and 4 of the reduction) is applied to the result
    -- of the adversary (step 1 and 2 of the reduction)
    letI so : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp)) ++ₛₒ
        (challengeQueryImpl (pSpec := ⟨!v[.P_to_V], !v[G₁]⟩))
    (simulateQ so
          (do
            let (ck, vk) := (srs, srs)
            let (cm, claims) ← liftComp (adversary.claim ck) _
            let reduction := Reduction.mk (adversary.prover ck)
              (kzgScheme.opening (ck, vk)).verifier
            let evals ← claims.mapM (fun ⟨q, r, st⟩ =>
              do
                let ⟨⟨transcript, _⟩, verifier_accept⟩ ← reduction.run (cm, q, r) st
                let pf := transcript 0
                return (q, r, verifier_accept, pf)
              )
            return (srs, cm, evals)
          ))

/-- ARSDH condition for an adversary "to win" -/
def ARSDH_cond (D : ℕ) : (ZMod p × Finset (ZMod p) × G₁ × G₁) → Prop :=
  fun (τ, S, (h₁ : G₁), h₂) =>
    let Zₛ : CPolynomial (ZMod p) := ∏ s ∈ S, (X - C s)
    S.card = D + 1 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / Zₛ.eval τ).val

/-- Function binding condition for an adversary "to win" -/
def FB_cond (n L : ℕ) : Vector (ZMod p × ZMod p × Bool) L → Prop :=
  fun (x : Vector (ZMod p × ZMod p × Bool) L) =>
    (∀ (i : Fin x.size), x[i].2.2 = true) -- ∀i. verifier_accept
    ∧ (¬ ∃ (d : Fin (n + 1) → ZMod p),
      ∀ (i : Fin x.size), OracleInterface.answer d x[i].1 = x[i].2.1)
      -- ∄ coeffs s.t. ∀i poly(coeffs).eval q = verifier_accept

/-- Extended function binding condition (taking more input values, logic unchanged) -/
def FB_cond_ext (n L : ℕ) : (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
  Vector (ZMod p × ZMod p × Bool × G₁) L) → Prop :=
  fun (x : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    Vector (ZMod p × ZMod p × Bool × G₁) L) =>
    let evals := x.2.2.2.map (fun (a, b, c, _d) => (a, b, c))
    FB_cond n L evals

/-- Function binding game -/
def FB_game {n L : ℕ} (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  (simulateQ (randomOracle ++ₛₒ (challengeQueryImpl (pSpec := pSpec')) :
      QueryImpl _ (StateT unifSpec.QueryCache ProbComp)) <|
      (do
        let (ck, vk) ← liftComp scheme.keygen _
        let (cm, claims) ← liftComp (adversary.claim ck) _
        let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
        claims.mapM (fun ⟨q, r, st⟩ =>
          do
            let ⟨_, verifier_accept⟩ ← reduction.run (cm, q, r) st
            return (q, r, verifier_accept)
          )
      : OracleComp _ _)).run' ∅

/-- Extended function binding game (returning more internal values, logic unchanged) -/
def FB_game_ext {n L : ℕ} {g₁ : G₁} {g₂ : G₂} (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  (simulateQ
    (randomOracle ++ₛₒ (challengeQueryImpl (pSpec := pSpec')) :
      QueryImpl _ (StateT unifSpec.QueryCache ProbComp))
    <|
    (do
      let a ← liftComp ($ᵗ (ZMod p)) _
      let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n a
      let (cm, claims) ← liftComp (adversary.claim srs) _
      let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
      let evals ← claims.mapM (fun ⟨q, r, st⟩ =>
        do
          let ⟨⟨transcript, _⟩, verifier_accept⟩ ← reduction.run (cm, q, r) st
          let pf := transcript 0
          return (q, r, verifier_accept, pf)
        )
      return (a, srs, cm, evals) : OracleComp _ _)
  ).run' ∅

omit [DecidableEq G₁] in
/-- Transition 1: extending output for proofs and commitment preserves the condition -/
lemma FB_game_ext_eq_FB_game {n L : ℕ} {AuxState : Type} [SelectableType G₁]
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    [FB_cond n L | FB_game AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = [FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  let scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  let proj := fun (x : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    Vector (ZMod p × ZMod p × Bool × G₁) L) => x.2.2.2.map (fun (a, b, c, _) => (a, b, c))
  -- First show condition equivalence: FB_cond ∘ proj = FB_cond_ext, then unfold it
  have h_cond : ∀ x, (FB_cond n L ∘ proj) x ↔ FB_cond_ext n L x := by
    intro x; simp only [Function.comp_apply, proj, FB_cond_ext]
  conv_rhs => rw [show
    [FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = [FB_cond n L ∘ proj | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    by apply probEvent_ext; intro x _; exact (h_cond x).symm]
  -- Use probEvent_map to pull the projection into the monad
  rw [← probEvent_map]
  -- Now both sides have the form [FB_cond n L | some_computation]
  -- Goal: [FB_cond n L | FB_game ...] = [FB_cond n L | proj <$> FB_game_ext ...]
  -- Show OracleComp equality: FB_game = proj <$> FB_game_ext
  congr 1
  simp only [FB_game, FB_game_ext, proj, scheme, KZG]
  simp only [StateT.run'_eq, Functor.map_map]
  -- unpack key_gen in FB_game to mirror the srs computation in FB_game_ext
  simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  -- peel the srs computation layers off
  apply bind_congr
  intro a_state
  simp [StateT.run_map]
  apply bind_congr
  intro srs_state

  -- monad level definition of the projection (keeping the state)
  let projf := (fun (x : (OracleInterface.Query (Fin (n + 1) → ZMod p)
    × OracleInterface.Response (Fin (n + 1) → ZMod p) × Bool × G₁))
    ↦ (x.1, x.2.1, x.2.2.1))
  have hfmap: (fun (a : Vector (OracleInterface.Query (Fin (n + 1) → ZMod p)
    × OracleInterface.Response (Fin (n + 1) → ZMod p) × Bool × G₁) L × unifSpec.QueryCache)
    ↦ Vector.map (fun (x:ZMod p × ZMod p × Bool × G₁) ↦ (x.1, x.2.1, x.2.2.1)) a.1)
    = (fun x ↦ x.1) ∘
    (fun (a : Vector (OracleInterface.Query (Fin (n + 1) → ZMod p)
    × OracleInterface.Response (Fin (n + 1) → ZMod p) × Bool × G₁) L × unifSpec.QueryCache)
    ↦ (Vector.map projf a.1, a.2))
    := by
    simp_all only [Function.comp_apply, Prod.forall, proj, projf]
    obtain ⟨fst, snd⟩ := a_state
    obtain ⟨fst_1, snd_1⟩ := srs_state
    obtain ⟨fst_1, snd_2⟩ := fst_1
    rfl

  -- drag the projection into the monad
  rw [hfmap]
  rw [comp_map]
  rw [←StateT.run_map]
  rw [←simulateQ_map]
  rw [vector_map_mapM]
  simp_all only [Function.comp_apply, Prod.forall, Fin.isValue, Functor.map_map, proj, projf]

/-- Transition 2: FB condition implies ARSDH condition after mapping -/
lemma FB_cond_le_ARSDH_cond {n L : ℕ} {AuxState : Type} [SelectableType G₁]
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    [FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ [(ARSDH_cond n) ∘ map_FB_to_ARSDH |
      FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  apply probEvent_mono
  sorry

omit [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- Transition 3: dragging the map into the probability event -/
lemma map_instance_drag {n L : ℕ} {AuxState : Type} [SelectableType G₁]
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩) :
    [(ARSDH_cond n) ∘ map_FB_to_ARSDH | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = [(ARSDH_cond n) |
      map_FB_to_ARSDH <$> FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme] := by
  simp only [Nat.reduceAdd, Fin.vcons_fin_zero, Fin.isValue, probEvent_map]

/-- Transition 4: the mapped game equals the ARSDH experiment -/
lemma ARSDH_game_eq {n L : ℕ} {AuxState : Type} [SelectableType G₁]
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    [(ARSDH_cond n) | map_FB_to_ARSDH <$>
      FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L AuxState adversary) := by
  let scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.ARSDH_Experiment]
  apply probEvent_congr
  · simp [ARSDH_cond]
  · simp [map_FB_to_ARSDH, FB_game_ext, reduction]
    simp only [StateT.run]

    have hτ :
      let pSpec' := { dir := !v[Direction.P_to_V], «Type» := !v[G₁] }
      OracleComp.evalDist (simulateQ randomOracle ($ᵗZMod p) ∅) = OracleComp.evalDist
      (simulateQ (randomOracle ++ₛₒ (challengeQueryImpl (pSpec := pSpec'))
        : QueryImpl _ (StateT _ ProbComp)) (liftComp ($ᵗZMod p) (unifSpec ++ₒ _ ))
        ∅) :=
      by
      intro pSpec'
      have gen : ∀ {β : Type} (oa : OracleComp unifSpec β),
        (simulateQ (randomOracle ++ₛₒ (challengeQueryImpl (pSpec := pSpec'))
          : QueryImpl _ (StateT _ ProbComp))
          (liftComp oa (unifSpec ++ₒ _)))
        = simulateQ randomOracle oa := by
        intro β oa
        induction oa using OracleComp.inductionOn with
        | pure x => simp
        | query_bind i t oa ih => simp [Function.comp_def, ih]; rfl
        | failure => simp
      simp only [gen]

    have hsrs: ∀ n a, Groups.generateSrs (p := p) (g₁ := g₁) (g₂ := g₂) n a
        = generateSrs (p := p) (g₁ := g₁) (g₂ := g₂) n a := by
      intros n a
      simp only [Groups.generateSrs, generateSrs, Groups.towerOfExponents, towerOfExponents]

    simp_rw [hτ,hsrs]
    rfl

/-- The ARSDH experiment is bounded by the ARSDH error -/
lemma ARSDH_error_bound {n L : ℕ} {AuxState : Type} [SelectableType G₁] (ARSDHerror : ℝ≥0)
    (hARSDH : Groups.ARSDHAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n ARSDHerror)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n (reduction (g₁ := g₁) (g₂ := g₂)
      (pairing := pairing) L AuxState adversary)
    ≤ ARSDHerror := by
  simp_all [Groups.ARSDHAssumption]

/- the KZG satisfies function binding as defined in `CommitmentScheme` provided ARSDH holds. -/
theorem functionBinding {g₁ : G₁} {g₂ : G₂}
    (L : ℕ) (AuxState : Type) [SelectableType G₁] (ARSDHerror : ℝ≥0)
    (hARSDH : Groups.ARSDHAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n ARSDHerror) :
    Commitment.functionBinding (L := L) (init := pure ∅) (impl := randomOracle)
      (hn := rfl) (hpSpec := { prover_first' := by simp }) AuxState
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) ARSDHerror := by
    letI scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    simp only [Commitment.functionBinding]
    intro adversary
    letI game := FB_game AuxState adversary scheme
    letI game_ext := FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
    convert (
      calc [FB_cond n L | game]
      _ = [FB_cond_ext n L | game_ext] :=
        FB_game_ext_eq_FB_game (pairing := pairing) adversary
      _ ≤ [(ARSDH_cond n) ∘ map_FB_to_ARSDH | game_ext] :=
        FB_cond_le_ARSDH_cond (pairing := pairing) adversary
      _ = [(ARSDH_cond n) | map_FB_to_ARSDH <$> game_ext] :=
        map_instance_drag adversary scheme
      _ = Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
        (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L AuxState adversary) :=
        ARSDH_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) adversary
      _ ≤ ARSDHerror := ARSDH_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing) ARSDHerror
        hARSDH adversary)

#check probEvent_mono
#check probEvent_map
#check probEvent_bind_eq_tsum
#check probEvent_eq_tsum_ite

end FunctionBinding

end CommitmentScheme

end KZG
