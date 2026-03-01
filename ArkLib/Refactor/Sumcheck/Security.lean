/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.Defs
import ArkLib.Refactor.Sumcheck.General
import ArkLib.Refactor.Sumcheck.Completeness
import ArkLib.Refactor.Security.Composition
import ArkLib.Refactor.Security.StateFunction

/-!
# Security Theorems for the Sumcheck Protocol

Security properties for the general sumcheck protocol:

- **Perfect completeness**: If the polynomial truly sums to the claimed target over `D^n`,
  the honest prover always makes the verifier accept (for *all* challenge sequences).
- **Round-by-round soundness**: Each challenge round can "flip" an incorrect claim to
  a correct-looking one with probability at most `deg / |F|`.
- **Soundness** (corollary): A false claim passes all `n` rounds with probability
  at most `n · deg / |F|`.

## Overview

The sumcheck protocol is a reduction from the *sumcheck claim*
  `∑_{x ∈ D^n} poly(x) = target`
to an *evaluation claim*
  `poly(r₁, …, rₙ) = finalTarget`
where `r₁, …, rₙ` are the verifier's challenges.

Sumcheck is a pure interactive proof — no shared oracle is needed. Perfect
completeness holds deterministically for all challenge sequences. Soundness
is over the uniform distribution on challenges.
-/

noncomputable section

open CompPoly CPoly ProtocolSpec OracleComp OracleSpec
open scoped NNReal ENNReal

namespace Sumcheck

variable {R : Type} [Field R] [BEq R] [LawfulBEq R]
variable {n m : ℕ} {deg : ℕ}

/-! ## Challenge sampling instances -/

noncomputable instance instChallengesSampleableGeneralPSpec [SampleableType R] :
    ChallengesSampleable (generalPSpec R deg n) :=
  ChallengesSampleable.ofReplicate n

/-! ## Perfect Completeness

The honest prover makes the verifier accept for every valid input. Since sumcheck has a
deterministic prover and verifier, this holds for *all* challenge sequences. We formulate
it using `Reduction.run` which pairs the prover and verifier. -/

/-- Perfect completeness for the general sumcheck reduction.

If `target = ∑_{x ∈ D^n} poly(x)`, then for any challenge sequence, running the
honest prover against `generalVerifier` yields `some` (acceptance). -/
theorem generalReduction_perfectCompleteness_of_backend [DecidableEq R]
    (poly : CMvPolynomial n R) (D : Fin m → R) (evalPoints : Vector R (deg + 1))
    (backend : ∀ i : ℕ, Vector R i → CDegreeLE R deg)
    (h_sum : ∀ i (fixed : Vector R i),
      (Finset.univ : Finset (Fin m)).sum (fun j =>
          CPolynomial.eval (D j) (backend i fixed).val) =
        trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := i) fixed D)
    (h_next : ∀ i (fixed : Vector R i) (r : R),
      CPolynomial.eval r (backend i fixed).val =
        trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := i + 1) (fixed.push r) D)
    (target : R) (h_valid : target ∈ Sumcheck.inputLang poly D)
    (challenges : Challenges (generalPSpec R deg n)) :
    ((generalReduction (R := R) (deg := deg) (n := n) (m := m)
        poly D evalPoints backend).run target () challenges).1.isSome := by
  classical
  -- Simplification helpers for the `Id` monad.
  have pure_id {α : Type} (x : α) : (pure x : Id α) = x := rfl
  have bind_id {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
  have map_id {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl
  -- State transition induced by the backend polynomial.
  let stepState (st : RoundState (R := R)) (r : R) : RoundState (R := R) :=
    let p := backend st.i st.challenges
    { i := st.i + 1
      challenges := st.challenges.push r
      target := CPolynomial.eval r p.val }
  -- Initial invariant: at `i = 0`, `trueTarget` is the full-domain sum.
  have hInv0 :
      (initState (R := R) (target := target)).target =
        trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := 0)
          (initState (R := R) (target := target)).challenges D := by
    rcases h_valid with ⟨rfl⟩
    -- Reduce `trueTarget` at `i = 0` and identify `evalPoint` with `D ∘ z`.
    -- (This is the only place we use that the initial `fixed` vector is empty.)
    change
      (Finset.univ : Finset (Fin n → Fin m)).sum (fun z =>
          CMvPolynomial.eval (D ∘ z) poly) =
        (Finset.univ : Finset (Fin n → Fin m)).sum (fun z =>
          CMvPolynomial.eval
            (evalPoint (R := R) (n := n) (m := m)
              (fixed := (⟨#[], rfl⟩ : Vector R 0)) D z)
            poly)
    -- goal: two sums over `Fin n → Fin m` match pointwise
    refine Finset.sum_congr rfl ?_
    intro z _
    -- show the evaluation functions coincide
    have :
        (evalPoint (R := R) (n := n) (m := m) (fixed := (⟨#[], rfl⟩ : Vector R 0)) D z) =
          (D ∘ z) := by
      funext k
      -- `i = 0`, so we always take the `else` branch and `rem = k.val < n`.
      simp [evalPoint]
    simp [this]
  -- Main round-by-round lemma: running `k` honest rounds yields a transcript that the
  -- `k`-fold composed verifier accepts, and the verifier’s output matches the honest state.
  -- Helpers: the honest prover after `k` rounds from state `st`, and its execution.
  let iter (k : Nat) (st : RoundState (R := R)) :
      Prover Id (RoundState (R := R) × Unit) (generalPSpec (R := R) deg k) :=
    Prover.iterate (m := Id) (S := RoundState (R := R) × Unit)
      (pSpec (R := R) deg) k
      (roundProverStep (R := R) (deg := deg) backend)
      (st, ())
  let run (k : Nat) (st : RoundState (R := R))
      (ch : Challenges (generalPSpec (R := R) deg k)) :
      Transcript (generalPSpec (R := R) deg k) × (RoundState (R := R) × Unit) :=
    Prover.run (m := Id) (Output := RoundState (R := R) × Unit)
      (generalPSpec (R := R) deg k) (iter k st) ch
  have hRoundByRound :
      ∀ (k : Nat) (st : RoundState (R := R))
        (hInv :
          st.target =
            trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := st.i) st.challenges D)
        (ch : Challenges (generalPSpec (R := R) deg k)),
        (Verifier.compNth k (roundVerifierState (R := R) (deg := deg) (m := m) D)) st
            (run k st ch).1 =
          some (run k st ch).2.1 := by
    intro k st hInv ch
    induction k generalizing st with
    | zero =>
        cases ch
        simp [run, iter, generalPSpec, Prover.iterate, Prover.run, Verifier.compNth,
          pure_id]
    | succ k ih =>
        let p : CDegreeLE R deg := backend st.i st.challenges
        let r : R := ch.head
        let st1 : RoundState (R := R) := stepState st r
        have hGuard :
            (Finset.univ : Finset (Fin m)).sum (fun j =>
                CPolynomial.eval (D j) p.val) = st.target := by
          simpa [p, hInv] using (h_sum st.i st.challenges)
        have hInv1 :
            st1.target =
              trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := st1.i)
                st1.challenges D := by
          simpa [st1, stepState, p, r] using (h_next st.i st.challenges r)
        -- Expand `run (k+1) st ch` into the first-round transcript piece and the tail run.
        have hRun :
            run (k + 1) st ch =
              (((p, (r, (run k st1 ch.tail).1))
                  : Transcript (generalPSpec (R := R) deg (k + 1))),
                (run k st1 ch.tail).2) := by
          -- `simp` unfolds `run/iter` and computes the first round;
          -- the remaining goal is definitional.
          simp [run, iter, generalPSpec, Prover.iterate, Prover.run, Prover.comp, roundProverStep,
            st1, stepState, p, r, pure_id, bind_id]
          rfl
        have hIH :
            (Verifier.compNth k (roundVerifierState (R := R) (deg := deg) (m := m) D)) st1
                (run k st1 ch.tail).1 =
              some (run k st1 ch.tail).2.1 :=
          ih (st := st1) hInv1 ch.tail
        -- Assemble one verifier step + IH:
        -- rewrite the honest transcript via `hRun`, then unfold the first verifier round.
        rw [hRun]
        -- After rewriting, the verifier’s first round is
        -- `roundVerifierState` on transcript `(p,r)`,
        -- which accepts by `hGuard` and outputs `st1`. The remaining verifier is `compNth k`,
        -- so the goal
        -- reduces to `hIH`.
        simpa [Verifier.compNth, Verifier.comp, roundVerifierState, Transcript.split,
          HVector.splitAt, HVector.head, HVector.tail, p, r, st1, stepState, hGuard] using hIH
  -- Now unfold `Reduction.run` and apply `hRoundByRound`
  -- at `k = n` from the initial state.
  let st0 : RoundState (R := R) := initState (R := R) (target := target)
  have hInvStart :
      st0.target =
        trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := st0.i) st0.challenges D := by
    simpa [st0, initState] using hInv0
  let runOut := run n st0 challenges
  have hAccept :
      (Verifier.compNth n (roundVerifierState (R := R) (deg := deg) (m := m) D)) st0 runOut.1 =
        some runOut.2.1 :=
    hRoundByRound n st0 hInvStart challenges
  -- Expand `Reduction.run` and rewrite the verifier result to `some ...`.
  unfold ProtocolSpec.Reduction.run
  -- `generalReduction.verifier` is `generalVerifier`,
  -- i.e. `Verifier.compNth ...` on `st0`.
  exact by
    simp [generalReduction, generalVerifier, st0, runOut, run, iter, hAccept,
      pure_id, bind_id]

/-! ## Soundness

The verifier rejects any false claim with high probability over the random challenges.

The soundness argument proceeds round by round. At each round, the adversary commits a
round polynomial `p_i`. If the sum `∑_{x ∈ D} p_i(x)` doesn't match the current target,
then by the Schwartz-Zippel lemma, a uniformly random evaluation point `r_i` yields a
consistent next target with probability at most `deg / |F|`.

By a union bound over `n` rounds, the total soundness error is `n · deg / |F|`. -/

section Soundness

variable [Fintype R] [SampleableType R] [DecidableEq R]

/-!
For sumcheck soundness we need that the *true* round function in each round is a
univariate polynomial of degree ≤ `deg`. In the canonical setting this follows from
an individual-degree bound on `poly`; here we assume it abstractly to avoid entangling
the proof with polynomial-degree development.
-/

/-- Existence of a degree-`deg` polynomial realizing the true round function. -/
def TrueRoundPolyExists (poly : CMvPolynomial n R) (D : Fin m → R) : Prop :=
  ∀ (i : ℕ) (_hi : i < n) (fixed : Vector R i),
    ∃ q : CDegreeLE R deg,
      (∀ t : R,
        CPolynomial.eval t q.val =
          trueRoundValue (R := R) (n := n) (m := m) (poly := poly) (i := i) fixed D t)
      ∧
      ((Finset.univ : Finset (Fin m)).sum (fun a =>
          CPolynomial.eval (D a) q.val) =
        trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := i) fixed D)

omit [BEq R] [LawfulBEq R] [Fintype R] [SampleableType R] [DecidableEq R] in
/-- The true target after pushing one challenge equals the true round value. -/
private lemma trueTarget_push_eq_trueRoundValue
    (poly : CMvPolynomial n R) (D : Fin m → R) (i : ℕ) (fixed : Vector R i) (r : R) :
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
  · have hki : i ≤ k.1 := Nat.le_of_not_lt hk
    by_cases hEq : k.1 = i
    · have hk' : k.1 < i + 1 := by omega
      simp [evalPoint, hEq]
    · have hlt : ¬ k.1 < i + 1 := by omega
      have hsub : k.1 - (i + 1) = k.1 - i - 1 := by omega
      have hsubN : n - (i + 1) = n - i - 1 := by omega
      simp [evalPoint, hk, hEq, hlt, hsub, hsubN]

/-! ### Univariate Schwartz–Zippel (via root counting) -/

set_option linter.unusedDecidableInType false in
private lemma prob_eval_eq_le_of_ne
    (p q : CDegreeLE R deg) (hne : p.val.toPoly ≠ q.val.toPoly) :
    Pr[fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val | $ᵗ R]
      ≤ (deg : ℝ≥0) / (Fintype.card R : ℝ≥0) := by
  classical
  -- Rewrite the event using `toPoly` so we can use Mathlib root bounds.
  have h_eval : ∀ r : R,
      (CPolynomial.eval r p.val = CPolynomial.eval r q.val) ↔
        (p.val.toPoly - q.val.toPoly).eval r = 0 := by
    intro r
    -- Bridge `CPolynomial.eval` through `toPoly`, then use `sub_eq_zero`.
    -- Goal becomes: `p.eval r = q.eval r ↔ (p - q).eval r = 0`.
    simp [CompPoly.CPolynomial.eval_toPoly, Polynomial.eval_sub, sub_eq_zero]
  -- The set of bad points is contained in the roots of the nonzero polynomial `p - q`.
  let f : Polynomial R := p.val.toPoly - q.val.toPoly
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hne
    -- If `toPoly` difference is zero, then the polynomials are equal.
    -- (`sub_eq_zero` in the polynomial ring)
    simpa [f] using (sub_eq_zero.mp hf)
  have h_deg_f : f.natDegree ≤ deg := by
    -- Use the degree bounds carried by `CDegreeLE`.
    have hp : p.val.toPoly.natDegree ≤ deg := by
      simpa [CompPoly.CPolynomial.natDegree_toPoly] using p.property
    have hq : q.val.toPoly.natDegree ≤ deg := by
      simpa [CompPoly.CPolynomial.natDegree_toPoly] using q.property
    -- `natDegree (p - q) ≤ deg` follows from `natDegree_sub_le_iff_left`.
    exact (Polynomial.natDegree_sub_le_iff_left (p := p.val.toPoly) (q := q.val.toPoly)
      (n := deg) hq).2 hp
  -- Convert the probability to a cardinality fraction over a finite uniform type.
  -- Then bound the numerator by the number of roots of `f`.
  have hcard :
      ((Finset.univ.filter (fun r : R =>
          CPolynomial.eval r p.val = CPolynomial.eval r q.val)).card : ℝ≥0)
        ≤ deg := by
    -- Replace the filter predicate with `f.eval r = 0`.
    have hfilter :
        (Finset.univ.filter (fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val)) =
          Finset.univ.filter (fun r : R => f.eval r = 0) := by
      ext r
      simp [h_eval, f]
    rw [hfilter]
    -- Filter set is contained in the (distinct) roots of `f`.
    have hsub :
        Finset.univ.filter (fun r : R => f.eval r = 0) ⊆ f.roots.toFinset := by
      intro r hr
      have : f.eval r = 0 := by
        simpa using (Finset.mem_filter.mp hr).2
      -- `mem_roots` needs `f ≠ 0`.
      have : r ∈ f.roots := by
        -- `Polynomial.mem_roots` is stated for multiset roots.
        simpa [Polynomial.mem_roots hf_ne] using this
      simpa using (Multiset.mem_toFinset.2 this)
    have hle1 :
        (Finset.univ.filter (fun r : R => f.eval r = 0)).card ≤ f.roots.toFinset.card :=
      Finset.card_le_card hsub
    have hle2 : (f.roots.toFinset.card : ℕ) ≤ f.roots.card := by
      exact Multiset.toFinset_card_le f.roots
    have hle3 : (f.roots.card : ℕ) ≤ f.natDegree := by
      simpa using (Polynomial.card_roots' f)
    -- Combine and push to `ℝ≥0`.
    have : (f.roots.toFinset.card : ℕ) ≤ deg := by
      have : f.roots.card ≤ deg := by
        exact le_trans hle3 h_deg_f
      exact le_trans hle2 this
    -- `card ≤ deg` for the filter set.
    exact_mod_cast (le_trans hle1 this)
  -- Final algebra: `Pr[event] = card/filter / card` and then use the bound.
  -- `probEvent_uniformSample` gives the exact probability for uniform sampling.
  -- (Note: `Pr` returns `ℝ≥0∞`, we bound it via coercions from `ℝ≥0`.)
  have hPr :
      Pr[fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val | $ᵗ R]
        = ((Finset.univ.filter (fun r : R =>
            CPolynomial.eval r p.val = CPolynomial.eval r q.val)).card : ℝ≥0)
            / (Fintype.card R : ℝ≥0) := by
    -- Provided by `VCVio`'s `SampleableType` development.
    rw [probEvent_uniformSample (α := R)
      (p := fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val)]
    simp [div_eq_mul_inv]
  rw [hPr]
  -- Use the numerator bound.
  -- Avoid specialized division lemmas by rewriting as multiplication by an inverse.
  have hcard' :
      ((Finset.univ.filter (fun r : R =>
          CPolynomial.eval r p.val = CPolynomial.eval r q.val)).card : ℝ≥0∞)
        ≤ (deg : ℝ≥0∞) := by
    exact_mod_cast hcard
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcard' (by positivity)

/-! ### Languages and error parameters -/

/-- Output language for the reduced claim after `n` rounds.

Since sumcheck is modeled as a **reduction**, the verifier outputs the random point
`r` (the sampled challenges) together with the final value `v`. The remaining
obligation is the evaluation relation `poly(r) = v`. -/
def outputLang (poly : CMvPolynomial n R) : Set (RoundState (R := R)) :=
  { st | ∃ h : st.i = n,
      CMvPolynomial.eval (fun i : Fin n => (by
        cases h
        simpa using st.challenges.get i)) poly = st.target }

/-- State-consistency language for a single sumcheck round step. -/
def roundStateLang (poly : CMvPolynomial n R) (D : Fin m → R) :
    Set (RoundState (R := R)) :=
  { st | st.i ≤ n ∧
      st.target = trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := st.i)
        st.challenges D }

/-- At the terminal round (`i = n`), `trueTarget` is just direct evaluation at the
fixed challenge point. -/
private lemma trueTarget_at_n
    (poly : CMvPolynomial n R) (D : Fin m → R) (fixed : Vector R n) :
    trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := n) fixed D =
      CMvPolynomial.eval (fun j : Fin n => fixed.get j) poly := by
  classical
  unfold trueTarget
  have hcard : Fintype.card (Fin (n - n) → Fin m) = 1 := by
    simp
  rcases (Fintype.card_eq_one_iff.mp hcard) with ⟨z0, hz0⟩
  have huniv : (Finset.univ : Finset (Fin (n - n) → Fin m)) = {z0} := by
    ext z
    simp [hz0 z]
  rw [huniv]
  have heval :
      evalPoint (R := R) (n := n) (m := m) fixed D z0 =
        fun j : Fin n => fixed.get j := by
    funext j
    simp [evalPoint, Vector.get_eq_getElem]
  simp [heval]

/-- Any output-language state satisfies the round-state consistency language. -/
private lemma outputLang_subset_roundStateLang
    (poly : CMvPolynomial n R) (D : Fin m → R) :
    outputLang (R := R) (n := n) poly ⊆ roundStateLang (R := R) (n := n) (m := m) poly D := by
  intro st hOut
  rcases hOut with ⟨rfl, hEval⟩
  refine ⟨le_rfl, ?_⟩
  have hEval' :
      CMvPolynomial.eval (fun j : Fin st.i => st.challenges.get j) poly = st.target := by
    simpa using hEval
  have hTrue :
      trueTarget (R := R) (n := st.i) (m := m) (poly := poly) (i := st.i) st.challenges D =
        CMvPolynomial.eval (fun j : Fin st.i => st.challenges.get j) poly :=
    trueTarget_at_n (R := R) (n := st.i) (m := m) poly D st.challenges
  calc
    st.target = CMvPolynomial.eval (fun j : Fin st.i => st.challenges.get j) poly := by
      simpa using hEval'.symm
    _ = trueTarget (R := R) (n := st.i) (m := m) (poly := poly) (i := st.i) st.challenges D := by
      simpa using hTrue.symm

/-- The per-round soundness error: `deg / |F|`. -/
def roundSoundnessError : ℝ≥0 :=
  ⟨deg / Fintype.card R, by positivity⟩

/-- Per-challenge round-by-round error function (uniform across rounds). -/
def rbrSoundnessError : ChallengeIndex (generalPSpec R deg n) → ℝ≥0 :=
  fun _ => roundSoundnessError (R := R) (deg := deg)

/-- Overall soundness error as the sum of per-challenge RBR errors. -/
def soundnessError : ℝ≥0 :=
  Finset.sum Finset.univ (rbrSoundnessError (R := R) (deg := deg) (n := n))

/-! ### Empty-oracle embedding for framework-native statements

Sumcheck's plain verifier lives in `Verifier Id ...`. The framework security notions
(`Verifier.rbrSoundness` / `Verifier.soundness`) are phrased over
`Verifier (OracleComp oSpec) ...`, so we embed the plain verifier into the empty-oracle
setting. -/

private abbrev EmptySpec : OracleSpec PEmpty := []ₒ

private def emptyImpl : QueryImpl EmptySpec (StateT Unit ProbComp) :=
  fun q => PEmpty.elim q

private def generalVerifierAsOracle (D : Fin m → R) :
    Verifier (OracleComp EmptySpec) R (RoundState (R := R)) (generalPSpec R deg n) :=
  fun target tr => OptionT.mk <| pure
    ((generalVerifier (R := R) (deg := deg) (n := n) (m := m) D target tr).run)

private def roundVerifierStateAsOracle (D : Fin m → R) :
    Verifier (OracleComp EmptySpec) (RoundState (R := R)) (RoundState (R := R))
      (pSpec (R := R) deg) :=
  fun st tr => OptionT.mk <| pure
    ((roundVerifierState (R := R) (deg := deg) (m := m) D st tr).run)

/-- The single-round per-challenge RBR error (same `deg / |F|` bound). -/
def singleRoundRbrError : ChallengeIndex (pSpec (R := R) deg) → ℝ≥0 :=
  fun _ => roundSoundnessError (R := R) (deg := deg)

/-- Round-by-round soundness for a single lifted sumcheck round. -/
theorem roundVerifierState_rbrSoundness
    (poly : CMvPolynomial n R) (D : Fin m → R)
    (hTrue : TrueRoundPolyExists (R := R) (n := n) (m := m) (deg := deg) poly D) :
    rbrSoundness
      (impl := emptyImpl)
      (langIn := roundStateLang (R := R) (n := n) (m := m) poly D)
      (langOut := roundStateLang (R := R) (n := n) (m := m) poly D)
      (verifier := roundVerifierStateAsOracle (R := R) (deg := deg) (m := m) D)
      (Inv := fun _ : Unit => True)
      (rbrError := singleRoundRbrError (R := R) (deg := deg)) := by
  classical
  let toFunSR :
      (k : Nat) → RoundState (R := R) →
      PartialTranscript (pSpec (R := R) deg) k → Prop :=
    fun k stmt tr =>
      match k with
      | 0 => stmt ∈ roundStateLang (R := R) (n := n) (m := m) poly D
      | 1 => False
      | 2 =>
          let p : CDegreeLE R deg := tr.head
          let r : R := tr.tail.head
          ((Finset.univ : Finset (Fin m)).sum (fun j =>
              CPolynomial.eval (D j) p.val) = stmt.target) ∧
            ({ i := stmt.i + 1
               challenges := stmt.challenges.push r
               target := CPolynomial.eval r p.val } ∈
              roundStateLang (R := R) (n := n) (m := m) poly D)
      | _ => False
  let sf : StateFunction emptyImpl (fun _ : Unit => True)
      (roundStateLang (R := R) (n := n) (m := m) poly D)
      (roundStateLang (R := R) (n := n) (m := m) poly D)
      (roundVerifierStateAsOracle (R := R) (deg := deg) (m := m) D) := {
    toFun := toFunSR
    toFun_empty := by
      intro stmt
      simp [toFunSR]
    toFun_next := by
      intro k hk hnon stmt tr hFalse msg
      have hk_lt2 : k < 2 := by simpa [pSpec] using hk
      have hk_cases : k = 0 ∨ k = 1 := by omega
      cases hk_cases with
      | inl hk0 =>
          subst hk0
          simp [toFunSR]
      | inr hk1 =>
          exfalso
          have hch :
              ((pSpec (R := R) deg).get ⟨1, by simp [pSpec]⟩).isChallenge = false := by
            simpa [hk1] using hnon
          simp [pSpec, ProtocolSpec.Round.isChallenge] at hch
    toFun_full := by
      intro stmt tr σ0 _ hNot
      have hNoAccept :
          ¬ (∃ s ∈ roundStateLang (R := R) (n := n) (m := m) poly D,
            (roundVerifierState (R := R) (deg := deg) (m := m) D stmt tr).run = some s) := by
        intro hAcc
        rcases hAcc with ⟨s, hs, hsEq⟩
        have hGuard :
            (Finset.univ : Finset (Fin m)).sum (fun j =>
              CPolynomial.eval (D j) tr.head.val) = stmt.target := by
          by_contra hGuard
          simp [roundVerifierState, hGuard] at hsEq
        have hsOut :
            s =
              { i := stmt.i + 1
                challenges := stmt.challenges.push tr.tail.head
                target := CPolynomial.eval tr.tail.head tr.head.val } := by
          have hsEq' := hsEq
          simp only [roundVerifierState, hGuard, guard_true, Option.pure_def,
            OptionT.run_bind] at hsEq'
          exact (Option.some.inj hsEq').symm
        have hState :
            { i := stmt.i + 1
              challenges := stmt.challenges.push tr.tail.head
              target := CPolynomial.eval tr.tail.head tr.head.val } ∈
              roundStateLang (R := R) (n := n) (m := m) poly D := by
          simpa [hsOut] using hs
        exact hNot (by
          simp [toFunSR, PartialTranscript.ofTranscript, hGuard, hState])
      by_cases hrun :
          (roundVerifierState (R := R) (deg := deg) (m := m) D stmt tr).run = none
      · rw [probEvent_eq_zero_iff]
        intro s hs hsLang
        have hs' :
            some s ∈ support ((OptionT.mk do
              (simulateQ emptyImpl
                ((roundVerifierStateAsOracle (R := R) (deg := deg) (m := m) D stmt tr)).run
              ).run' σ0).run) := by
          simpa [OptionT.mem_support_iff] using hs
        have : False := by
          rcases (by
            simpa [roundVerifierStateAsOracle, simulateQ_pure,
              OptionT.mk, OptionT.run, StateT.run'] using hs' :
              ∃ u, (some s, u) ∈ support
                (pure ((roundVerifierState (R := R) (deg := deg) (m := m) D stmt tr).run, σ0))) with
            ⟨u, hu⟩
          simp [hrun, support_pure] at hu
        exact this
      · cases hrun' : (roundVerifierState (R := R) (deg := deg) (m := m) D stmt tr).run with
        | none =>
            exfalso
            exact hrun hrun'
        | some s0 =>
            have hs0 :
                (roundVerifierState (R := R) (deg := deg) (m := m) D stmt tr).run = some s0 := hrun'
            have hsNotLang :
                s0 ∉ roundStateLang (R := R) (n := n) (m := m) poly D := by
              intro hsLang
              exact hNoAccept ⟨s0, hsLang, hs0⟩
            rw [probEvent_eq_zero_iff]
            intro s hs hsLang
            have hsEq : s = s0 := by
              have hs' :
                  some s ∈ support ((OptionT.mk do
                    (simulateQ emptyImpl
                      ((roundVerifierStateAsOracle (R := R) (deg := deg) (m := m) D stmt tr)).run
                    ).run' σ0).run) := by
                simpa [OptionT.mem_support_iff] using hs
              rcases (by
                simpa [roundVerifierStateAsOracle, simulateQ_pure,
                  OptionT.mk, OptionT.run, StateT.run'] using hs' :
                  ∃ u, (some s, u) ∈ support
                    (pure ((roundVerifierState (R := R) (deg := deg) (m := m) D stmt tr).run, σ0)))
                    with
                ⟨u, hu⟩
              have hsSome : some s = some s0 := by
                simpa [hs0, support_pure] using hu
              exact Option.some.inj hsSome
            subst hsEq
            exact hsNotLang hsLang
  }
  refine ⟨sf, ?_⟩
  intro stmtIn hStmtIn Output prover i σ0 hσ0
  have hi1 : (i.1 : Nat) = 1 := by
    rcases i with ⟨i, hiChallenge⟩
    have hi_lt2 : (i : Nat) < 2 := by simp [pSpec]
    have hi_cases : (i : Nat) = 0 ∨ (i : Nat) = 1 := by omega
    cases hi_cases with
    | inl h0 =>
        exfalso
        have hch :
            ((pSpec (R := R) deg).get ⟨0, by simp [pSpec]⟩).isChallenge = true := by
          simpa [h0] using hiChallenge
        simp [pSpec, ProtocolSpec.Round.isChallenge] at hch
    | inr h1 => simp [h1]
  rcases prover with ⟨msg, cont⟩
  let mx : ProbComp (Challenges (pSpec (R := R) deg)) := sampleChallenges (pSpec (R := R) deg)
  let my : Challenges (pSpec (R := R) deg) → ProbComp (Transcript (pSpec (R := R) deg) × Output) :=
    fun ch =>
      (simulateQ emptyImpl (Prover.run (pSpec (R := R) deg) (msg, cont) ch)).run' σ0
  let trConst :
      Challenges (pSpec (R := R) deg) → Transcript (pSpec (R := R) deg) :=
    fun ch => msg ::ₕ ch.head ::ₕ HVector.nil
  let bad : (Transcript (pSpec (R := R) deg) × Output) → Prop :=
    fun z =>
      ¬ toFunSR 1 stmtIn (HVector.take 1 (pSpec (R := R) deg) z.1) ∧
        toFunSR 2 stmtIn (HVector.take 2 (pSpec (R := R) deg) z.1)
  have hBadEq : bad = fun z =>
      toFunSR 2 stmtIn (HVector.take 2 (pSpec (R := R) deg) z.1) := by
    funext z
    simp [bad, toFunSR]
  let cond : Challenges (pSpec (R := R) deg) → Prop := fun ch =>
    toFunSR 2 stmtIn (HVector.take 2 (pSpec (R := R) deg) (trConst ch))
  have hmy :
      ∀ ch,
        my ch =
          (fun out : Output => (trConst ch, out)) <$>
            (simulateQ emptyImpl (do
              let next ← cont
              next ch.head)).run' σ0 := by
    intro ch
    unfold my trConst
    simp [Prover.run, pSpec, simulateQ_bind]
  have hPoint :
      ∀ ch, Pr[bad | my ch] ≤ if cond ch then 1 else 0 := by
    intro ch
    rw [hBadEq, hmy ch, probEvent_map]
    by_cases hcond : cond ch
    · simp [cond, hcond, probEvent_le_one]
    · simp [cond, hcond]
  have hBindLe : Pr[bad | mx >>= my] ≤ Pr[cond | mx] := by
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine ENNReal.tsum_le_tsum ?_
    intro ch
    simpa [mul_ite, mul_one, mul_zero] using (mul_le_mul' le_rfl (hPoint ch))
  have hcond_le :
      Pr[cond | mx] ≤ (roundSoundnessError (R := R) (deg := deg) : ℝ≥0∞) := by
    have hsumMsg :
        (Finset.univ : Finset (Fin m)).sum (fun j =>
            CPolynomial.eval (D j) msg.val) = stmtIn.target ∨
        (Finset.univ : Finset (Fin m)).sum (fun j =>
            CPolynomial.eval (D j) msg.val) ≠ stmtIn.target :=
      em _
    cases hsumMsg with
    | inr hsumNe =>
        have hcondFalse : ∀ ch, ¬ cond ch := by
          intro ch hcond
          have hsum :
              (Finset.univ : Finset (Fin m)).sum (fun j =>
                  CPolynomial.eval (D j) msg.val) = stmtIn.target := by
            simpa [cond, toFunSR, trConst] using hcond.1
          exact hsumNe hsum
        have : Pr[cond | mx] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro ch hch hcond
          exact (hcondFalse ch) hcond
        rw [this]
        exact bot_le
    | inl hsumOk =>
        by_cases hi : stmtIn.i < n
        · rcases hTrue stmtIn.i hi stmtIn.challenges with ⟨qTrue, hqEval, hqSum⟩
          have hTargetNe :
              stmtIn.target ≠
                trueTarget (R := R) (n := n) (m := m) (poly := poly)
                  (i := stmtIn.i) stmtIn.challenges D := by
            intro hEq
            exact hStmtIn ⟨Nat.le_of_lt hi, hEq⟩
          have hne : msg.val.toPoly ≠ qTrue.val.toPoly := by
            intro hEq
            have hsumEq :
                (Finset.univ : Finset (Fin m)).sum (fun a => CPolynomial.eval (D a) msg.val) =
                  trueTarget (R := R) (n := n) (m := m) (poly := poly)
                    (i := stmtIn.i) stmtIn.challenges D := by
              calc
                (Finset.univ : Finset (Fin m)).sum (fun a => CPolynomial.eval (D a) msg.val)
                    = (Finset.univ : Finset (Fin m)).sum (fun a =>
                        CPolynomial.eval (D a) qTrue.val) := by
                        refine Finset.sum_congr rfl ?_
                        intro a _
                        simp [CompPoly.CPolynomial.eval_toPoly, hEq]
                _ = trueTarget (R := R) (n := n) (m := m) (poly := poly)
                      (i := stmtIn.i) stmtIn.challenges D := hqSum
            apply hTargetNe
            calc
              stmtIn.target
                  = (Finset.univ : Finset (Fin m)).sum (fun a =>
                      CPolynomial.eval (D a) msg.val) := hsumOk.symm
              _ = trueTarget (R := R) (n := n) (m := m) (poly := poly)
                    (i := stmtIn.i) stmtIn.challenges D := hsumEq
          have hcondEq :
              Pr[cond | mx] ≤
                Pr[fun r : R =>
                    CPolynomial.eval r msg.val = CPolynomial.eval r qTrue.val | $ᵗ R] := by
            let condR : R → Prop := fun r =>
              ({ i := stmtIn.i + 1
                 challenges := stmtIn.challenges.push r
                 target := CPolynomial.eval r msg.val } : RoundState (R := R))
                ∈ roundStateLang (R := R) (n := n) (m := m) poly D
            have hcond_as_head : ∀ ch, cond ch ↔ condR ch.head := by
              intro ch
              constructor
              · intro hcond
                simpa [cond, condR, toFunSR, trConst] using hcond.2
              · intro hcondR
                refine ⟨?_, ?_⟩
                · simpa [cond, toFunSR, trConst] using hsumOk
                · simpa [cond, condR, toFunSR, trConst] using hcondR
            have hMapHead :
                (fun ch => ch.head) <$> mx = ($ᵗ R) := by
              unfold mx sampleChallenges
              simp [pSpec, ChallengesSampleable.sampleChallenges]
            have hcondMap : Pr[cond | mx] = Pr[condR | $ᵗ R] := by
              calc
                Pr[cond | mx] = Pr[fun ch => condR ch.head | mx] := by
                  refine le_antisymm ?_ ?_
                  · refine probEvent_mono ?_
                    intro ch _ hcond
                    exact (hcond_as_head ch).1 hcond
                  · refine probEvent_mono ?_
                    intro ch _ hcondR
                    exact (hcond_as_head ch).2 hcondR
                _ = Pr[condR | (fun ch => ch.head) <$> mx] := by
                  symm
                  rw [probEvent_map]
                  rfl
                _ = Pr[condR | $ᵗ R] := by
                  simp [hMapHead]
            have hcondRle :
                Pr[condR | $ᵗ R] ≤
                  Pr[fun r : R =>
                      CPolynomial.eval r msg.val = CPolynomial.eval r qTrue.val | $ᵗ R] := by
              refine probEvent_mono ?_
              intro r _ hcondR
              have hTarget :
                  CPolynomial.eval r msg.val =
                    trueTarget (R := R) (n := n) (m := m) (poly := poly)
                      (i := stmtIn.i + 1) (stmtIn.challenges.push r) D := hcondR.2
              have hRound :
                  trueTarget (R := R) (n := n) (m := m) (poly := poly)
                    (i := stmtIn.i + 1) (stmtIn.challenges.push r) D =
                  trueRoundValue (R := R) (n := n) (m := m) (poly := poly)
                    (i := stmtIn.i) stmtIn.challenges D r :=
                trueTarget_push_eq_trueRoundValue
                  (R := R) (n := n) (m := m) (poly := poly) (D := D)
                  stmtIn.i stmtIn.challenges r
              calc
                CPolynomial.eval r msg.val
                    = trueTarget (R := R) (n := n) (m := m) (poly := poly)
                        (i := stmtIn.i + 1) (stmtIn.challenges.push r) D := hTarget
                _ = trueRoundValue (R := R) (n := n) (m := m) (poly := poly)
                      (i := stmtIn.i) stmtIn.challenges D r := hRound
                _ = CPolynomial.eval r qTrue.val := (hqEval r).symm
            exact hcondMap ▸ hcondRle
          have hSZ :
              Pr[fun r : R => CPolynomial.eval r msg.val = CPolynomial.eval r qTrue.val | $ᵗ R]
              ≤ (roundSoundnessError (R := R) (deg := deg) : ℝ≥0∞) := by
            have hSZ0 :
                Pr[fun r : R => CPolynomial.eval r msg.val = CPolynomial.eval r qTrue.val | $ᵗ R]
                ≤ ((deg : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0∞) :=
              prob_eval_eq_le_of_ne (R := R) (deg := deg) msg qTrue hne
            have hszVal :
                (roundSoundnessError (R := R) (deg := deg) : ℝ≥0∞) =
                  ((deg : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)) := by
              have hcard_ne : (Fintype.card R : ℝ≥0) ≠ 0 := by
                exact_mod_cast (Fintype.card_ne_zero (α := R))
              calc
                (roundSoundnessError (R := R) (deg := deg) : ℝ≥0∞)
                    = (((deg : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
                      rfl
                _ = ((deg : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)) := by
                      exact ENNReal.coe_div hcard_ne
            exact hszVal.symm ▸ hSZ0
          exact le_trans hcondEq hSZ
        · have hcondFalse : ∀ ch, ¬ cond ch := by
            intro ch hcond
            have hLang :
                ({ i := stmtIn.i + 1
                   challenges := stmtIn.challenges.push ch.head
                   target := CPolynomial.eval ch.head msg.val } :
                  RoundState (R := R))
                  ∈ roundStateLang (R := R) (n := n) (m := m) poly D := by
              simpa [cond, toFunSR, trConst, hsumOk] using hcond.2
            exact not_lt_of_ge hLang.1 (Nat.lt_of_not_ge hi)
          have : Pr[cond | mx] = 0 := by
            rw [probEvent_eq_zero_iff]
            intro ch hch hcond
            exact (hcondFalse ch) hcond
          rw [this]
          exact bot_le
  let flipPred : Transcript (pSpec (R := R) deg) → Prop := fun tr =>
    ¬ sf.toFun i.1 stmtIn (HVector.take i.1 (pSpec (R := R) deg) tr) ∧
      sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) (pSpec (R := R) deg) tr)
  have hBadMap : bad = fun z => flipPred z.1 := by
    funext z
    have hiSucc : (i.1 : Nat) + 1 = 2 := by omega
    apply propext
    constructor
    · intro hbad
      refine ⟨?_, ?_⟩
      · rw [hi1]
        simp [sf, toFunSR]
      · have hbad2 : toFunSR 2 stmtIn (HVector.take 2 (pSpec (R := R) deg) z.1) := by
          simpa [bad, hBadEq] using hbad
        rw [hiSucc]
        simpa [sf] using hbad2
    · intro hflip
      have hpost2' : toFunSR (i.1 + 1) stmtIn
          (HVector.take (i.1 + 1) (pSpec (R := R) deg) z.1) := by
        simpa [sf] using hflip.2
      have hpost2 : toFunSR 2 stmtIn (HVector.take 2 (pSpec (R := R) deg) z.1) := by
        rwa [hiSucc] at hpost2'
      simpa [bad, hBadEq] using hpost2
  have hExpEq :
      (do
        let challenges ← sampleChallenges (pSpec (R := R) deg)
        Prod.fst <$> (simulateQ emptyImpl
          (Prover.run (pSpec (R := R) deg) (msg, cont) challenges)).run' σ0) =
      (Prod.fst <$> (mx >>= my)) := by
    simp [mx, my, map_eq_bind_pure_comp, bind_assoc]
  have hFinal :
      Pr[flipPred | do
          let challenges ← sampleChallenges (pSpec (R := R) deg)
          Prod.fst <$> (simulateQ emptyImpl
            (Prover.run (pSpec (R := R) deg) (msg, cont) challenges)).run' σ0] ≤
        (roundSoundnessError (R := R) (deg := deg) : ℝ≥0∞) := by
    rw [hExpEq, probEvent_map]
    have hPair :
        Pr[fun z => flipPred z.1 | mx >>= my] ≤
          (roundSoundnessError (R := R) (deg := deg) : ℝ≥0∞) := by
      rw [← hBadMap]
      exact le_trans hBindLe hcond_le
    simpa [Function.comp] using hPair
  simpa [singleRoundRbrError] using hFinal

/-- Round-by-round soundness of the `n`-round sumcheck verifier in the framework form. -/
theorem generalVerifier_rbrSoundness
    (poly : CMvPolynomial n R) (D : Fin m → R)
    (hTrue : TrueRoundPolyExists (R := R) (n := n) (m := m) (deg := deg) poly D) :
    rbrSoundness
      (impl := emptyImpl)
      (langIn := Sumcheck.inputLang poly D)
      (langOut := outputLang (R := R) (n := n) poly)
      (verifier := generalVerifierAsOracle (R := R) (deg := deg) (n := n) (m := m) D)
      (Inv := fun _ : Unit => True)
      (rbrError := rbrSoundnessError (R := R) (deg := deg) (n := n)) := by
  sorry

/-! This is expected to be obtained from `generalVerifier_rbrSoundness` via the
framework theorem `rbrSoundness_implies_soundness`. -/
/-- Soundness of the general sumcheck verifier in framework form. -/
theorem generalVerifier_soundness
    (poly : CMvPolynomial n R) (D : Fin m → R)
    (hTrue : TrueRoundPolyExists (R := R) (n := n) (m := m) (deg := deg) poly D) :
    Verifier.soundness
      (init := (pure () : ProbComp Unit))
      (impl := emptyImpl)
      (langIn := Sumcheck.inputLang poly D)
      (langOut := outputLang (R := R) (n := n) poly)
      (verifier := generalVerifierAsOracle (R := R) (deg := deg) (n := n) (m := m) D)
      (soundnessError := soundnessError (R := R) (deg := deg) (n := n)) := by
  -- Invoke the generic implication `RBR soundness -> soundness`.
  refine rbrSoundness_implies_soundness (init := (pure () : ProbComp Unit))
    (impl := emptyImpl) (Inv := fun _ : Unit => True) ?_ ?_ ?_
  · intro σ0 hσ0
    trivial
  · intro t σ0 _ z hz
    trivial
  · exact generalVerifier_rbrSoundness (R := R) (n := n) (m := m) (deg := deg) poly D hTrue

end Soundness

end Sumcheck
