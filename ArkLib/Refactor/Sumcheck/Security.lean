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
