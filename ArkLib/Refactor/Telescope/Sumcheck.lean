import ArkLib.Refactor.Telescope.Basic
import ArkLib.Refactor.Telescope.Security.Defs
import ArkLib.Refactor.Sumcheck.Completeness
import ArkLib.Refactor.Sumcheck.General

/-!
# Telescope-Native Sumcheck

This module re-expresses the plain sumcheck protocol over `ProtocolCtx`.

The key design change is that the verifier's challenge prefix is threaded through
the recursive protocol description and prover/verifier definitions, rather than
being packaged into an explicit `RoundState` statement. The live statement at each
node is therefore just the current target value `R`.
-/

open CompPoly CPoly
open ProtocolCtx

namespace Sumcheck.Telescope

variable (R : Type) [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
variable (deg : ℕ)

/-- The empty challenge prefix used to start the telescope-native protocol. -/
def emptyPrefix : Vector R 0 := ⟨#[], rfl⟩

/-- Telescope-native sumcheck context for `remaining` rounds, starting from a fixed
challenge prefix. The branch after each verifier challenge carries the extended
prefix into the recursive call. -/
@[reducible] def ctxFrom :
    (remaining : Nat) → {i : Nat} → Vector R i → ProtocolCtx
  | 0, _, _ => .nil
  | remaining + 1, _, fixed =>
      .P_to_V (CDegreeLE R deg) inferInstance (fun _ =>
        .V_to_P R (fun r => ctxFrom remaining (fixed.push r)))

/-- The full `n`-round telescope-native sumcheck context. -/
@[reducible] def ctx (n : Nat) : ProtocolCtx :=
  ctxFrom (R := R) (deg := deg) n (emptyPrefix (R := R))

section Plain

variable {R deg}
variable {n m : ℕ}

/-- Honest prover for the telescope-native sumcheck protocol from an arbitrary
challenge prefix. At the leaf it returns the true residual target. -/
def proverFrom :
    (remaining : Nat) → {i : Nat} →
    (poly : OStmt R deg n) → (fixed : Vector R i) →
    (D : Fin m → R) → (evalPoints : Vector R (deg + 1)) →
    ProtocolCtx.Prover Id (ctxFrom (R := R) (deg := deg) remaining fixed) (fun _ => R)
  | 0, _, poly, fixed, D, _ =>
      trueTarget (R := R) (n := n) (m := m) (poly := poly) fixed D
  | remaining + 1, _, poly, fixed, D, evalPoints =>
      let roundPoly := computeRoundPoly (R := R) (deg := deg) (n := n) (m := m)
        poly fixed D evalPoints
      let next :
          ProtocolCtx.Prover Id
            (.V_to_P R (fun r =>
              ctxFrom (R := R) (deg := deg) remaining (fixed.push r)))
            (fun _ => R) :=
        fun r => pure (proverFrom remaining poly (fixed.push r) D evalPoints)
      ((⟨roundPoly, (pure next : Id _)⟩) :
          ProtocolCtx.Prover Id
            (.P_to_V (CDegreeLE R deg) inferInstance (fun _ =>
              .V_to_P R (fun r =>
                ctxFrom (R := R) (deg := deg) remaining (fixed.push r))))
            (fun _ => R))

/-- Plain verifier for the telescope-native sumcheck protocol from an arbitrary
challenge prefix. The current statement is just the target value for the remaining
sum; the challenge prefix itself is carried externally by the recursive call. -/
def verifierFrom :
    (remaining : Nat) → {i : Nat} →
    (fixed : Vector R i) → (D : Fin m → R) →
    ProtocolCtx.Verifier Id R
      (ctxFrom (R := R) (deg := deg) remaining fixed) (fun _ => R)
  | 0, _, _, _ => fun target _ => pure target
  | remaining + 1, _, fixed, D => fun target tr =>
      let roundPoly : CDegreeLE R deg := tr.1
      let challenge : R := tr.2.1
      if (Finset.univ : Finset (Fin m)).sum (fun a =>
            CPolynomial.eval (D a) roundPoly.val) = target then
        verifierFrom remaining (fixed.push challenge) D
          (CPolynomial.eval challenge roundPoly.val) tr.2.2
      else
        failure

/-- Top-level honest prover for telescope-native sumcheck. -/
def prover
    (poly : OStmt R deg n) (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    ProtocolCtx.Prover Id (ctx (R := R) (deg := deg) n) (fun _ => R) :=
  proverFrom (R := R) (deg := deg) n poly (emptyPrefix (R := R)) D evalPoints

/-- Top-level verifier for telescope-native sumcheck. -/
def verifier (D : Fin m → R) :
    ProtocolCtx.Verifier Id R (ctx (R := R) (deg := deg) n) (fun _ => R) :=
  verifierFrom (R := R) (deg := deg) n (emptyPrefix (R := R)) D

end Plain

noncomputable section Soundness

open scoped NNReal ENNReal

variable {R deg}
variable {n m : ℕ}
variable [Fintype R] [SampleableType R]

/-- The pointwise sumcheck target invariant at a fixed challenge prefix. -/
def goodTargetFrom
    (poly : OStmt R deg n) (D : Fin m → R) {i : Nat}
    (fixed : Vector R i) (target : R) : Prop :=
  target = trueTarget (R := R) (n := n) (m := m) (poly := poly) fixed D

/-- Per-round challenge error for sumcheck under uniform sampling. -/
noncomputable def roundError : ℝ≥0 :=
  ⟨deg / Fintype.card R, by positivity⟩

/-- Local claims for the telescope-native sumcheck soundness witness.

`some target` means the subtree is still tracking a live target value.
`none` marks a dead branch after a failed local sumcheck identity. -/
private def goodClaimFrom
    (poly : OStmt R deg n) (D : Fin m → R) {i : Nat}
    (fixed : Vector R i) : Option R → Prop
  | some target => goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target
  | none => False

/-- Telescope-native claim tree for a sumcheck subtree rooted at `ctxFrom remaining fixed`.

The claim is the current target value when the branch is still live (`some target`), and
`none` once a local sumcheck identity has already failed. -/
def claimTreeFrom
    (poly : OStmt R deg n) (D : Fin m → R) :
    (remaining : Nat) → {i : Nat} → (fixed : Vector R i) →
    ClaimTree (ctxFrom (R := R) (deg := deg) remaining fixed) (Option R)
  | 0, _, fixed =>
      .nil (goodClaimFrom poly D fixed)
  | remaining + 1, _, fixed =>
      .message
        (goodClaimFrom poly D fixed)
        (fun _ => Option R)
        (fun msg =>
          .challenge
            (goodClaimFrom poly D fixed)
            (roundError (R := R) (deg := deg))
            (fun _ => Option R)
            (fun r => claimTreeFrom poly D remaining (fixed.push r))
            (fun claim r =>
              match claim with
              | none => none
              | some target =>
                  if (Finset.univ : Finset (Fin m)).sum
                      (fun a => CPolynomial.eval (D a) msg.val) = target then
                    some (CPolynomial.eval r msg.val)
                  else
                    none))
        (fun claim _ => claim)

/-- Full claim tree for telescope-native sumcheck. -/
@[reducible] def claimTree
    (poly : OStmt R deg n) (D : Fin m → R) :
    ClaimTree (ctx (R := R) (deg := deg) n) (Option R) :=
  claimTreeFrom poly D n (emptyPrefix (R := R))

omit [SampleableType R] in
@[simp] private theorem claimTreeFrom_good_some
    (poly : OStmt R deg n) (D : Fin m → R)
    (remaining : Nat) {i : Nat} (fixed : Vector R i) (target : R) :
    (claimTreeFrom poly D remaining fixed).good (some target) ↔
      goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target := by
  cases remaining <;> simp [claimTreeFrom, goodClaimFrom, ClaimTree.good]

omit [SampleableType R] in
@[simp] private theorem claimTreeFrom_good_none
    (poly : OStmt R deg n) (D : Fin m → R)
    (remaining : Nat) {i : Nat} (fixed : Vector R i) :
    ¬ (claimTreeFrom poly D remaining fixed).good none := by
  cases remaining <;> simp [claimTreeFrom, goodClaimFrom, ClaimTree.good]

omit [Nontrivial R] [DecidableEq R] in
private lemma prob_eval_eq_le_of_ne
    (p q : CDegreeLE R deg) (hne : p.val.toPoly ≠ q.val.toPoly) :
    Pr[fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val | $ᵗ R]
      ≤ ((deg : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  classical
  letI : DecidableEq R := Classical.decEq R
  have h_eval : ∀ r : R,
      (CPolynomial.eval r p.val = CPolynomial.eval r q.val) ↔
        (p.val.toPoly - q.val.toPoly).eval r = 0 := by
    intro r
    simp [CompPoly.CPolynomial.eval_toPoly, Polynomial.eval_sub, sub_eq_zero]
  let f : Polynomial R := p.val.toPoly - q.val.toPoly
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hne
    simpa [f] using (sub_eq_zero.mp hf)
  have h_deg_f : f.natDegree ≤ deg := by
    have hp : p.val.toPoly.natDegree ≤ deg := by
      simpa [CompPoly.CPolynomial.natDegree_toPoly] using p.property
    have hq : q.val.toPoly.natDegree ≤ deg := by
      simpa [CompPoly.CPolynomial.natDegree_toPoly] using q.property
    exact (Polynomial.natDegree_sub_le_iff_left
      (p := p.val.toPoly) (q := q.val.toPoly) (n := deg) hq).2 hp
  have hcard :
      ((Finset.univ.filter fun r : R =>
          CPolynomial.eval r p.val = CPolynomial.eval r q.val).card : ℝ≥0)
        ≤ deg := by
    have hfilter :
        (Finset.univ.filter fun r : R =>
          CPolynomial.eval r p.val = CPolynomial.eval r q.val) =
        Finset.univ.filter (fun r : R => f.eval r = 0) := by
      ext r
      simp [h_eval, f]
    rw [hfilter]
    have hsub :
        Finset.univ.filter (fun r : R => f.eval r = 0) ⊆ f.roots.toFinset := by
      intro r hr
      have : f.eval r = 0 := by
        simpa using (Finset.mem_filter.mp hr).2
      have : r ∈ f.roots := by
        simpa [Polynomial.mem_roots hf_ne] using this
      simpa using (Multiset.mem_toFinset.2 this)
    have hle1 :
        (Finset.univ.filter (fun r : R => f.eval r = 0)).card ≤ f.roots.toFinset.card :=
      Finset.card_le_card hsub
    have hle2 : (f.roots.toFinset.card : ℕ) ≤ f.roots.card := by
      exact Multiset.toFinset_card_le f.roots
    have hle3 : (f.roots.card : ℕ) ≤ f.natDegree := by
      simpa using (Polynomial.card_roots' f)
    have : (f.roots.toFinset.card : ℕ) ≤ deg := by
      have : f.roots.card ≤ deg := le_trans hle3 h_deg_f
      exact le_trans hle2 this
    exact_mod_cast (le_trans hle1 this)
  have hPr :
      Pr[fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val | $ᵗ R]
        = ((Finset.univ.filter fun r : R =>
            CPolynomial.eval r p.val = CPolynomial.eval r q.val).card : ℝ≥0)
            / (Fintype.card R : ℝ≥0) := by
    rw [probEvent_uniformSample
      (α := R) (p := fun r : R => CPolynomial.eval r p.val = CPolynomial.eval r q.val)]
    simp [div_eq_mul_inv]
  rw [hPr]
  have hcard' :
      ((Finset.univ.filter fun r : R =>
          CPolynomial.eval r p.val = CPolynomial.eval r q.val).card : ℝ≥0∞)
        ≤ (deg : ℝ≥0∞) := by
    exact_mod_cast hcard
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcard' (by positivity)

omit [DecidableEq R] in
private theorem prob_goodTarget_push_le_roundError
    (poly : OStmt R deg n) (D : Fin m → R) {i : Nat}
    (fixed : Vector R i) (target : R) (msg : CDegreeLE R deg)
    (hi : i < n)
    (hBad : ¬ goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target)
    (hSum : (Finset.univ : Finset (Fin m)).sum
        (fun a => CPolynomial.eval (D a) msg.val) = target) :
    Pr[fun r : R =>
        goodTargetFrom (R := R) (n := n) (m := m) poly D
          (fixed.push r) (CPolynomial.eval r msg.val) | $ᵗ R]
      ≤ (roundError (R := R) (deg := deg) : ℝ≥0∞) := by
  classical
  letI : DecidableEq R := Classical.decEq R
  rcases trueRoundPolyExists_of_ostmt (R := R) (n := n) (m := m) poly D i hi fixed with
    ⟨qTrue, hqEval, hqSum⟩
  have hne : msg.val.toPoly ≠ qTrue.val.toPoly := by
    intro hEq
    have hsumEq :
        (Finset.univ : Finset (Fin m)).sum (fun a => CPolynomial.eval (D a) msg.val) =
          trueTarget (R := R) (n := n) (m := m) (poly := poly) fixed D := by
      calc
        (Finset.univ : Finset (Fin m)).sum (fun a => CPolynomial.eval (D a) msg.val)
            = (Finset.univ : Finset (Fin m)).sum (fun a =>
                CPolynomial.eval (D a) qTrue.val) := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  simp [CompPoly.CPolynomial.eval_toPoly, hEq]
        _ = trueTarget (R := R) (n := n) (m := m) (poly := poly) fixed D := hqSum
    apply hBad
    exact hSum.symm.trans hsumEq
  have hEventLe :
      Pr[fun r : R =>
          goodTargetFrom (R := R) (n := n) (m := m) poly D
            (fixed.push r) (CPolynomial.eval r msg.val) | $ᵗ R]
        ≤
      Pr[fun r : R => CPolynomial.eval r msg.val = CPolynomial.eval r qTrue.val | $ᵗ R] := by
    refine probEvent_mono ?_
    intro r _ hGood
    dsimp [goodTargetFrom] at hGood
    calc
      CPolynomial.eval r msg.val
          = trueTarget (R := R) (n := n) (m := m) (poly := poly)
              (fixed.push r) D := hGood
      _ = trueRoundValue (R := R) (n := n) (m := m) (poly := poly) fixed D r :=
          trueTarget_push_eq_trueRoundValue (R := R) (n := n) (m := m) poly D i fixed r
      _ = CPolynomial.eval r qTrue.val := (hqEval r).symm
  have hSz :
      Pr[fun r : R => CPolynomial.eval r msg.val = CPolynomial.eval r qTrue.val | $ᵗ R]
        ≤ ((deg : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0∞) :=
    prob_eval_eq_le_of_ne (R := R) (deg := deg) msg qTrue hne
  have hRoundVal :
      (roundError (R := R) (deg := deg) : ℝ≥0∞) =
        ((deg : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)) := by
    have hcard_ne : (Fintype.card R : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := R))
    calc
      (roundError (R := R) (deg := deg) : ℝ≥0∞)
          = (((deg : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
              rfl
      _ = ((deg : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)) := by
            exact ENNReal.coe_div hcard_ne
  exact le_trans hEventLe (hRoundVal.symm ▸ hSz)

/-- Structural soundness of the telescope-native sumcheck claim tree. -/
theorem claimTreeFrom_isSound
    (poly : OStmt R deg n) (D : Fin m → R) :
    (remaining : Nat) → {i : Nat} →
    (fixed : Vector R i) →
    i + remaining = n →
    (sample : (T : Type) → ProbComp T) →
    sample R = ($ᵗR) →
    (claimTreeFrom poly D remaining fixed).IsSound sample
  | 0, _, fixed, _hLen, sample, _hSampleR => by
      simp [claimTreeFrom, ClaimTree.IsSound]
  | remaining + 1, i, fixed, hLen, sample, hSampleR => by
      refine ⟨?_, ?_⟩
      · intro claim hBad msg
        simpa [claimTreeFrom, ClaimTree.good] using hBad
      · intro msg
        refine ⟨?_, ?_⟩
        · intro claim hBad
          rw [hSampleR]
          cases claim with
          | none =>
              change
                Pr[fun r : R => (claimTreeFrom poly D remaining (fixed.push r)).good none | $ᵗ R] ≤
                  (roundError (R := R) (deg := deg) : ℝ≥0∞)
              have hDead :
                  (fun r : R =>
                    (claimTreeFrom poly D remaining (fixed.push r)).good none) =
                    fun _ : R => False := by
                funext r
                apply propext
                constructor
                · exact claimTreeFrom_good_none
                    (poly := poly) (D := D)
                    (remaining := remaining) (fixed := fixed.push r)
                · intro hFalse
                  exact False.elim hFalse
              rw [hDead]
              simp [roundError]
          | some target =>
              by_cases hSum : (Finset.univ : Finset (Fin m)).sum
                  (fun a => CPolynomial.eval (D a) msg.val) = target
              · have hi : i < n := by
                  rw [← hLen]
                  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
                have hBadTarget :
                    ¬ goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target := by
                  simpa [goodClaimFrom] using hBad
                have hEvent :
                    (fun r : R =>
                      (claimTreeFrom poly D remaining (fixed.push r)).good
                        (some (CPolynomial.eval r msg.val))) =
                      fun r : R =>
                        goodTargetFrom (R := R) (n := n) (m := m) poly D
                          (fixed.push r) (CPolynomial.eval r msg.val) := by
                  funext r
                  exact propext
                    (claimTreeFrom_good_some
                      (poly := poly) (D := D)
                      (remaining := remaining) (fixed := fixed.push r)
                      (target := CPolynomial.eval r msg.val))
                have hProb :
                    Pr[fun r : R =>
                        (claimTreeFrom poly D remaining (fixed.push r)).good
                          (some (CPolynomial.eval r msg.val)) | $ᵗ R] ≤
                      (roundError (R := R) (deg := deg) : ℝ≥0∞) := by
                  rw [hEvent]
                  exact prob_goodTarget_push_le_roundError
                    (R := R) (deg := deg) (n := n) (m := m)
                    poly D fixed target msg hi hBadTarget hSum
                simpa [hSum] using hProb
              · have hDead :
                    (fun r : R =>
                      (claimTreeFrom poly D remaining (fixed.push r)).good none) =
                      fun _ : R => False := by
                  funext r
                  apply propext
                  constructor
                  · exact claimTreeFrom_good_none
                      (poly := poly) (D := D)
                      (remaining := remaining) (fixed := fixed.push r)
                  · intro hFalse
                    exact False.elim hFalse
                have hProb :
                    Pr[fun r : R =>
                        (claimTreeFrom poly D remaining (fixed.push r)).good none | $ᵗ R] ≤
                      (roundError (R := R) (deg := deg) : ℝ≥0∞) := by
                  rw [hDead]
                  simp [roundError]
                simp [hSum]
        · intro r
          have hLen' : i + 1 + remaining = n := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hLen
          simpa [claimTreeFrom] using
            claimTreeFrom_isSound (poly := poly) (D := D)
              remaining (i := i + 1) (fixed := fixed.push r) hLen' sample hSampleR

/-- Structural soundness of the full telescope-native sumcheck claim tree. -/
theorem claimTree_isSound
    (poly : OStmt R deg n) (D : Fin m → R)
    (sample : (T : Type) → ProbComp T)
    (hSampleR : sample R = ($ᵗR)) :
    (claimTree poly D).IsSound sample := by
  simpa [claimTree] using
    claimTreeFrom_isSound (poly := poly) (D := D)
      n (fixed := emptyPrefix (R := R)) (by simp) sample hSampleR

/-- Accepted outputs for the open telescope-native sumcheck verifier: the returned
residual target must satisfy the terminal claim predicate for the full transcript. -/
def acceptsFrom
    (poly : OStmt R deg n) (D : Fin m → R) :
    (remaining : Nat) → {i : Nat} → (fixed : Vector R i) →
    (tr : Transcript (ctxFrom (R := R) (deg := deg) remaining fixed)) → Set R
  | 0, _, fixed, _ =>
      {s | goodTargetFrom (R := R) (n := n) (m := m) poly D fixed s}
  | remaining + 1, _, fixed, ⟨_, ⟨r, trRest⟩⟩ =>
      acceptsFrom poly D remaining (fixed.push r) trRest

/-- Accepted outputs for the full telescope-native sumcheck verifier. -/
@[reducible] def accepts
    (poly : OStmt R deg n) (D : Fin m → R) :
    (tr : Transcript (ctx (R := R) (deg := deg) n)) → Set R :=
  acceptsFrom (poly := poly) (D := D) n (emptyPrefix (R := R))

omit [SampleableType R] in
private theorem verifierFrom_accepts_terminal
    (poly : OStmt R deg n) (D : Fin m → R) :
    (remaining : Nat) → {i : Nat} → (fixed : Vector R i) → (target : R) →
    ∀ {tr s},
      (verifierFrom remaining fixed D target tr).run = some s →
      s ∈ acceptsFrom (poly := poly) (D := D) remaining fixed tr →
      (claimTreeFrom poly D remaining fixed).terminalGood tr
        ((claimTreeFrom poly D remaining fixed).follow tr (some target))
  | 0, _, fixed, target, tr, s, hRun, hMem => by
      cases hRun
      simpa [verifierFrom, acceptsFrom, claimTreeFrom, goodClaimFrom] using hMem
  | remaining + 1, _, fixed, target, ⟨msg, ⟨r, trRest⟩⟩, s, hRun, hMem => by
      by_cases hSum : (Finset.univ : Finset (Fin m)).sum
          (fun a => CPolynomial.eval (D a) msg.val) = target
      · have hRest :
            (verifierFrom remaining (fixed.push r) D (CPolynomial.eval r msg.val) trRest).run =
              some s := by
            simpa [verifierFrom, hSum] using hRun
        have hTail :
            (claimTreeFrom poly D remaining (fixed.push r)).terminalGood trRest
              ((claimTreeFrom poly D remaining (fixed.push r)).follow trRest
                (some (CPolynomial.eval r msg.val))) :=
          verifierFrom_accepts_terminal (poly := poly) (D := D)
            remaining (fixed := fixed.push r) (target := CPolynomial.eval r msg.val)
            hRest hMem
        change
          (claimTreeFrom poly D remaining (fixed.push r)).terminalGood trRest
            ((claimTreeFrom poly D remaining (fixed.push r)).follow trRest
              (if hSum' : (Finset.univ : Finset (Fin m)).sum
                  (fun a => CPolynomial.eval (D a) msg.val) = target then
                some (CPolynomial.eval r msg.val)
              else
                none))
        simpa [hSum] using hTail
      · simp [verifierFrom, hSum] at hRun

/-- Soundness of the open telescope-native sumcheck verifier from an arbitrary challenge
prefix. The statement is the claimed target value, and accepted outputs are exactly the
residual targets that satisfy the terminal claim predicate. -/
theorem verifierFrom_soundness
    (poly : OStmt R deg n) (D : Fin m → R) :
    (remaining : Nat) → {i : Nat} → (fixed : Vector R i) →
    i + remaining = n →
    (sample : (T : Type) → ProbComp T) →
    sample R = ($ᵗR) →
    ProtocolCtx.Verifier.soundness sample
      {target | goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target}
      (fun _ => ctxFrom (R := R) (deg := deg) remaining fixed)
      (fun _ _ => R)
      (fun _ tr => acceptsFrom (poly := poly) (D := D) remaining fixed tr)
      (fun target tr => verifierFrom remaining fixed D target tr)
      (fun _ => (claimTreeFrom poly D remaining fixed).maxPathError)
  | remaining, _, fixed, hLen, sample, hSampleR => by
      refine ProtocolCtx.Verifier.soundness_of_isSound sample
        {target | goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target}
        (fun _ => ctxFrom (R := R) (deg := deg) remaining fixed)
        (fun _ => Option R)
        (fun _ => claimTreeFrom poly D remaining fixed)
        (fun target => some target)
        (fun _ =>
          claimTreeFrom_isSound (poly := poly) (D := D)
            remaining (fixed := fixed) hLen sample hSampleR)
        (fun _ _ => R)
        (fun _ tr => acceptsFrom (poly := poly) (D := D) remaining fixed tr)
        (fun target tr => verifierFrom remaining fixed D target tr)
        ?_ ?_
      · intro target hNotIn
        simpa using
          (show ¬ goodTargetFrom (R := R) (n := n) (m := m) poly D fixed target from
            hNotIn)
      · intro target tr s hRun hMem
        exact verifierFrom_accepts_terminal
          (poly := poly) (D := D)
          remaining (fixed := fixed) (target := target) hRun hMem

/-- Soundness of the full telescope-native sumcheck verifier. -/
theorem verifier_soundness
    (poly : OStmt R deg n) (D : Fin m → R)
    (sample : (T : Type) → ProbComp T)
    (hSampleR : sample R = ($ᵗR)) :
    ProtocolCtx.Verifier.soundness sample
      {target | goodTargetFrom (R := R) (n := n) (m := m)
        poly D (emptyPrefix (R := R)) target}
      (fun _ => ctx (R := R) (deg := deg) n)
      (fun _ _ => R)
      (fun _ tr => accepts (poly := poly) (D := D) tr)
      (fun target tr => verifier (R := R) (deg := deg) (n := n) (m := m) D target tr)
      (fun _ => (claimTree poly D).maxPathError) := by
  intro AdversaryOutput prover statement hNotIn
  have hResult :=
    (verifierFrom_soundness (poly := poly) (D := D)
      n (fixed := emptyPrefix (R := R)) (by simp) sample hSampleR)
      (prover := prover) (statement := statement)
    (by simpa [Set.mem_setOf_eq] using hNotIn)
  simpa [ctx, verifier, accepts, claimTree] using hResult

end Soundness

end Sumcheck.Telescope
