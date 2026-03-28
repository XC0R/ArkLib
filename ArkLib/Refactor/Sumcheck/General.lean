/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.Defs
import ArkLib.Refactor.Sumcheck.SingleRound
import ArkLib.Refactor.Sumcheck.PartialEval
import ArkLib.Refactor.Sumcheck.Completeness

/-!
# Multi-Round Sumcheck Protocol

Composes `n` single rounds of the sumcheck protocol into the full multi-round protocol.

- `generalPSpec` — the `n`-round protocol spec (replicate `pSpec` `n` times)
- `generalVerifier` — composed `n`-round plain verifier via `Verifier.compNth`
- `generalOracleVerifier` — composed `n`-round oracle verifier via `OracleVerifier.compNth`
-/

open CompPoly CPoly ProtocolSpec OracleComp OracleSpec

namespace Sumcheck

variable (R : Type) [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
variable (deg : ℕ)

/-! ## Multi-round protocol spec -/

@[reducible] def generalPSpec (n : ℕ) : ProtocolSpec :=
  ProtocolSpec.replicate n (pSpec R deg)

/-! ## Multi-round plain verifier -/

variable {R} {deg}
variable {n m : ℕ}

def initState (target : R) : RoundState (R := R) :=
  { i := 0, challenges := ⟨#[], rfl⟩, target := target }

/-- The single-round verifier, lifted to act on the state statement type `RoundState`. -/
def roundVerifierState (D : Fin m → R) :
    Verifier Id (RoundState (R := R)) (RoundState (R := R)) (pSpec (R := R) deg) :=
  fun st tr => do
    let p : CDegreeLE R deg := tr.head
    let chal : R := (tr.tail).head
    guard ((Finset.univ : Finset (Fin m)).sum (fun j => CPolynomial.eval (D j) p.val) = st.target)
    pure { i := st.i + 1
           challenges := st.challenges.push chal
           target := CPolynomial.eval chal p.val }

/-- Multi-round sumcheck verifier (as a state transformer).

Runs `n` single rounds and returns the final `RoundState`. The final check against the original
multivariate polynomial is deferred to the output language/relation. -/
def generalVerifier (D : Fin m → R) :
    Verifier Id R (RoundState (R := R)) (generalPSpec R deg n) :=
  fun target tr => do
    let st0 := initState (R := R) target
    (Verifier.compNth n (roundVerifierState (R := R) (deg := deg) D)) st0 tr

/-! ## Multi-round oracle verifier -/

section OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- Single-round oracle verifier that outputs `R` for `compNth` composition.
Queries the round polynomial at domain points, checks the sum, and returns the new target. -/
def roundOracleVerifier (D : Fin m → R) :
    OracleVerifier oSpec
      R (fun (_ : Unit) => OStmt R deg n)
      R (fun (_ : Unit) => OStmt R deg n)
      (pSpec R deg) :=
  OracleVerifier.keepInputOracle (oSpec := oSpec)
    (StmtIn := R) (StmtOut := R)
    (OStmt := fun (_ : Unit) => OStmt R deg n) (pSpec := pSpec R deg)
    (fun target challenges => do
      let result ← (oracleVerifier (n := n) (m := m) (deg := deg) (ι := ι) (oSpec := oSpec)
        D).verify target challenges
      pure result.target)

def generalOracleVerifier (D : Fin m → R) :
    OracleVerifier oSpec
      R (fun (_ : Unit) => OStmt R deg n)
      R (fun (_ : Unit) => OStmt R deg n)
      (generalPSpec R deg n) :=
  OracleVerifier.compNth n (roundOracleVerifier D)

end OracleVerifier

section OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}

/-- State-threaded oracle verifier for one sumcheck round.

This is the oracle analogue of `roundVerifierState`: it checks the current target,
consumes one challenge, and appends that challenge to the accumulated round state
while leaving the input polynomial oracle unchanged. -/
def roundOracleVerifierState (D : Fin m → R) :
    OracleVerifier oSpec
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n)
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n)
      (pSpec R deg) :=
  OracleVerifier.keepInputOracle (oSpec := oSpec)
    (StmtIn := RoundState (R := R)) (StmtOut := RoundState (R := R))
    (OStmt := fun (_ : Unit) => OStmt R deg n) (pSpec := pSpec R deg)
    (fun st challenges => do
      let result ← (oracleVerifier (R := R) (deg := deg) (n := n) (m := m) (oSpec := oSpec)
        D).verify st.target challenges
      pure { i := st.i + 1
             challenges := st.challenges.push result.challenge
             target := result.target })

/-- Compose `n` state-threaded oracle verifier rounds. -/
def generalOracleVerifierState (D : Fin m → R) :
    OracleVerifier oSpec
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n)
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n)
      (generalPSpec R deg n) :=
  OracleVerifier.compNth n (roundOracleVerifierState (R := R) (deg := deg) (n := n)
    (m := m) (oSpec := oSpec) D)

/-- Stateful one-round oracle reduction for sumcheck. The prover computes the round
polynomial from the current accumulated challenges and preserves the multivariate
polynomial oracle as output oracle data. -/
def roundOracleReductionState
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    OracleReduction oSpec
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n) Unit
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n) Unit
      (pSpec R deg) where
  prover := fun ⟨⟨st, oStmtData⟩, ()⟩ => do
    let roundPoly := computeRoundPoly (R := R) (deg := deg) (n := n) (m := m) (i := st.i)
      (oStmtData ()) st.challenges D evalPoints
    pure (roundPoly, pure (fun chal =>
      pure (({
          i := st.i + 1
          challenges := st.challenges.push chal
          target := CPolynomial.eval chal roundPoly.val
        }, oStmtData), ())))
  verifier := roundOracleVerifierState (R := R) (deg := deg) (n := n) (m := m)
    (oSpec := oSpec) D

/-- Compose `n` stateful oracle rounds into the full sumcheck oracle reduction over
`RoundState`. -/
def generalOracleReductionState
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    OracleReduction oSpec
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n) Unit
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n) Unit
      (generalPSpec R deg n) :=
  OracleReduction.compNth n (roundOracleReductionState (R := R) (deg := deg) (n := n)
    (m := m) (oSpec := oSpec) D evalPoints)

/-- Full oracle reduction for multi-round sumcheck.

It initializes the `RoundState` from the claimed target sum and then runs the
stateful `n`-round oracle reduction. -/
def generalOracleReduction
    (D : Fin m → R) (evalPoints : Vector R (deg + 1)) :
    OracleReduction oSpec
      R (fun (_ : Unit) => OStmt R deg n) Unit
      (RoundState (R := R)) (fun (_ : Unit) => OStmt R deg n) Unit
      (generalPSpec R deg n) where
  prover := fun ⟨⟨target, oStmtData⟩, ()⟩ =>
    (generalOracleReductionState (R := R) (deg := deg) (n := n) (m := m)
      (oSpec := oSpec) D evalPoints).prover
      ((initState (R := R) target, oStmtData), ())
  verifier := OracleVerifier.keepInputOracle (oSpec := oSpec)
    (StmtIn := R) (StmtOut := RoundState (R := R))
    (OStmt := fun (_ : Unit) => OStmt R deg n) (pSpec := generalPSpec R deg n)
    (fun target challenges =>
      (generalOracleVerifierState (R := R) (deg := deg) (n := n) (m := m)
        (oSpec := oSpec) D).verify
        (initState (R := R) target) challenges)

end OracleReduction

/-! ## Multi-round prover

The multi-round prover accumulates challenges across rounds. Each round computes
the round polynomial using all previously received challenges, sends it, receives a
new challenge, and continues. Built by structural recursion on the remaining number
of rounds `k`, with `prevChallenges` tracking all challenges seen so far. -/

def roundProverStep
    (backend : ∀ i : ℕ, Vector R i → CDegreeLE R deg) :
    (RoundState (R := R) × Unit) → Id (Prover Id (RoundState (R := R) × Unit) (pSpec (R := R) deg))
  | (st, ()) =>
      let roundPoly := backend st.i st.challenges
      pure (roundPoly, pure (fun chal =>
        pure ({ i := st.i + 1
                challenges := st.challenges.push chal
                target := CPolynomial.eval chal roundPoly.val }, ())))

/-! ## Multi-round reduction -/

def generalReduction
    (poly : OStmt R deg n) (D : Fin m → R) (evalPoints : Vector R (deg + 1))
    (backend : ∀ i : ℕ, Vector R i → CDegreeLE R deg :=
      fun i prev => computeRoundPoly (R := R) (deg := deg) (n := n) (m := m) (i := i)
        poly prev D evalPoints) :
    Reduction Id R Unit (RoundState (R := R)) Unit (generalPSpec R deg n) where
  prover := fun (target, ()) => do
    let st0 : RoundState (R := R) := initState (R := R) target
    let out0 : RoundState (R := R) × Unit := (st0, ())
    Prover.iterate (m := Id) (S := RoundState (R := R) × Unit)
      (pSpec (R := R) deg) n
      (roundProverStep (R := R) (deg := deg) backend)
      out0
  verifier := generalVerifier (R := R) (deg := deg) (n := n) (m := m) D

/-! ## Symbolic prover via `HonestProver.compNth`

An alternate prover that directly executes the sumcheck equation using partial evaluation
and domain summation, composed via `Reduction.compNth`. The prover threads a `SymbolicPoly`
witness that tracks the partially-evaluated polynomial together with its surviving
individual-degree bound. -/

/-- Single-round honest prover using symbolic partial evaluation.
Dependent pattern matching on `k + 1` gives `poly : CMvPolynomial (k + 1) R` with zero casts.
Each round:
1. Computes the round polynomial via `roundPoly` (variable 0 free, rest summed over D)
2. After receiving a challenge, reduces via `partialEvalFirst` -/
def symbolicRoundHonestProver (D : Fin m → R) :
    HonestProver Id (RoundState (R := R)) (SymbolicPoly (R := R) deg)
      (RoundState (R := R)) (SymbolicPoly (R := R) deg) (pSpec (R := R) deg) :=
  fun (st, sp) =>
    match sp with
    | ⟨k + 1, ⟨poly, hDegree⟩⟩ =>
      let rp := CMvPolynomial.roundPoly D k poly
      pure (⟨rp, CMvPolynomial.roundPoly_natDegree_le D poly
        (fun mono hmono => by simpa using hDegree 0 mono hmono)⟩, pure (fun chal =>
        pure ({ i := st.i + 1
                challenges := st.challenges.push chal
                target := CPolynomial.eval chal rp },
              ⟨k, ⟨CMvPolynomial.partialEvalFirst chal poly,
                CMvPolynomial.partialEvalFirst_individualDegreeLE chal poly hDegree⟩⟩)))
    | ⟨0, _⟩ =>
      pure ((⟨(0 : CPolynomial R), CMvPolynomial.CPolynomial.natDegree_zero_le deg⟩
        : CDegreeLE R deg),
        pure (fun _ => pure (st, sp)))

/-- Single-round reduction pairing the symbolic prover with `roundVerifierState`. -/
def symbolicRoundReduction (D : Fin m → R) :
    Reduction Id (RoundState (R := R)) (SymbolicPoly (R := R) deg)
      (RoundState (R := R)) (SymbolicPoly (R := R) deg) (pSpec (R := R) deg) where
  prover := symbolicRoundHonestProver D
  verifier := roundVerifierState D

/-- Multi-round symbolic reduction via `Reduction.compNth`. -/
def symbolicReductionState (D : Fin m → R) :
    Reduction Id (RoundState (R := R)) (SymbolicPoly (R := R) deg)
      (RoundState (R := R)) (SymbolicPoly (R := R) deg) (generalPSpec R deg n) :=
  Reduction.compNth n (symbolicRoundReduction D)

/-- Full symbolic reduction from `R` (target) to `RoundState`.
Wraps `initState` on input and discards the `SymbolicPoly` witness on output. -/
def symbolicGeneralReduction (poly : OStmt R deg n) (D : Fin m → R) :
    Reduction Id R Unit (RoundState (R := R)) Unit (generalPSpec R deg n) where
  prover := fun (target, ()) => do
    let p ← (symbolicReductionState (deg := deg) D).prover
      (initState (R := R) target, ⟨n, poly⟩)
    pure (Prover.mapOutput (fun (st, _) => (st, ())) _ p)
  verifier := generalVerifier (R := R) (deg := deg) (n := n) (m := m) D

/-! ## Language definitions for soundness -/

omit [Nontrivial R] [DecidableEq R] in
/-- Output language for the reduced claim after `n` rounds.

Since sumcheck is modeled as a **reduction**, the verifier outputs the random point
`r` (the sampled challenges) together with the final value `v`. The remaining
obligation is the evaluation relation `poly(r) = v`. -/
def outputLang (poly : OStmt R deg n) : Set (RoundState (R := R)) :=
  { st | ∃ h : st.i = n,
      CMvPolynomial.eval (fun i : Fin n => (by
        cases h
        simpa using st.challenges.get i)) poly.val = st.target }

omit [Nontrivial R] [DecidableEq R] in
/-- State-consistency language for a single sumcheck round step. -/
def roundStateLang (poly : OStmt R deg n) (D : Fin m → R) :
    Set (RoundState (R := R)) :=
  { st | st.i ≤ n ∧
      st.target = trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := st.i)
        st.challenges D }

omit [Nontrivial R] [DecidableEq R] in
/-- Input-language membership is equivalent to round-state consistency at initialization. -/
theorem inputLang_iff_initState_mem_roundStateLang
    (poly : OStmt R deg n) (D : Fin m → R) (target : R) :
    target ∈ Sumcheck.inputLang poly D ↔
      initState (R := R) target ∈ roundStateLang (R := R) (n := n) (m := m) poly D := by
  constructor
  · intro hIn
    refine ⟨Nat.zero_le _, ?_⟩
    rcases hIn with rfl
    exact (trueTarget_at_zero poly D _).symm
  · intro hState
    rcases hState with ⟨_, hEq⟩
    change target = (Finset.univ : Finset (Fin n → Fin m)).sum (fun z =>
      CMvPolynomial.eval (D ∘ z) poly.val)
    calc
      target
          = trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := 0)
              (initState (R := R) (target := target)).challenges D := hEq
      _ = (Finset.univ : Finset (Fin n → Fin m)).sum (fun z =>
            CMvPolynomial.eval (D ∘ z) poly.val) := trueTarget_at_zero poly D _

omit [Nontrivial R] [DecidableEq R] in
/-- Any output-language state satisfies the round-state consistency language. -/
theorem outputLang_subset_roundStateLang
    (poly : OStmt R deg n) (D : Fin m → R) :
    outputLang (R := R) (n := n) poly ⊆ roundStateLang (R := R) (n := n) (m := m) poly D := by
  intro st hOut
  rcases hOut with ⟨rfl, hEval⟩
  refine ⟨le_refl _, ?_⟩
  have hEval' :
      CMvPolynomial.eval (fun j : Fin st.i => st.challenges.get j) poly.val = st.target := by
    simpa using hEval
  have hTrue :
      trueTarget (R := R) (n := st.i) (m := m) (poly := poly) (i := st.i) st.challenges D =
        CMvPolynomial.eval (fun j : Fin st.i => st.challenges.get j) poly.val :=
    trueTarget_at_n (R := R) (n := st.i) (m := m) poly D st.challenges
  calc
    st.target = CMvPolynomial.eval (fun j : Fin st.i => st.challenges.get j) poly.val := by
      simpa using hEval'.symm
    _ = trueTarget (R := R) (n := st.i) (m := m) (poly := poly) (i := st.i) st.challenges D := by
      simpa using hTrue.symm

/-! ## Existence of true round polynomial -/

omit [Nontrivial R] [DecidableEq R] in
/-- Existence of a degree-`deg` polynomial realizing the true round function. -/
def TrueRoundPolyExists (poly : OStmt R deg n) (D : Fin m → R) : Prop :=
  ∀ (i : ℕ) (_hi : i < n) (fixed : Vector R i),
    ∃ q : CDegreeLE R deg,
      (∀ t : R,
        CPolynomial.eval t q.val =
          trueRoundValue (R := R) (n := n) (m := m) (poly := poly) (i := i) fixed D t)
      ∧
      ((Finset.univ : Finset (Fin m)).sum (fun a =>
          CPolynomial.eval (D a) q.val) =
        trueTarget (R := R) (n := n) (m := m) (poly := poly) (i := i) fixed D)

omit [Nontrivial R] [DecidableEq R] in
theorem trueRoundPolyExists_of_ostmt
    (poly : OStmt R deg n) (D : Fin m → R) :
    TrueRoundPolyExists (R := R) (n := n) (m := m) poly D := by
  intro i hi fixed
  let k : ℕ := n - i - 1
  have hk : k + 1 + i = n := by
    dsimp [k]
    omega
  let polyCast : OStmt R deg (k + 1 + i) := hk.symm ▸ poly
  have hk_succ : k + 1 + i - i = k + 1 := by
    omega
  have hk_tail : k + 1 + i - (i + 1) = k := by
    omega
  let castTail (z : Fin k → Fin m) : Fin (k + 1 + i - (i + 1)) → Fin m :=
    fun j => z ⟨j.1, by simpa [hk_tail] using j.2⟩
  let castHead (z : Fin (k + 1) → Fin m) : Fin (k + 1 + i - i) → Fin m :=
    fun j => z ⟨j.1, by simpa [hk_succ] using j.2⟩
  have hpolyCastEq : HEq polyCast poly := by
    simp [polyCast]
  have hTrueRoundEq :
      ∀ t : R,
        trueRoundValue (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
          (i := i) fixed D t =
        trueRoundValue (R := R) (n := n) (m := m) (poly := poly)
          (i := i) fixed D t := by
    intro t
    let G : ∀ n : ℕ, OStmt R deg n → R :=
      fun n q =>
        trueRoundValue (R := R) (n := n) (m := m) (poly := q) (i := i) fixed D t
    simpa [G] using congr_heq (congr_arg_heq G hk) hpolyCastEq
  have hTrueTargetEq :
      trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
        (i := i) fixed D =
      trueTarget (R := R) (n := n) (m := m) (poly := poly)
        (i := i) fixed D := by
    let G : ∀ n : ℕ, OStmt R deg n → R :=
      fun n q =>
        trueTarget (R := R) (n := n) (m := m) (poly := q) (i := i) fixed D
    simpa [G] using congr_heq (congr_arg_heq G hk) hpolyCastEq
  let eTail : (Fin k → Fin m) ≃ (Fin (k + 1 + i - (i + 1)) → Fin m) := {
    toFun := castTail
    invFun := fun z j => z ⟨j.1, by simp [hk_tail]⟩
    left_inv := by
      intro z
      funext j
      simp [castTail]
    right_inv := by
      intro z
      funext j
      simp [castTail]
  }
  let eHead : (Fin (k + 1) → Fin m) ≃ (Fin (k + 1 + i - i) → Fin m) := {
    toFun := castHead
    invFun := fun z j => z ⟨j.1, by simpa [hk_succ] using j.2⟩
    left_inv := by
      intro z
      funext j
      simp [castHead]
    right_inv := by
      intro z
      funext j
      simp [castHead]
  }
  suffices
      ∃ q : CDegreeLE R deg,
        (∀ t : R,
          CPolynomial.eval t q.val =
            trueRoundValue (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
              (i := i) fixed D t)
        ∧
        ((Finset.univ : Finset (Fin m)).sum (fun a =>
            CPolynomial.eval (D a) q.val) =
          trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
            (i := i) fixed D) from by
    rcases this with ⟨q, hEval, hSum⟩
    refine ⟨q, ?_, ?_⟩
    · intro t
      calc
        CPolynomial.eval t q.val
            = trueRoundValue (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
                (i := i) fixed D t := hEval t
        _ = trueRoundValue (R := R) (n := n) (m := m) (poly := poly)
              (i := i) fixed D t := hTrueRoundEq t
    · calc
        (Finset.univ : Finset (Fin m)).sum (fun a => CPolynomial.eval (D a) q.val)
            = trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
                (i := i) fixed D := hSum
        _ = trueTarget (R := R) (n := n) (m := m) (poly := poly)
              (i := i) fixed D := hTrueTargetEq
  let pResid : CMvPolynomial (k + 1) R :=
    CMvPolynomial.partialEvalPrefix fixed polyCast.val
  have hPrefix :
      ∀ (t : R) (z : Fin k → Fin m),
        CMvPolynomial.prefixPoint fixed (Fin.cons t (D ∘ z)) =
          evalPoint (R := R) (n := k + 1 + i) (m := m) (fixed := fixed.push t) D
            (castTail z) := by
    intro t z
    funext x
    by_cases hx : x.1 < i
    · have hx' : x.1 < i + 1 := by omega
      simp [CMvPolynomial.prefixPoint_spec, evalPoint, hx, hx',
        Vector.get_eq_getElem, Vector.getElem_push_lt hx]
    · by_cases hEq : x.1 = i
      · simp [CMvPolynomial.prefixPoint_spec, evalPoint, hEq]
      · have hlt : ¬ x.1 < i + 1 := by omega
        have hidxLt : x.1 - i - 1 < k := by omega
        have hidx :
            (⟨x.1 - i, by
                have hval : x.1 - i = (x.1 - i - 1) + 1 := by omega
                rw [hval]
                exact Nat.succ_lt_succ hidxLt⟩ : Fin (k + 1)) =
              (⟨x.1 - i - 1, hidxLt⟩ : Fin k).succ := by
          have hval : x.1 - i = (x.1 - i - 1) + 1 := by
            omega
          apply Fin.ext
          change x.1 - i = x.1 - i - 1 + 1
          exact hval
        have hsub : x.1 - (i + 1) = x.1 - i - 1 := by omega
        have hrem : x.1 - (i + 1) < k + 1 + i - (i + 1) := by
          simpa [hk_tail, hsub] using hidxLt
        let v : Fin (k + 1) → R := Fin.cons t (D ∘ z)
        calc
          CMvPolynomial.prefixPoint fixed v x
              = v ⟨x.1 - i, by
                  have hval : x.1 - i = (x.1 - i - 1) + 1 := by omega
                  rw [hval]
                  exact Nat.succ_lt_succ hidxLt⟩ := by
                    simpa [v, hx] using
                      (CMvPolynomial.prefixPoint_spec fixed v x)
          _ = v ((⟨x.1 - i - 1, hidxLt⟩ : Fin k).succ) := by
                  simpa using congrArg v hidx
          _ = D (z ⟨x.1 - i - 1, hidxLt⟩) := by
                  rw [show v = Fin.cons t (D ∘ z) by rfl, Fin.cons_succ]
                  simp [Function.comp]
          _ = D (castTail z ⟨x.1 - (i + 1),
                by simpa [hk_tail, hsub] using hidxLt⟩) := by
                  simp [castTail, hsub]
          _ = evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed.push t) D (castTail z) x := by
                  change D (castTail z ⟨x.1 - (i + 1),
                    by simpa [hk_tail, hsub] using hidxLt⟩) =
                    (if h : x.1 < i + 1 then (fixed.push t)[x.1]
                     else
                       let rem := x.1 - (i + 1)
                       if h' : rem < k + 1 + i - (i + 1) then
                         D (castTail z ⟨rem, h'⟩) else 0)
                  have hkNotLe : ¬ k ≤ x.1 - i - 1 := not_le_of_gt hidxLt
                  simp [hlt, castTail, hsub, hk_tail, hkNotLe]
  have hResidDeg :
      CMvPolynomial.IndividualDegreeLE (R := R) deg pResid := by
    dsimp [pResid]
    exact CMvPolynomial.partialEvalPrefix_individualDegreeLE
      (deg := deg) fixed polyCast.val polyCast.property
  have hqdeg : (CMvPolynomial.roundPoly D k pResid).natDegree ≤ deg := by
    apply CMvPolynomial.roundPoly_natDegree_le (deg := deg) (D := D) (p := pResid)
    intro mono hmono
    exact hResidDeg 0 mono hmono
  let q : CDegreeLE R deg := ⟨CMvPolynomial.roundPoly D k pResid, hqdeg⟩
  have hqEval : ∀ t : R,
      CPolynomial.eval t q.val =
        trueRoundValue (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
          (i := i) fixed D t := by
    intro t
    calc
      CPolynomial.eval t q.val
          = CPolynomial.eval t (CMvPolynomial.roundPoly D k pResid) := by
              rfl
      _ = (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
            pResid.eval (Fin.cons t (D ∘ z))) := by
              simpa [q] using (CMvPolynomial.roundPoly_eval (D := D) k pResid t)
      _ = (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
            CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m) (fixed := fixed.push t) D
                (castTail z))
              polyCast.val) := by
              refine Finset.sum_congr rfl ?_
              intro z _
              calc
                pResid.eval (Fin.cons t (D ∘ z))
                    = polyCast.val.eval
                        (CMvPolynomial.prefixPoint fixed
                          (Fin.cons t (D ∘ z))) := by
                        simpa [pResid] using
                          (CMvPolynomial.partialEvalPrefix_eval fixed
                            polyCast.val (Fin.cons t (D ∘ z)))
                _ = polyCast.val.eval
                      (evalPoint (R := R) (n := k + 1 + i) (m := m)
                        (fixed := fixed.push t) D
                        (castTail z)) := by
                        simp [hPrefix t z]
      _ = trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
            (i := i + 1) (fixed.push t) D := by
              calc
                (∑ z : Fin k → Fin m,
                  CMvPolynomial.eval
                    (evalPoint (R := R) (n := k + 1 + i) (m := m)
                      (fixed := fixed.push t) D (castTail z))
                    polyCast.val)
                    =
                  ∑ z' : Fin (k + 1 + i - (i + 1)) → Fin m,
                    CMvPolynomial.eval
                      (evalPoint (R := R) (n := k + 1 + i) (m := m)
                        (fixed := fixed.push t) D z')
                      polyCast.val := by
                        simpa [eTail, castTail] using
                          (Fintype.sum_equiv eTail
                            (fun z : Fin k → Fin m =>
                              CMvPolynomial.eval
                                (evalPoint (R := R) (n := k + 1 + i) (m := m)
                                  (fixed := fixed.push t) D (castTail z))
                                polyCast.val)
                            (fun z' : Fin (k + 1 + i - (i + 1)) → Fin m =>
                              CMvPolynomial.eval
                                (evalPoint (R := R) (n := k + 1 + i) (m := m)
                                  (fixed := fixed.push t) D z')
                                polyCast.val)
                            (fun _ => rfl))
                _ = trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
                      (i := i + 1) (fixed.push t) D := by
                        unfold trueTarget
                        rfl
      _ = trueRoundValue (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
            (i := i) fixed D t := by
              simpa using
                (trueTarget_push_eq_trueRoundValue
                  (R := R) (n := k + 1 + i) (m := m)
                  (poly := polyCast) (D := D) i fixed t)
  have hTargetDecomp :
      (Finset.univ : Finset (Fin m)).sum (fun a =>
        trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
          (i := i + 1) (fixed.push (D a)) D) =
      trueTarget (R := R) (n := k + 1 + i) (m := m)
        (poly := polyCast) (i := i) fixed D := by
    let e : (Fin m × (Fin k → Fin m)) ≃ (Fin (k + 1) → Fin m) := {
      toFun := fun az => Fin.cons az.1 az.2
      invFun := fun z => (z 0, fun j => z j.succ)
      left_inv := by
        intro az
        cases az
        simp
      right_inv := by
        intro z
        funext j
        cases j using Fin.cases with
        | zero => simp
        | succ j => simp
    }
    have hProd :
        (∑ a : Fin m, ∑ z : Fin k → Fin m,
          CMvPolynomial.eval
            (evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed.push (D a)) D (castTail z))
            polyCast.val)
          =
        ∑ az : Fin m × (Fin k → Fin m),
          CMvPolynomial.eval
            (evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed.push (D az.1)) D (castTail az.2))
            polyCast.val := by
      simpa using
        (Fintype.sum_prod_type
          (f := fun az : Fin m × (Fin k → Fin m) =>
            CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed.push (D az.1)) D (castTail az.2))
              polyCast.val)).symm
    have hPrefixHead :
        ∀ z' : Fin (k + 1) → Fin m,
          CMvPolynomial.prefixPoint fixed (D ∘ z') =
            evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed) D (castHead z') := by
      intro z'
      funext x
      by_cases hx : x.1 < i
      · simp [CMvPolynomial.prefixPoint_spec, evalPoint, hx,
          Vector.get_eq_getElem]
      · have hidxBound : x.1 - i < k + 1 := by omega
        simp [CMvPolynomial.prefixPoint_spec, evalPoint, castHead,
          hx, hidxBound, hk_succ]
    have hEvalPointCons :
        ∀ az : Fin m × (Fin k → Fin m),
          CMvPolynomial.eval
            (evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed.push (D az.1)) D (castTail az.2))
            polyCast.val
            =
          CMvPolynomial.eval
            (evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed) D
              (castHead (Fin.cons az.1 az.2)))
            polyCast.val := by
      intro az
      rcases az with ⟨a, z⟩
      have hCons : Fin.cons (D a) (D ∘ z) = D ∘ Fin.cons a z := by
        funext j
        cases j using Fin.cases with
        | zero => simp [Function.comp]
        | succ j => simp [Function.comp]
      calc
        CMvPolynomial.eval
            (evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed.push (D a)) D (castTail z))
            polyCast.val
            =
          CMvPolynomial.eval
            (CMvPolynomial.prefixPoint fixed
              (Fin.cons (D a) (D ∘ z)))
            polyCast.val := by
              simpa using
                congrArg (fun v => CMvPolynomial.eval v polyCast.val)
                  (hPrefix (D a) z).symm
        _ = CMvPolynomial.eval
              (CMvPolynomial.prefixPoint fixed (D ∘ Fin.cons a z))
              polyCast.val := by
                simp [hCons]
        _ = CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed) D (castHead (Fin.cons a z)))
              polyCast.val := by
                simpa using
                  congrArg (fun v => CMvPolynomial.eval v polyCast.val)
                    (hPrefixHead (Fin.cons a z))
    calc
      (∑ a : Fin m,
        trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
          (i := i + 1) (fixed.push (D a)) D)
          =
        (∑ a : Fin m, ∑ z : Fin k → Fin m,
          CMvPolynomial.eval
            (evalPoint (R := R) (n := k + 1 + i) (m := m)
              (fixed := fixed.push (D a)) D (castTail z))
            polyCast.val) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              symm
              simpa [eTail, castTail] using
                (Fintype.sum_equiv eTail
                  (fun z : Fin k → Fin m =>
                    CMvPolynomial.eval
                      (evalPoint (R := R) (n := k + 1 + i) (m := m)
                        (fixed := fixed.push (D a)) D (castTail z))
                      polyCast.val)
                  (fun z' : Fin (k + 1 + i - (i + 1)) → Fin m =>
                    CMvPolynomial.eval
                      (evalPoint (R := R) (n := k + 1 + i) (m := m)
                        (fixed := fixed.push (D a)) D z')
                      polyCast.val)
                  (fun _ => rfl))
      _ = ∑ az : Fin m × (Fin k → Fin m),
            CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed.push (D az.1)) D (castTail az.2))
              polyCast.val := hProd
      _ = ∑ az : Fin m × (Fin k → Fin m),
            CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed) D
                (castHead (Fin.cons az.1 az.2)))
              polyCast.val := by
                refine Fintype.sum_congr
                  (f := fun az : Fin m × (Fin k → Fin m) =>
                    CMvPolynomial.eval
                      (evalPoint (R := R) (n := k + 1 + i) (m := m)
                        (fixed := fixed.push (D az.1)) D
                        (castTail az.2))
                      polyCast.val)
                  (g := fun az : Fin m × (Fin k → Fin m) =>
                    CMvPolynomial.eval
                      (evalPoint (R := R) (n := k + 1 + i) (m := m)
                        (fixed := fixed) D
                        (castHead (Fin.cons az.1 az.2)))
                      polyCast.val) ?_
                intro az
                exact hEvalPointCons az
      _ = ∑ z' : Fin (k + 1) → Fin m,
            CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed) D (castHead z'))
              polyCast.val := by
                simpa [e, castHead] using
                  (Fintype.sum_equiv e
                    (fun az : Fin m × (Fin k → Fin m) =>
                      CMvPolynomial.eval
                        (evalPoint (R := R) (n := k + 1 + i) (m := m)
                          (fixed := fixed) D
                          (castHead (Fin.cons az.1 az.2)))
                        polyCast.val)
                    (fun z' : Fin (k + 1) → Fin m =>
                      CMvPolynomial.eval
                        (evalPoint (R := R) (n := k + 1 + i) (m := m)
                          (fixed := fixed) D (castHead z'))
                        polyCast.val)
                    (fun _ => rfl))
      _ = ∑ z'' : Fin (k + 1 + i - i) → Fin m,
            CMvPolynomial.eval
              (evalPoint (R := R) (n := k + 1 + i) (m := m)
                (fixed := fixed) D z'')
              polyCast.val := by
                simpa [eHead, castHead] using
                  (Fintype.sum_equiv eHead
                    (fun z' : Fin (k + 1) → Fin m =>
                      CMvPolynomial.eval
                        (evalPoint (R := R) (n := k + 1 + i) (m := m)
                          (fixed := fixed) D (castHead z'))
                        polyCast.val)
                    (fun z'' : Fin (k + 1 + i - i) → Fin m =>
                      CMvPolynomial.eval
                        (evalPoint (R := R) (n := k + 1 + i) (m := m)
                          (fixed := fixed) D z'')
                        polyCast.val)
                    (fun _ => rfl))
      _ = trueTarget (R := R) (n := k + 1 + i) (m := m)
            (poly := polyCast) (i := i) fixed D := by
            unfold trueTarget
            rfl
  have hqSum :
      ((Finset.univ : Finset (Fin m)).sum (fun a =>
          CPolynomial.eval (D a) q.val) =
        trueTarget (R := R) (n := k + 1 + i) (m := m)
          (poly := polyCast) (i := i) fixed D) := by
    calc
      (∑ a : Fin m, CPolynomial.eval (D a) q.val)
          = ∑ a : Fin m,
              trueRoundValue (R := R) (n := k + 1 + i) (m := m)
                (poly := polyCast) (i := i) fixed D (D a) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                exact hqEval (D a)
      _ = ∑ a : Fin m,
            trueTarget (R := R) (n := k + 1 + i) (m := m) (poly := polyCast)
              (i := i + 1) (fixed.push (D a)) D := by
                refine Finset.sum_congr rfl ?_
                intro a _
                symm
                exact trueTarget_push_eq_trueRoundValue
                  (R := R) (n := k + 1 + i) (m := m)
                  (poly := polyCast) (D := D) i fixed (D a)
      _ = trueTarget (R := R) (n := k + 1 + i) (m := m)
            (poly := polyCast) (i := i) fixed D := hTargetDecomp
  exact ⟨q, hqEval, hqSum⟩

end Sumcheck
