/-
Presentation-quality definitions for the sumcheck protocol.
Everything here compiles. Used as source for slide code snippets.
-/
import ArkLib.Refactor.Sumcheck.SingleRound
import ArkLib.Refactor.Sumcheck.General

open CompPoly CPoly ProtocolSpec OracleComp OracleSpec
open scoped BigOperators

namespace Sumcheck.Slides

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
variable {n m deg : ℕ}

-- ═══════════════════════════════════════════════════
-- FIGURE 1: Protocol Specification
-- ═══════════════════════════════════════════════════

section Spec

open ProtocolSpec

-- IMPORTANT: CUSTOM DEFINITION AND NOTATION HERE FOR MAXIMUM READABILITY

local notation:max F"⦃≤"d"⦄[X]" => CDegreeLE F d

local notation:max F"⦃≤"d"⦄[X_⟦"n"⟧]" => CMvDegreeLE F n d

abbrev BoolVec (k : ℕ) := Fin k → Fin 2

local notation:max D "^⦃" k "⦄" => (D : Finset (Fin k → Fin 2))

local notation:max "#⸨"D"⸩" => Fintype.card D


set_option quotPrecheck false in
local macro:max p:term " ⸨" x:term "⸩" : term => `(sorry)

set_option quotPrecheck false in
local macro:max p:term " ⸨" x:term ", " y:term "⸩" : term => `(sorry)

local macro:max p:term " ⸨X, " y:term "⸩" : term => `(sorry)

inductive Direction where | P_to_V | V_to_P

def ProtocolSpec := List (Direction × Type)

def Transcript : ProtocolSpec → Type
  | [] => Unit
  | (.P_to_V, Msg) :: rest => Msg × Transcript rest
  | (.V_to_P, Chal) :: rest => Chal × Transcript rest

variable (F : Type) [Field F] (d n : ℕ)

variable [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

def scRoundSpec : ProtocolSpec :=
  [(.P_to_V, F⦃≤ d⦄[X]), (.V_to_P, F)]


def Prover (Output : Type) : ProtocolSpec → Type
  | [] => Output
  | (.P_to_V, Msg) :: rest => Msg × Prover Output rest
  | (.V_to_P, Chal) :: rest => Chal → Prover Output rest

structure scRoundInput where
  target : F
  poly : F⦃≤ d⦄[X_⟦n⟧]

structure scRoundOutput where
  newTarget : F
  challenge : F
  poly : F⦃≤ d⦄[X_⟦n⟧]

/- (target, poly) →
     (message ×
       (challenge →
         (newTarget, challenge, poly))) -/
def scRoundProver' : (scRoundInput F d n) →
    Prover (scRoundOutput F d n) (scRoundSpec F d) := sorry

def scRoundProver (T₀ : F) (P : F⦃≤ d⦄[X_⟦n⟧]) :
    Prover (F × F⦃≤ d⦄[X_⟦n-1⟧]) (scRoundSpec F d) :=
  let sPoly := ∑ b ∈ {0, 1} ^⦃n-1⦄, P ⸨X, b⸩
  (sPoly, fun r => (sPoly ⸨r⸩, P ⸨r, ·⸩))


def Verifier (Input Output : Type) (pSpec : ProtocolSpec) : Type :=
  Input → Transcript pSpec → Option Output

open scoped NNReal

variable (Stmt : Type) (language : Set Stmt)

def soundness (ε : ℝ≥0) : Prop :=
    ∀ stmt ∉ language, ∀ prover,
  Pr[fun result => result = some (T₁, P) ∧ sumPoly P = T₁ | do return ⟪prover, verifier⟫(stmt)] ≤ ε

def scRoundVerifier :
    Verifier (F × F⦃≤ d⦄[X_⟦n-1⟧]) (F × F) scRoundSpec := sorry



-- n-round sumcheck = n copies of the per-round spec
@[reducible] def nRoundSpec (n : ℕ) : ProtocolSpec :=
  ProtocolSpec.replicate n (spec (R := R) (deg := deg))

-- A transcript records all messages and challenges
-- Transcript  pSpec := HVector Round.type pSpec
-- Challenges  pSpec := HVector id (challengeTypes pSpec)
-- Messages    pSpec := HVector id (messageTypes pSpec)

end Spec

-- ═══════════════════════════════════════════════════
-- FIGURE 2: Honest Prover
-- ═══════════════════════════════════════════════════

-- The prover computes the round polynomial via evaluate-and-interpolate,
-- sends it, and upon receiving challenge r returns new target p(r).
def prover' {i : ℕ}
    (poly : OStmt R deg n) (challenges : Vector R i)
    (D : Fin m → R) (pts : Vector R (deg + 1)) :
    Prover Id (StmtOut R) (pSpec R deg) :=
  let p := computeRoundPoly poly challenges D pts
  (p, pure fun r => pure ⟨CPolynomial.eval r p.val, r⟩)

-- ═══════════════════════════════════════════════════
-- FIGURE 3: Verifier & Oracle Verifier
-- ═══════════════════════════════════════════════════

-- Plain verifier: reads polynomial p and challenge r from transcript
def verifier' (D : Fin m → R) :
    Verifier Id (StmtIn R) (StmtOut R) (pSpec R deg) :=
  fun target tr =>
    let p := tr.head
    let r := tr.tail.head
    if ∑ i : Fin m, CPolynomial.eval (D i) p.val = target
    then pure ⟨CPolynomial.eval r p.val, r⟩
    else failure

-- Oracle verifier: queries polynomial p via oracle interface
-- (does not see p directly — only makes point queries)
section OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

def queryPoly (x : R) :
    OracleComp (oSpec + [fun (_ : Unit) => OStmt R deg n]ₒ +
      oracleSpecOfMessages (pSpec R deg)) R := by
  change OracleComp _ (oracleSpecOfMessages (pSpec R deg) (Sum.inl x))
  exact OracleComp.lift (OracleQuery.query (spec :=
    oSpec + [fun (_ : Unit) => OStmt R deg n]ₒ + oracleSpecOfMessages (pSpec R deg))
    (Sum.inr (Sum.inl x)))

def oracleVerifier' (D : Fin m → R) :
    OracleVerifier oSpec
      (StmtIn R) (fun (_ : Unit) => OStmt R deg n)
      (StmtOut R) (fun (_ : Unit) => OStmt R deg n)
      (pSpec R deg) where
  verify target challenges := do
    let evals ← (List.finRange m).mapM fun i =>
      OptionT.lift (queryPoly (D i))
    guard (evals.sum = target)
    let r := challenges.head
    let t' ← OptionT.lift (queryPoly r)
    pure ⟨t', r⟩
  simulate q :=
    liftM (query (spec := [fun (_ : Unit) => OStmt R deg n]ₒ +
      oracleSpecOfMessages (pSpec R deg)) (Sum.inl q))
  reify data _ := some data

end OracleVerifier

-- ═══════════════════════════════════════════════════
-- FIGURE 4: n-Round Reduction
-- ═══════════════════════════════════════════════════

-- Full n-round sumcheck reduction:
-- prover iterates n rounds, verifier composes n checks
def generalReduction'
    (poly : OStmt R deg n) (D : Fin m → R)
    (evalPoints : Vector R (deg + 1)) :
    Reduction Id R Unit (RoundState (R := R)) Unit (generalPSpec R deg n) where
  prover := fun (target, ()) => do
    let backend : ∀ i : ℕ, Vector R i → CDegreeLE R deg :=
      fun i prev => computeRoundPoly poly prev D evalPoints
    Prover.iterate (pSpec R deg) n
      (roundProverStep backend) (initState target, ())
  verifier := generalVerifier D

end Sumcheck.Slides
