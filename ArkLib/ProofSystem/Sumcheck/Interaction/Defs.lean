/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Chain
import ArkLib.Interaction.TwoParty.Compose
import ArkLib.Interaction.Reduction
import ArkLib.ProofSystem.Sumcheck.Interaction.CompPoly

/-!
# Interaction-Native Sum-Check: Shared Definitions

This module defines the shared algebraic core for the Interaction-native sum-check stack,
using CompPoly types throughout.

## Overview

The sum-check protocol verifies a claim of the form

  `∑ x ∈ D^n, poly(x) = target`

where `poly : CMvDegreeLE R n deg` is a computable multivariate polynomial over `n` variables
with individual degree at most `deg`, `D` is a finite evaluation domain, and `target : R` is
the claimed sum.

A single round of sum-check is a two-message interaction:
1. **Prover → Verifier**: the prover sends the *round polynomial*, a `CDegreeLE R deg`
   univariate polynomial obtained by keeping one variable free and summing the rest over `D`.
2. **Verifier → Prover**: the verifier replies with a random field challenge `r_i`.

After round `i`, the target is updated to `p_i(r_i)`. The public *stage state*
(`RoundClaim R`) carries only this target; challenge history lives in the chained transcript.

## Main Definitions

- `RoundClaim R`: the public per-round claim (target value), the state chain stage state.
- `roundSpec R deg`: the `Interaction.Spec` for one round (two messages).
- `roundRoles R deg`: the `RoleDecoration` (sender then receiver).
- `advance`: updates the stage state after a round (`target ↦ poly.eval(challenge)`).
- `roundCheck`: the per-round sum check (computable `Bool`).
- `RoundCheckProp`: propositional version of `roundCheck`.
- `fullSum`: the full sum `∑_{x ∈ D^n} poly(x)` that sum-check verifies.
-/

namespace Sumcheck

open Interaction CompPoly CPoly

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (deg : ℕ)

/-- The public claim at each round of sum-check: just the target sum value.
This is the state chain `Stage` type (uniform across rounds). -/
abbrev RoundClaim := R

/-! ## Single-round interaction shape -/

/-- The `Interaction.Spec` for a single round: prover sends a degree-bounded univariate
polynomial (`CDegreeLE R deg`), then verifier sends a field element challenge. -/
def roundSpec : Spec :=
  .node (CDegreeLE R deg) fun _ =>
    .node R fun _ =>
      .done

/-- Role decoration for a single round: prover (sender) sends first, verifier (receiver)
sends second. -/
def roundRoles : RoleDecoration (roundSpec R deg) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

/-- Extract the polynomial from a single-round transcript. -/
abbrev roundPoly (tr : Spec.Transcript (roundSpec R deg)) :
    CDegreeLE R deg :=
  tr.1

/-- Extract the challenge from a single-round transcript. -/
abbrev roundChallenge (tr : Spec.Transcript (roundSpec R deg)) :
    R :=
  tr.2.1

/-- Advance the public claim after one round: evaluate the sent polynomial at the challenge.
This is the state chain `advance` function. The new target is `poly.eval(challenge)`. -/
def advance
    (_ : Nat) (_ : RoundClaim R) (tr : Spec.Transcript (roundSpec R deg)) :
    RoundClaim R :=
  CPolynomial.eval (roundChallenge R deg tr) (roundPoly R deg tr).1

/-! ## Per-round sum check -/

/-- The per-round sum check: verify that the univariate polynomial's evaluations over the
domain `D` sum to the claimed target. This is the defining check of sum-check. -/
def roundCheck {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (poly : CDegreeLE R deg) : Bool :=
  ((Finset.univ : Finset (Fin m_dom)).sum fun j => CPolynomial.eval (D j) poly.1) == target

/-- Propositional version of `roundCheck`: the polynomial's evaluations over `D`
sum to the target. -/
def RoundCheckProp {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (poly : CDegreeLE R deg) : Prop :=
  ((Finset.univ : Finset (Fin m_dom)).sum fun j => CPolynomial.eval (D j) poly.1) = target

/-- The full sum `∑_{z ∈ D^n} poly(D ∘ z)` of a multivariate polynomial over the product domain.
This is the claimed quantity in sum-check: the protocol verifies `fullSum D poly = target`. -/
def fullSum {n : ℕ} {m_dom : ℕ} (D : Fin m_dom → R) (poly : CMvDegreeLE R n deg) : R :=
  (Finset.univ : Finset (Fin n → Fin m_dom)).sum fun z =>
    CMvPolynomial.eval (D ∘ z) poly.1

/-! ## Uniform-round helpers for `Spec.stateChain` -/

/-- The per-round spec, ignoring both index and stage state (the round shape is uniform). -/
def roundSpecFn (_ : Nat) (_ : RoundClaim R) : Spec :=
  roundSpec R deg

/-- The per-round role decoration, ignoring both index and stage state. -/
def roundRolesFn (_ : Nat) (_ : RoundClaim R) :
    RoleDecoration (roundSpec R deg) :=
  roundRoles R deg

end

end Sumcheck
