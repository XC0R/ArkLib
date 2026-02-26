/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Sumcheck.General

/-!
# Sumcheck Protocol Test

Runs the full sumcheck protocol (both prover and verifier) on a concrete example
over `ZMod 7`:

- **Polynomial**: `p(x₀, x₁) = x₀ + x₁` (2 variables, degree 1 in each)
- **Domain**: `D = {0, 1}` (binary, `m = 2`)
- **Degree bound**: `deg = 1`
- **Claimed sum**: `∑_{(a,b) ∈ {0,1}²} (a + b) = 0 + 1 + 1 + 2 = 4`

The prover, verifier, and full reduction are all **computable**. The only `sorry`
dependency is `lagrangeInterpolate_natDegree` (a proof obligation, not executable
code), so `#eval!` is used for the full reduction.

## Round-by-round

**Round 1** (variable `x₀`):
  `g₁(X) = 2X + 1`, coefficients `#[1, 2]`
  Check: `g₁(0) + g₁(1) = 1 + 3 = 4 = target` ✓
  Challenge: `r₁ = 3`  →  new target = `g₁(3) = 0 mod 7`

**Round 2** (variable `x₁`):
  `g₂(X) = X + 3`, coefficients `#[3, 1]`
  Check: `g₂(0) + g₂(1) = 3 + 4 = 0 mod 7 = new target` ✓
  Challenge: `r₂ = 5`  →  final target = `g₂(5) = 1 mod 7`
-/

open CompPoly CPoly ProtocolSpec

namespace Sumcheck.Test

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev F := ZMod 7

def myPoly : CMvPolynomial 2 F := CMvPolynomial.X 0 + CMvPolynomial.X 1
def D : Fin 2 → F := fun i => (i : F)
def evalPts : Vector F 2 := ⟨#[0, 1], rfl⟩

/-! ## Evaluation tests (native_decide) -/

-- Round 1 polynomial: g₁(X) = 2X + 1
def g₁ : CompPoly.CPolynomial F := ⟨#[(1 : F), 2], by native_decide⟩
def g₂ : CompPoly.CPolynomial F := ⟨#[(3 : F), 1], by native_decide⟩

example : CPolynomial.eval (0 : F) g₁ = 1 := by native_decide
example : CPolynomial.eval (1 : F) g₁ = 3 := by native_decide
example : CPolynomial.eval (3 : F) g₁ = 0 := by native_decide
example : CPolynomial.eval (0 : F) g₂ = 3 := by native_decide
example : CPolynomial.eval (1 : F) g₂ = 4 := by native_decide
example : CPolynomial.eval (5 : F) g₂ = 1 := by native_decide

/-! ## Verifier acceptance (native_decide) -/

def roundPoly₁ : CDegreeLE F 1 := ⟨g₁, by native_decide⟩
def roundPoly₂ : CDegreeLE F 1 := ⟨g₂, by native_decide⟩

def transcript : Transcript (generalPSpec F 1 2) :=
  (roundPoly₁, ((3 : F), (roundPoly₂, ((5 : F), PUnit.unit))))

-- Verifier ACCEPTS honest transcript
example :
    (generalVerifier (n := 2) (m := 2) (deg := 1) D (4 : F) transcript).isSome = true := by
  native_decide

-- Verifier output = 1
example : (generalVerifier (n := 2) (m := 2) (deg := 1) D (4 : F) transcript).get
    (by native_decide) = (1 : F) := by
  native_decide

-- Wrong target REJECTED
example :
    (generalVerifier (n := 2) (m := 2) (deg := 1) D (3 : F) transcript).isSome = false := by
  native_decide

/-! ## Full reduction execution (#eval!) -/

-- Run the full honest prover + verifier end-to-end
#eval! do
  let challenges : Challenges (generalPSpec F 1 2) :=
    ((3 : F), ((5 : F), PUnit.unit))
  let result := (generalReduction myPoly D evalPts).run (4 : F) () challenges
  let (verResult, (proverOut, ())) := result
  let showF := fun (x : F) => toString x.val
  IO.println s!"=== Sumcheck over ZMod 7 ==="
  IO.println s!"Polynomial: p(x₀, x₁) = x₀ + x₁"
  IO.println s!"Domain: D = \{0, 1}"
  IO.println s!"Claimed sum: 4"
  IO.println s!"Challenges: r₁ = 3, r₂ = 5"
  IO.println s!"Verifier: {if verResult.isSome then "ACCEPTED" else "REJECTED"}"
  match verResult with
  | some v => IO.println s!"Final target (verifier): {showF v}"
  | none => pure ()
  IO.println s!"Final target (prover):  {showF proverOut}"
  IO.println s!"(should be p(3,5) = 3 + 5 = 8 = 1 mod 7)"

end Sumcheck.Test
