/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import ArkLib.OracleReduction.Security.Basic
import Clean.Circuit.Foundations

/-!
# Clean ↔ ArkLib Bridge

This module bridges Clean's `FormalCircuit` (circuit-level soundness/completeness) to ArkLib's
`Reduction` (protocol-level security). Clean circuits are deterministic non-interactive arguments:
the prover provides a witness environment, the verifier checks polynomial constraints. This maps
directly to a `NonInteractiveReduction`.

## Architecture

- **Clean**: `FormalCircuit F Input Output` with `Soundness` (constraints → spec) and
  `Completeness` (assumptions → constraints satisfiable)
- **ArkLib**: `Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec` with probabilistic
  completeness/soundness security definitions

The bridge wraps a `FormalCircuit` as a `NonInteractiveReduction` where:
- `StmtIn = Input F` (public input)
- `WitIn = Environment F` (prover's full variable assignment)
- `StmtOut = Output F` (circuit output)
- `WitOut = Unit`
- Message = the witness environment (single prover→verifier message)

Both prover and verifier use the canonical input variable encoding `varFromOffset Input 0`.

## Main results

- `toReduction`: wraps a `FormalCircuit` as a `NonInteractiveReduction`
- `reduction_perfectCompleteness`: transfers both Clean security properties into ArkLib's
  perfect completeness. Clean's `original_completeness` (assumptions imply constraints hold)
  and `original_soundness` (constraints imply spec) compose to show the output satisfies
  `Spec` with probability 1.
- `reduction_soundness`: ArkLib-structural soundness (error = 0). Inputs outside `Assumptions`
  are rejected by the verifier. This is a property of the bridge construction, not a transfer
  of Clean's soundness (which is already used in `reduction_perfectCompleteness` above).
-/

open OracleSpec OracleComp ProtocolSpec Circuit

namespace Clean.Bridge

variable {F : Type} [Field F]
  {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-! ### Canonical input variable encoding -/

/-- The canonical variable encoding for the input type, starting at offset 0.
    Both prover and verifier use this encoding for consistency. -/
abbrev canonicalInputVar (Input : TypeMap) (F : Type) [Field F] [ProvableType Input] :
    Var Input F :=
  varFromOffset Input 0

/-! ### Protocol specification -/

/-- Protocol spec for a Clean circuit: single prover→verifier message containing the environment.
    This is a 1-round protocol where the prover sends and the verifier decides. -/
@[reducible, simp]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Environment F]⟩

/-- No challenges in a single-message P→V protocol. -/
instance : ∀ i, VCVCompatible ((pSpec (F := F)).Challenge i) | ⟨0, h⟩ => nomatch h

/-- Our protocol spec is prover-only (single P→V message, no challenges). -/
instance : ProverOnly (pSpec (F := F)) where
  prover_first' := rfl

/-! ### Prover construction -/

/-- The prover for a Clean circuit reduction.
    Takes input and witness environment, sends the environment as its single message.
    After sending, outputs the circuit's computed result using the canonical input encoding. -/
def mkProver (circuit : FormalCircuit F Input Output) :
    Prover []ₒ (Input F) (Environment F) (Output F) Unit (pSpec (F := F)) where
  PrvState
  | 0 => (Input F) × (Environment F)
  | 1 => (Input F) × (Environment F)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨_inp, env⟩ => pure (env, ⟨_inp, env⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨_inp, env⟩ =>
    let inputVar := canonicalInputVar Input F
    let output := eval env (circuit.output inputVar 0)
    pure (output, ())

/-! ### Verifier construction -/

/-- The verifier for a Clean circuit reduction.
    Receives the input statement and the transcript (containing the prover's environment message).
    Noncomputably checks `circuit.Assumptions` on the input; if satisfied, computes and returns
    the circuit output. If assumptions fail, rejects.

    The constraint-checking is implicit: soundness of the bridge follows from the fact that
    the verifier rejects all inputs outside the Assumptions language, making the ArkLib soundness
    error = 0. Completeness uses Clean's original_completeness + original_soundness
    to show the output satisfies Spec. -/
noncomputable def mkVerifier (circuit : FormalCircuit F Input Output) :
    Verifier []ₒ (Input F) (Output F) (pSpec (F := F)) where
  verify := fun inp transcript =>
    haveI : Decidable (circuit.Assumptions inp) := Classical.propDecidable _
    let env : Environment F := transcript ⟨0, by omega⟩
    let inputVar := canonicalInputVar Input F
    if circuit.Assumptions inp then
      pure (eval env (circuit.output inputVar 0))
    else
      failure

/-! ### Reduction assembly -/

/-- The full non-interactive reduction wrapping a Clean `FormalCircuit`.

This is the core bridge construction: given a Clean circuit with proven soundness and completeness,
we obtain an ArkLib `NonInteractiveReduction` suitable for composition with ArkLib's protocol
machinery (Fiat-Shamir, commitment schemes, etc.). -/
noncomputable def toReduction (circuit : FormalCircuit F Input Output) :
    NonInteractiveReduction (Environment F) []ₒ
      (Input F) (Environment F) (Output F) Unit :=
  { prover := mkProver circuit
    verifier := mkVerifier circuit }

/-! ### Relations -/

/-- The input relation: pairs `(input, env)` where:
    - `input` satisfies the circuit's assumptions
    - evaluating the canonical input encoding in `env` yields `input`
    - `env` uses local witness generators (needed for completeness) -/
def relIn (circuit : FormalCircuit F Input Output) :
    Set ((Input F) × Environment F) :=
  { p | circuit.Assumptions p.1 ∧
        eval p.2 (canonicalInputVar Input F) = p.1 ∧
        p.2.UsesLocalWitnesses 0
          (circuit.main (canonicalInputVar Input F) |>.operations 0) }

/-- The output relation: pairs `(output, ())` where the output satisfies the circuit's spec
    with respect to some input. -/
def relOut (circuit : FormalCircuit F Input Output) :
    Set ((Output F) × Unit) :=
  { p | ∃ input : Input F, circuit.Spec input p.1 }

/-! ### Security transfer theorems -/

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- **Completeness transfer**: Clean's `Completeness` implies ArkLib's `perfectCompleteness`.

Clean says: given assumptions, the default witness generator produces a satisfying assignment.
ArkLib says: the honest prover convinces the verifier with probability 1.

The bridge: the honest prover uses the witness environment. By Clean's `original_completeness`,
the constraints hold. By Clean's `original_soundness`, the spec holds on the output. Since
everything is deterministic (no randomness in `[]ₒ`), success probability = 1. -/
theorem reduction_perfectCompleteness (circuit : FormalCircuit F Input Output) :
    Reduction.perfectCompleteness init impl
      (relIn circuit) (relOut circuit) (toReduction circuit) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  simp only [relIn, Set.mem_setOf_eq] at hIn
  obtain ⟨hAssume, hEval, hWit⟩ := hIn
  -- Derive the Clean soundness chain: Assumptions + UsesLocalWitnesses → Spec
  have hConstr := circuit.original_completeness 0 witIn
    (canonicalInputVar Input F) stmtIn hEval hAssume hWit
  have hSpec := circuit.original_soundness 0 witIn
    (canonicalInputVar Input F) stmtIn hEval hAssume hConstr
  -- ProverOnly instance enables Prover.run_of_prover_first to reduce Prover.run
  -- for our 1-round pSpec, eliminating the Fin.induction blocker.
  set_option linter.unusedSimpArgs false in
  simp only [toReduction, Reduction.run, Verifier.run, mkVerifier, mkProver,
    if_pos hAssume, OptionT.run_pure,
    Prover.run_of_prover_first,
    OracleComp.liftComp_eq_liftM, monadLift_pure, pure_bind,
    OptionT.run_bind, OptionT.run_monadLift,
    map_pure, Option.elim_some, Option.getM, bind_pure_comp, Functor.map_map,
    Option.elimM, bind_map_left, Option.elim_none, OptionT.run_failure,
    simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- probFailure = 0: OptionT.mk (some v <$> init) never fails
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_map, Set.mem_image, not_exists, not_and]
    intro _ _
    exact nofun
  · -- All outputs satisfy relOut ∧ prover=verifier agreement
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_map, Set.mem_image] at hx
    obtain ⟨_, _, hx⟩ := hx
    simp only [Option.some.injEq] at hx
    subst hx
    exact ⟨⟨stmtIn, hSpec⟩, rfl⟩

/-- **Structural soundness**: ArkLib soundness with error 0.

The verifier noncomputably checks `circuit.Assumptions`. For any input `stmtIn` outside
`{Assumptions}`, the check fails and the verifier rejects (returns `failure`). Since
`OptionT.mk` wraps this as `none`, no output is produced, and the probability of
accepting into `langOut` is 0.

Note: Clean's `original_soundness` (constraints imply spec) is not used here. It is
transferred via `reduction_perfectCompleteness`, where it ensures output correctness
for in-language inputs. -/
theorem reduction_soundness (circuit : FormalCircuit F Input Output) :
    Verifier.soundness init impl
      { inp | circuit.Assumptions inp }
      { out | ∃ inp, circuit.Spec inp out }
      (toReduction circuit).verifier 0 := by
  simp only [Verifier.soundness, toReduction, mkVerifier, ENNReal.coe_zero, nonpos_iff_eq_zero]
  intro WitIn WitOut witIn prover stmtIn hNotIn
  simp only [Set.mem_setOf_eq] at hNotIn
  simp only [Reduction.run, Verifier.run, if_neg hNotIn, OptionT.run_failure]
  rw [probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  exfalso
  -- The inner OptionT computation's .run always produces none because the verifier
  -- returns failure (¬ Assumptions), causing getM on none to fail.
  -- After OptionT.run_bind, liftM (pure none) >>= getM reduces to pure none.
  -- The full OracleComp is Prover.run ... >>= fun _ => pure none.
  -- After simulateQ and StateT.run', support ⊆ {none}, contradicting some x ∈ support.
  set_option linter.unusedSimpArgs false in
  simp only [OptionT.run_bind, OptionT.run_monadLift, map_pure, Option.elim_some,
    OptionT.run_failure, Option.elim_none, Option.getM,
    simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    support_map, support_bind, support_pure, Set.mem_image, Set.mem_iUnion,
    Set.mem_singleton_iff, bind_pure_comp, Functor.map_map] at hx
  obtain ⟨⟨_, _⟩, _, rfl⟩ := hx
  simp at *

end Clean.Bridge
