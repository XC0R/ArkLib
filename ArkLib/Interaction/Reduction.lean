/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.TwoParty

/-!
# Provers, Verifiers, and Reductions

Interactive protocol participants and their composition, built on `Spec` with
a `RoleDecoration`. The protocol structure is a `Spec` (interaction tree) plus
a `RoleDecoration` that assigns sender/receiver roles to each node.

- **Prover**: takes (statement, witness), produces a role-dependent `Strategy`
  that interacts with the verifier and outputs a new (statement, witness) pair.
- **Verifier**: holds a `Counterpart` (challenge sampler / message observer)
  and a decision function applied after the interaction completes.
- **Reduction**: pairs a prover with a verifier for the same protocol spec.

## Running a reduction

`Reduction.execute` runs the prover's strategy against the verifier's
counterpart (via `Strategy.runWithRoles`), then applies the verifier's decision.
-/

set_option autoImplicit false

namespace Interaction

variable {m : Type → Type}

/-! ## Protocol participants -/

/-- A prover in an interactive protocol. Given a statement and witness, the
prover produces a role-dependent strategy that interacts over `pSpec` with
role assignments `roles`, outputting a new statement-witness pair. -/
structure Prover (m : Type → Type) (pSpec : Spec) (roles : RoleDecoration pSpec)
    (StmtIn WitIn StmtOut WitOut : Type) where
  run : StmtIn → WitIn → Spec.Strategy.withRoles m pSpec roles (fun _ => StmtOut × WitOut)

/-- A verifier in an interactive protocol. The `challenger` field is the
verifier's behavior during interaction: it observes prover messages (Pi at
sender nodes) and samples challenges (Sigma at receiver nodes). After the
interaction, `decide` examines the statement and full transcript. -/
structure Verifier (m : Type → Type) (pSpec : Spec) (roles : RoleDecoration pSpec)
    (StmtIn : Type) where
  challenger : Spec.Counterpart m pSpec roles
  decide : StmtIn → Spec.Transcript pSpec → m Bool

/-- A reduction pairs a prover with a verifier for the same protocol. -/
structure Reduction (m : Type → Type) (pSpec : Spec) (roles : RoleDecoration pSpec)
    (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover m pSpec roles StmtIn WitIn StmtOut WitOut
  verifier : Verifier m pSpec roles StmtIn

/-- A proof system: a reduction with no witness/statement output. -/
abbrev Proof (m : Type → Type) (pSpec : Spec) (roles : RoleDecoration pSpec)
    (StmtIn WitIn : Type) :=
  Reduction m pSpec roles StmtIn WitIn PUnit PUnit

/-! ## Execution -/

/-- Execute a reduction: run the prover's strategy against the verifier's
counterpart, then apply the decision function. Returns the transcript, the
verifier's decision, and the prover's output. -/
def Reduction.execute {m : Type → Type} [Monad m]
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {StmtIn WitIn StmtOut WitOut : Type}
    (r : Reduction m pSpec roles StmtIn WitIn StmtOut WitOut)
    (stmt : StmtIn) (wit : WitIn) :
    m ((_ : Spec.Transcript pSpec) × Bool × StmtOut × WitOut) := do
  let ⟨tr, stmtOut, witOut⟩ ←
    Spec.Strategy.runWithRoles pSpec roles (r.prover.run stmt wit) r.verifier.challenger
  let b ← r.verifier.decide stmt tr
  return ⟨tr, b, stmtOut, witOut⟩

/-! ## Sequential composition (TODO: Strategy.comp and Reduction.comp) -/

end Interaction
