/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.TwoParty.Decoration
import ArkLib.Interaction.TwoParty.Strategy

/-!
# Provers, Verifiers, and Reductions

Interactive protocol participants and their composition, built on `Spec` with
a `RoleDecoration`. The type architecture uses:

- `StatementIn` — the input statement type
- `WitnessIn` — the input witness type (plain, no dependency on `StatementIn`)
- `Context : StatementIn → Spec` — protocol spec depends on statement
- `Roles : (s : StatementIn) → RoleDecoration (Context s)` — roles per statement
- `StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type`
- `WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type`

Input and output are plain products:
- **Input**: `StatementIn × WitnessIn`
- **Output**: `StatementOut s tr × WitnessOut s tr`

## Participants

- **Prover**: monadic setup producing a role-dependent `Strategy` with
  `WitnessOut` output.
- **Verifier**: a statement-indexed `Counterpart` with `StatementOut` at
  `.done`. No `OptionT` — acceptance semantics (if needed) are chosen by the
  caller through the `StatementOut` type (e.g., `StatementOut = fun _ _ => Option Bool`).
- **Reduction**: pairs a prover with a verifier for the same protocol spec.

Both `Prover` and `Verifier` are `abbrev`s (transparent type aliases) for
the underlying function types.

## Running a reduction

`Reduction.execute` runs the prover's strategy against the verifier (via
`Strategy.runWithRoles`), returning the transcript plus both outputs.
-/

namespace Interaction

variable {m : Type → Type}

/-! ## Protocol participants -/

/-- A prover: given `(s, w : WitnessIn)`, performs monadic setup and produces a
role-dependent strategy whose output is `WitnessOut s tr`. -/
abbrev Prover (m : Type → Type)
    (StatementIn WitnessIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) :=
  (s : StatementIn) → WitnessIn →
    m (Spec.Strategy.withRoles m (Context s) (Roles s) (fun tr => WitnessOut s tr))

/-- A verifier: given statement `s`, provides a `Counterpart` with
`StatementOut s tr` at `.done`. No `OptionT` wrapping — the caller chooses
whether `StatementOut` includes `Option` for accept/reject semantics. -/
abbrev Verifier (m : Type → Type)
    (StatementIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) :=
  (s : StatementIn) → Spec.Counterpart m (Context s) (Roles s)
    (fun tr => StatementOut s tr)

/-- A reduction pairs a prover with a verifier for the same protocol. -/
structure Reduction (m : Type → Type)
    (StatementIn WitnessIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type)
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) where
  prover : Prover m StatementIn WitnessIn Context Roles WitnessOut
  verifier : Verifier m StatementIn Context Roles StatementOut

/-- A proof system: a reduction with trivial witness output. -/
abbrev Proof (m : Type → Type)
    (StatementIn WitnessIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) :=
  Reduction m StatementIn WitnessIn Context Roles StatementOut (fun _ _ => PUnit)

/-! ## Execution -/

/-- Execute a reduction: run the prover's strategy against the verifier's
counterpart (via `Strategy.runWithRoles`). Returns the transcript, the
prover's output (`WitnessOut`), and the verifier's output (`StatementOut`). -/
def Reduction.execute {m : Type → Type} [Monad m]
    {StatementIn WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : Reduction m StatementIn WitnessIn Context Roles StatementOut WitnessOut)
    (stmt : StatementIn) (wit : WitnessIn) :
    m ((tr : Spec.Transcript (Context stmt)) ×
       WitnessOut stmt tr × StatementOut stmt tr) := do
  let strategy ← reduction.prover stmt wit
  Spec.Strategy.runWithRoles (Context stmt) (Roles stmt) strategy (reduction.verifier stmt)

/-- Run a prover strategy against a verifier. Convenience wrapper around
`Spec.Strategy.runWithRoles` that applies the statement-indexed verifier. -/
def Verifier.run {m : Type → Type} [Monad m]
    {StatementIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (v : Verifier m StatementIn Context Roles StatementOut)
    (s : StatementIn)
    {OutputP : Spec.Transcript (Context s) → Type}
    (prover : Spec.Strategy.withRoles m (Context s) (Roles s) OutputP) :
    m ((tr : Spec.Transcript (Context s)) × OutputP tr × StatementOut s tr) :=
  Spec.Strategy.runWithRoles (Context s) (Roles s) prover (v s)

/-! ## Sequential composition (TODO: Strategy.comp and Reduction.comp) -/

end Interaction
