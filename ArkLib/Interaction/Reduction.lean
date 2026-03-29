/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.TwoParty.Compose

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

universe u

namespace Interaction

/-! ## Protocol participants -/

/-- A prover: given `(s, w : WitnessIn)`, performs monadic setup and produces a
role-dependent strategy whose output is `WitnessOut s tr`. -/
abbrev Prover (m : Type u → Type u)
    (StatementIn WitnessIn : Type u)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u) :=
  (s : StatementIn) → WitnessIn →
    m (Spec.Strategy.withRoles m (Context s) (Roles s) (fun tr => WitnessOut s tr))

/-- A verifier: given statement `s`, provides a `Counterpart` with
`StatementOut s tr` at `.done`. No `OptionT` wrapping — the caller chooses
whether `StatementOut` includes `Option` for accept/reject semantics. -/
abbrev Verifier (m : Type u → Type u)
    (StatementIn : Type u)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u) :=
  (s : StatementIn) → Spec.Counterpart m (Context s) (Roles s)
    (fun tr => StatementOut s tr)

/-- A reduction pairs a prover with a verifier for the same protocol. -/
structure Reduction (m : Type u → Type u)
    (StatementIn WitnessIn : Type u)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u)
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u) where
  prover : Prover m StatementIn WitnessIn Context Roles WitnessOut
  verifier : Verifier m StatementIn Context Roles StatementOut

/-- A proof system is a reduction where the prover does not forward any
witness to the next stage (`WitnessOut = PUnit`). Accept/reject semantics
are not fixed here — they are determined by the choice of `StatementOut`
(e.g., `Bool`, `Option _`) and the security definitions. -/
abbrev Proof (m : Type u → Type u)
    (StatementIn WitnessIn : Type u)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u) :=
  Reduction m StatementIn WitnessIn Context Roles StatementOut (fun _ _ => PUnit)

/-! ## Execution -/

/-- Execute a reduction: run the prover's strategy against the verifier's
counterpart (via `Strategy.runWithRoles`). Returns the transcript, the
prover's output (`WitnessOut`), and the verifier's output (`StatementOut`). -/
def Reduction.execute {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u}
    (reduction : Reduction m StatementIn WitnessIn Context Roles StatementOut WitnessOut)
    (stmt : StatementIn) (wit : WitnessIn) :
    m ((tr : Spec.Transcript (Context stmt)) ×
       WitnessOut stmt tr × StatementOut stmt tr) := do
  let strategy ← reduction.prover stmt wit
  Spec.Strategy.runWithRoles (Context stmt) (Roles stmt) strategy (reduction.verifier stmt)

/-- Run a prover strategy against a verifier. Convenience wrapper around
`Spec.Strategy.runWithRoles` that applies the statement-indexed verifier. -/
def Verifier.run {m : Type u → Type u} [Monad m]
    {StatementIn : Type u}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u}
    (v : Verifier m StatementIn Context Roles StatementOut)
    (s : StatementIn)
    {OutputP : Spec.Transcript (Context s) → Type u}
    (prover : Spec.Strategy.withRoles m (Context s) (Roles s) OutputP) :
    m ((tr : Spec.Transcript (Context s)) × OutputP tr × StatementOut s tr) :=
  Spec.Strategy.runWithRoles (Context s) (Roles s) prover (v s)

/-! ## Sequential composition -/

/-- Compose a reduction with a second-phase prover and verifier (factored interface).
The first reduction runs over `ctx₁`, producing intermediate outputs `StmtMid` and
`WitMid`. These feed into second-phase components whose protocol `ctx₂`
may depend on the first transcript. The composed output types are given as
factored two-argument families, lifted through `Transcript.liftAppend`.

The second phase is given as separate prover/verifier components (rather than
a full `Reduction`) because a `Reduction` indexes its context by `StatementIn`,
whereas here the second context depends on `(s, tr₁)` — a transcript-level
dependency that can't be captured by the `Reduction` type alone. -/
def Reduction.comp {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {StmtMid WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type u}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {StmtOut WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type u}
    (r₁ : Reduction m StatementIn WitnessIn ctx₁ roles₁ StmtMid WitMid)
    (prover₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      WitMid s tr₁ →
        m (Spec.Strategy.withRoles m (ctx₂ s tr₁) (roles₂ s tr₁) (WitOut s tr₁)))
    (verifier₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      StmtMid s tr₁ →
        Spec.Counterpart m (ctx₂ s tr₁) (roles₂ s tr₁) (StmtOut s tr₁)) :
    Reduction m StatementIn WitnessIn
      (fun s => (ctx₁ s).append (ctx₂ s))
      (fun s => (roles₁ s).append (roles₂ s))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s)) where
  prover s w := do
    let strat₁ ← r₁.prover s w
    Spec.Strategy.compWithRoles strat₁ (fun tr₁ wMid => prover₂ s tr₁ wMid)
  verifier s :=
    Spec.Counterpart.append (r₁.verifier s) (fun tr₁ sMid => verifier₂ s tr₁ sMid)

/-- Build a reduction over a chained protocol from per-stage prover and verifier
steps, with stage-dependent output families. At each stage the prover
transforms `ProverFamily i st` and the verifier transforms `VerifierFamily i st`.
The full chain outputs are computed by `Transcript.chainFamily`. -/
def Reduction.ofChain {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {Stage : Nat → Type u}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {ProverFamily VerifierFamily : (i : Nat) → Stage i → Type u}
    (n : Nat)
    (initStage : StatementIn → Stage 0)
    (proverInit : (s : StatementIn) → WitnessIn → m (ProverFamily 0 (initStage s)))
    (proverStep : (i : Nat) → (st : Stage i) → ProverFamily i st →
      m (Spec.Strategy.withRoles m (spec i st) (roles i st)
        (fun tr => ProverFamily (i + 1) (advance i st tr))))
    (verifierInit : (s : StatementIn) → VerifierFamily 0 (initStage s))
    (verifierStep : (i : Nat) → (st : Stage i) → VerifierFamily i st →
      Spec.Counterpart m (spec i st) (roles i st)
        (fun tr => VerifierFamily (i + 1) (advance i st tr))) :
    Reduction m StatementIn WitnessIn
      (fun s => Spec.chain Stage spec advance n 0 (initStage s))
      (fun s => RoleDecoration.chain roles n 0 (initStage s))
      (fun s => Spec.Transcript.chainFamily VerifierFamily n 0 (initStage s))
      (fun s => Spec.Transcript.chainFamily ProverFamily n 0 (initStage s)) where
  prover s w := do
    let a ← proverInit s w
    Spec.Strategy.chainCompWithRoles proverStep n 0 (initStage s) a
  verifier s :=
    Spec.Counterpart.chainComp verifierStep n 0 (initStage s) (verifierInit s)

/-- Uniform `Reduction.ofChain` with fixed prover state `α` and verifier state `β`. -/
def Reduction.ofChainUniform {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {Stage : Nat → Type u}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {α β : Type u}
    (n : Nat)
    (initStage : StatementIn → Stage 0)
    (proverInit : StatementIn → WitnessIn → m α)
    (proverStep : (i : Nat) → (st : Stage i) → α →
      m (Spec.Strategy.withRoles m (spec i st) (roles i st) (fun _ => α)))
    (verifierInit : StatementIn → β)
    (verifierStep : (i : Nat) → (st : Stage i) → β →
      Spec.Counterpart m (spec i st) (roles i st) (fun _ => β)) :
    Reduction m StatementIn WitnessIn
      (fun s => Spec.chain Stage spec advance n 0 (initStage s))
      (fun s => RoleDecoration.chain roles n 0 (initStage s))
      (fun _ _ => β) (fun _ _ => α) where
  prover s w := do
    let a ← proverInit s w
    Spec.Strategy.chainCompWithRolesUniform proverStep n 0 (initStage s) a
  verifier s :=
    Spec.Counterpart.chainCompUniform verifierStep n 0 (initStage s) (verifierInit s)

end Interaction
