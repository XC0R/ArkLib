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

Input and output are represented as:
- **Input**: `StatementIn × WitnessIn`
- **Honest prover output**: `HonestProverOutput (StatementOut s tr) (WitnessOut s tr)`

## Participants

- **Prover**: monadic setup producing a role-dependent `Strategy` whose output is
  `HonestProverOutput StatementOut WitnessOut`.
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

universe u v

namespace Interaction

/-! ## Protocol participants -/

/-- Output produced by an honest prover: the next statement together with the
next witness to be forwarded by composition. -/
abbrev HonestProverOutput (StatementOut : Type u) (WitnessOut : Type v) :=
  StatementOut × WitnessOut

namespace HonestProverOutput

/-- Statement component of an honest prover output. -/
abbrev stmt {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : StatementOut :=
  out.1

/-- Witness component of an honest prover output. -/
abbrev wit {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : WitnessOut :=
  out.2

end HonestProverOutput

/-- A prover: given `(s, w : WitnessIn)`, performs monadic setup and produces a
role-dependent strategy whose output is
`HonestProverOutput (StatementOut s tr) (WitnessOut s tr)`. -/
abbrev Prover (m : Type u → Type u)
    (StatementIn WitnessIn : Type u)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u) :=
  (s : StatementIn) → WitnessIn →
    m (Spec.Strategy.withRoles m (Context s) (Roles s)
      (fun tr => HonestProverOutput (StatementOut s tr) (WitnessOut s tr)))

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
  prover : Prover m StatementIn WitnessIn Context Roles StatementOut WitnessOut
  verifier : Verifier m StatementIn Context Roles StatementOut

/-- A proof system is a reduction where the prover does not forward any
witness to the next stage (`WitnessOut = PUnit`). Accept/reject semantics
are not fixed here — they are determined by the choice of `StatementOut`
(e.g., `Bool`, `Option _`) and the security definitions. Its honest prover
output is `HonestProverOutput StatementOut PUnit`. -/
abbrev Proof (m : Type u → Type u)
    (StatementIn WitnessIn : Type u)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u) :=
  Reduction m StatementIn WitnessIn Context Roles StatementOut (fun _ _ => PUnit)

/-! ## Execution -/

/-- Execute a reduction: run the prover's strategy against the verifier's
counterpart (via `Strategy.runWithRoles`). Returns the transcript, the
 prover's output (`HonestProverOutput StatementOut WitnessOut`), and the verifier's output
 (`StatementOut`). -/
def Reduction.execute {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u}
    (reduction : Reduction m StatementIn WitnessIn Context Roles StatementOut WitnessOut)
    (stmt : StatementIn) (wit : WitnessIn) :
    m ((tr : Spec.Transcript (Context stmt)) ×
       HonestProverOutput (StatementOut stmt tr) (WitnessOut stmt tr) ×
         StatementOut stmt tr) := do
  let strategy ← reduction.prover stmt wit
  Spec.Strategy.runWithRoles (Context stmt) (Roles stmt) strategy (reduction.verifier stmt)

/-- A continuation reduction over a shared input. The protocol context depends on the
shared input, while the honest prover and verifier additionally receive their own
private local state. This is the right shape for transcript-indexed second-stage
composition, where both parties agree on the transcript but only each side knows
its own carried state. -/
structure Reduction.Continuation (m : Type u → Type u)
    (SharedIn : Type u)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (StatementIn WitnessIn : (shared : SharedIn) → Type u)
    (StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u) where
  prover : (shared : SharedIn) → StatementIn shared → WitnessIn shared →
    m (Spec.Strategy.withRoles m (Context shared) (Roles shared)
      (fun tr => HonestProverOutput (StatementOut shared tr) (WitnessOut shared tr)))
  verifier : (shared : SharedIn) → StatementIn shared →
    Spec.Counterpart m (Context shared) (Roles shared) (fun tr => StatementOut shared tr)

/-- Execute a continuation reduction on a shared input together with the verifier
and prover local states. -/
def Reduction.Continuation.execute {m : Type u → Type u} [Monad m]
    {SharedIn : Type u}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : (shared : SharedIn) → Type u}
    {StatementOut WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (reduction : Reduction.Continuation m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut)
    (shared : SharedIn) (stmt : StatementIn shared) (wit : WitnessIn shared) :
    m ((tr : Spec.Transcript (Context shared)) ×
      HonestProverOutput (StatementOut shared tr) (WitnessOut shared tr) ×
        StatementOut shared tr) := do
  let strategy ← reduction.prover shared stmt wit
  Spec.Strategy.runWithRoles (Context shared) (Roles shared) strategy
    (reduction.verifier shared stmt)

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

/-- Compose a reduction with a transcript-indexed continuation reduction.
The first reduction runs over `ctx₁`, producing intermediate outputs `StmtMid` and
`WitMid`. These feed into `reduction2`, whose protocol `ctx₂` may depend on the
first transcript. The composed output types are factored two-argument families,
lifted through `Transcript.liftAppend`. -/
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
    (reduction1 : Reduction m StatementIn WitnessIn ctx₁ roles₁ StmtMid WitMid)
    (reduction2 : Reduction.Continuation m
      ((s : StatementIn) × Spec.Transcript (ctx₁ s))
      (fun shared => ctx₂ shared.1 shared.2)
      (fun shared => roles₂ shared.1 shared.2)
      (fun shared => StmtMid shared.1 shared.2)
      (fun shared => WitMid shared.1 shared.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2 tr₂)) :
    Reduction m StatementIn WitnessIn
      (fun s => (ctx₁ s).append (ctx₂ s))
      (fun s => (roles₁ s).append (roles₂ s))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s)) where
  prover s w := do
    let strat₁ ← reduction1.prover s w
    let strat ← Spec.Strategy.compWithRoles strat₁ (fun tr₁ midOut =>
      reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        Spec.Transcript.liftAppendProd (ctx₁ s) (ctx₂ s) (StmtOut s) (WitOut s) tr out)
      strat
  verifier s :=
    Spec.Counterpart.append (reduction1.verifier s) (fun tr₁ sMid =>
      reduction2.verifier ⟨s, tr₁⟩ sMid)

/-- Executing a sequentially composed reduction factors into first executing the
prefix reduction and then the suffix interaction induced by its outputs. -/
theorem Reduction.execute_comp
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {StatementIn WitnessIn : Type u}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {StmtMid WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type u}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {StmtOut WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type u}
    (reduction1 : Reduction m StatementIn WitnessIn ctx₁ roles₁ StmtMid WitMid)
    (reduction2 : Reduction.Continuation m
      ((s : StatementIn) × Spec.Transcript (ctx₁ s))
      (fun shared => ctx₂ shared.1 shared.2)
      (fun shared => roles₂ shared.1 shared.2)
      (fun shared => StmtMid shared.1 shared.2)
      (fun shared => WitMid shared.1 shared.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2 tr₂))
    (s : StatementIn) (w : WitnessIn) :
    (Reduction.comp reduction1 reduction2).execute s w =
      (do
        let ⟨tr₁, midOut, sMid⟩ ← reduction1.execute s w
        let strat₂ ← reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit
        let ⟨tr₂, out, sOut⟩ ←
          Spec.Strategy.runWithRoles (ctx₂ s tr₁) (roles₂ s tr₁) strat₂
            (reduction2.verifier ⟨s, tr₁⟩ sMid)
        pure ⟨Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂,
          ⟨Spec.Transcript.packAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr₁ tr₂ out.stmt,
            Spec.Transcript.packAppend (ctx₁ s) (ctx₂ s) (WitOut s) tr₁ tr₂ out.wit⟩,
          Spec.Transcript.packAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr₁ tr₂ sOut⟩) := by
  simp only [execute, comp, bind_assoc, pure_bind]
  refine congrArg (fun k => reduction1.prover s w >>= k) ?_
  funext strat₁
  let mapOut :
      (tr : Spec.Transcript ((ctx₁ s).append (ctx₂ s))) →
      Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s)
        (fun tr₁ tr₂ => HonestProverOutput (StmtOut s tr₁ tr₂) (WitOut s tr₁ tr₂)) tr →
      HonestProverOutput
        (Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr)
        (Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s) tr) :=
    fun tr out =>
      Spec.Transcript.liftAppendProd (ctx₁ s) (ctx₂ s) (StmtOut s) (WitOut s) tr out
  let mapTriple :
      ((tr : Spec.Transcript ((ctx₁ s).append (ctx₂ s))) ×
        Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s)
          (fun tr₁ tr₂ => HonestProverOutput (StmtOut s tr₁ tr₂) (WitOut s tr₁ tr₂)) tr ×
        Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr) →
      ((tr : Spec.Transcript ((ctx₁ s).append (ctx₂ s))) ×
        HonestProverOutput
          (Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr)
          (Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s) tr) ×
        Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr) :=
    fun z => ⟨z.1, mapOut z.1 z.2.1, z.2.2⟩
  have hmap :
      (do
        let strat ← Spec.Strategy.compWithRoles strat₁
          (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
        Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
          (Spec.Strategy.mapOutputWithRoles mapOut strat)
          (Spec.Counterpart.append (reduction1.verifier s)
            (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) =
        mapTriple <$>
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
            Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
              strat
              (Spec.Counterpart.append (reduction1.verifier s)
                (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) := by
    have hraw :
        (do
          let strat ← Spec.Strategy.compWithRoles strat₁
            (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
          Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
            (Spec.Strategy.mapOutputWithRoles mapOut strat)
            (Spec.Counterpart.append (reduction1.verifier s)
              (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) =
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
                strat
                (Spec.Counterpart.append (reduction1.verifier s)
                  (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) := by
      refine congrArg
        (fun k =>
          Spec.Strategy.compWithRoles strat₁
            (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit) >>= k) ?_
      funext strat
      simpa [mapTriple, mapOut, Spec.Counterpart.mapOutput_id] using
        (Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput
          (fP := mapOut) (fC := fun _ x => x) strat
          (Spec.Counterpart.append (reduction1.verifier s)
            (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid)))
    calc
      (do
        let strat ← Spec.Strategy.compWithRoles strat₁
          (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
        Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
          (Spec.Strategy.mapOutputWithRoles mapOut strat)
          (Spec.Counterpart.append (reduction1.verifier s)
            (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) =
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
                strat
                (Spec.Counterpart.append (reduction1.verifier s)
                  (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) := hraw
      _ = mapTriple <$>
            (do
              let strat ← Spec.Strategy.compWithRoles strat₁
                (fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
              Spec.Strategy.runWithRoles ((ctx₁ s).append (ctx₂ s)) ((roles₁ s).append (roles₂ s))
                strat
                (Spec.Counterpart.append (reduction1.verifier s)
                  (fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))) := by
        simp
  rw [hmap]
  simpa [mapTriple, mapOut, bind_assoc] using
    congrArg (fun mx => mapTriple <$> mx)
      (Spec.Strategy.runWithRoles_compWithRoles_append
        (strat₁ := strat₁)
        (f := fun tr₁ midOut => reduction2.prover ⟨s, tr₁⟩ midOut.stmt midOut.wit)
        (cpt₁ := reduction1.verifier s)
        (cpt₂ := fun tr₁ sMid => reduction2.verifier ⟨s, tr₁⟩ sMid))

/-- Compose per-stage prover and verifier step functions into a reduction over
a chained protocol `Spec.stateChain Stage spec advance n`.

The prover and verifier each carry evolving state through the state chain:
- `ProverState i st` is the prover's state at stage `i` with state chain state `st`.
  Initialized from the witness via `proverInit`, then transformed at each stage
  by `proverStep`. The terminal prover state becomes `WitnessOut`.
- `VerifierState i st` is the verifier's state at stage `i`.
  Initialized from the statement via `verifierInit`, then transformed by
  `verifierStep`. The terminal verifier state becomes `StatementOut`.

Both output types are computed as `Transcript.stateChainFamily` of the respective
state families. -/
def Reduction.stateChainComp {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {Stage : Nat → Type u}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {ProverState VerifierState : (i : Nat) → Stage i → Type u}
    (n : Nat)
    (initStage : StatementIn → Stage 0)
    (proverInit : (s : StatementIn) → WitnessIn → m (ProverState 0 (initStage s)))
    (proverStep : (i : Nat) → (st : Stage i) → ProverState i st →
      m (Spec.Strategy.withRoles m (spec i st) (roles i st)
        (fun tr => ProverState (i + 1) (advance i st tr))))
    (stmtResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      Spec.Transcript.stateChainFamily VerifierState n 0 (initStage s) tr)
    (verifierInit : (s : StatementIn) → VerifierState 0 (initStage s))
    (verifierStep : (i : Nat) → (st : Stage i) → VerifierState i st →
      Spec.Counterpart m (spec i st) (roles i st)
        (fun tr => VerifierState (i + 1) (advance i st tr))) :
    Reduction m StatementIn WitnessIn
      (fun s => Spec.stateChain Stage spec advance n 0 (initStage s))
      (fun s => RoleDecoration.stateChain roles n 0 (initStage s))
      (fun s => Spec.Transcript.stateChainFamily VerifierState n 0 (initStage s))
      (fun s => Spec.Transcript.stateChainFamily ProverState n 0 (initStage s)) where
  prover s w := do
    let a ← proverInit s w
    let strat ← Spec.Strategy.stateChainCompWithRoles proverStep n 0 (initStage s) a
    pure <| Spec.Strategy.mapOutputWithRoles (fun tr pOut => ⟨stmtResult s tr, pOut⟩) strat
  verifier s :=
    Spec.Counterpart.stateChainComp verifierStep n 0 (initStage s) (verifierInit s)

/-- Uniform `Reduction.stateChainComp` with fixed prover state `α` and verifier
state `β` at every stage. -/
def Reduction.stateChainCompUniform {m : Type u → Type u} [Monad m]
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
    (stmtResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) → β)
    (verifierInit : StatementIn → β)
    (verifierStep : (i : Nat) → (st : Stage i) → β →
      Spec.Counterpart m (spec i st) (roles i st) (fun _ => β)) :
    Reduction m StatementIn WitnessIn
      (fun s => Spec.stateChain Stage spec advance n 0 (initStage s))
      (fun s => RoleDecoration.stateChain roles n 0 (initStage s))
      (fun _ _ => β) (fun _ _ => α) where
  prover s w := do
    let a ← proverInit s w
    let strat ← Spec.Strategy.stateChainCompWithRolesUniform proverStep n 0 (initStage s) a
    pure <| Spec.Strategy.mapOutputWithRoles (fun tr a' => ⟨stmtResult s tr, a'⟩) strat
  verifier s :=
    Spec.Counterpart.stateChainCompUniform verifierStep n 0 (initStage s) (verifierInit s)

/-! ## Chain-based (stateless) reduction composition

Reduction composition over an `n`-round protocol described by `Spec.Chain`,
with **no prover state, no verifier state, and no round index family**.

Each participant provides a per-round step that receives the remaining
`Chain` and produces the strategy/counterpart for the current round.
The remaining chain implicitly encodes prior transcript context
(since it was obtained by applying prior transcripts to the original
continuation). No state flows between rounds (per-round outputs are `PUnit`).
The final `StatementOut` and `WitnessOut` are computed from the full
transcript via caller-supplied result functions. -/

namespace Spec

/-- Build a `Decoration S` for `Chain.toSpec n c` from per-round decorators.
At each level, the decorator receives the remaining `Chain` and
produces the decoration for the current round's spec. -/
def Decoration.ofChain {S : Type u → Type v}
    (decoAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → Decoration S rem.1) :
    (n : Nat) → (c : Chain.{u} n) → Decoration S (Chain.toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, cont⟩ =>
      Decoration.append (decoAt ⟨spec, cont⟩)
        (fun tr => Decoration.ofChain decoAt n (cont tr))

namespace Chain

/-- Build a `RoleDecoration` for the full spec from per-round role
assignments. Specializes `Decoration.ofChain` to `fun _ => Role`. -/
abbrev roles
    (rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1) :
    (n : Nat) → (c : Chain.{u} n) → RoleDecoration (Chain.toSpec n c) :=
  Decoration.ofChain rolesAt

end Chain

/-- Compose per-round prover strategies into a full strategy over the
chain. Each round's step receives the remaining `Chain` and
produces the strategy for that round's spec. Output is `PUnit` — no
state flows between rounds. -/
def Strategy.ofChain {m : Type u → Type u} [Monad m]
    {rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1}
    (step : {k : Nat} → (rem : Chain.{u} (k + 1)) →
      m (Strategy.withRoles m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1}))) :
    (n : Nat) → (c : Chain.{u} n) →
    m (Strategy.withRoles m (Chain.toSpec n c)
      (Decoration.ofChain rolesAt n c) (fun _ => PUnit.{u + 1}))
  | 0, _ => pure ⟨⟩
  | n + 1, ⟨spec, cont⟩ => do
    let strat ← step ⟨spec, cont⟩
    @Strategy.compWithRolesFlat m _ spec (fun tr => Chain.toSpec n (cont tr))
      (rolesAt ⟨spec, cont⟩) (fun tr => Decoration.ofChain rolesAt n (cont tr))
      (fun _ => PUnit.{u + 1}) (fun _ => PUnit.{u + 1})
      strat (fun tr _ => Strategy.ofChain step n (cont tr))

/-- Compose per-round verifier counterparts into a full counterpart over
the chain. Each round's step receives the remaining `Chain` and
produces the counterpart for that round's spec. Output is `PUnit`. -/
def Counterpart.ofChain {m : Type u → Type u} [Monad m]
    {rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1}
    (step : {k : Nat} → (rem : Chain.{u} (k + 1)) →
      Counterpart m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1})) :
    (n : Nat) → (c : Chain.{u} n) →
    Counterpart m (Chain.toSpec n c)
      (Decoration.ofChain rolesAt n c) (fun _ => PUnit.{u + 1})
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, cont⟩ =>
    @Counterpart.appendFlat m _ spec (fun tr => Chain.toSpec n (cont tr))
      (rolesAt ⟨spec, cont⟩) (fun tr => Decoration.ofChain rolesAt n (cont tr))
      (fun _ => PUnit.{u + 1}) (fun _ => PUnit.{u + 1})
      (step ⟨spec, cont⟩)
      (fun tr _ => Counterpart.ofChain step n (cont tr))

end Spec

/-- Compose per-round prover and verifier steps into a full `Reduction`
over an `n`-round `Chain`. No `ProverState`, `VerifierState`, or
round index family. Per-round steps produce `PUnit` — no state flows
between rounds. The final `StatementOut` and `WitnessOut` are computed
from the full transcript via `stmtResult` and `witResult`. -/
def Reduction.ofChain {m : Type u → Type u} [Monad m]
    {StatementIn WitnessIn : Type u}
    {n : Nat}
    {c : StatementIn → Spec.Chain.{u} n}
    {rolesAt : {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) → RoleDecoration rem.1}
    {StatementOut WitnessOut : (s : StatementIn) →
      Spec.Transcript (Spec.Chain.toSpec n (c s)) → Type u}
    (proverRound : (s : StatementIn) → WitnessIn →
      {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) →
        m (Spec.Strategy.withRoles m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1})))
    (verifierRound : (s : StatementIn) →
      {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) →
        Spec.Counterpart m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1}))
    (witResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c s))) → WitnessOut s tr)
    (stmtResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c s))) → StatementOut s tr) :
    Reduction m StatementIn WitnessIn
      (fun s => Spec.Chain.toSpec n (c s))
      (fun s => Spec.Decoration.ofChain rolesAt n (c s))
      StatementOut WitnessOut where
  prover s w := do
    let strat ← Spec.Strategy.ofChain (rolesAt := rolesAt) (proverRound s w) n (c s)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr _ => ⟨stmtResult s tr, witResult s tr⟩) strat
  verifier s :=
    Spec.Counterpart.mapOutput (fun tr _ => stmtResult s tr)
      (Spec.Counterpart.ofChain (rolesAt := rolesAt) (verifierRound s) n (c s))

end Interaction
