/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

open OracleComp OracleSpec

namespace Interaction

namespace OracleDecoration

/-! ## Composition infrastructure

To compose oracle reductions, we need that `toMonadDecoration` distributes over
`Spec.append` and `Spec.stateChain`. The accumulated oracle spec after the first phase
serves as the starting spec for the second phase. -/

/-- Lift a transcript-split oracle index family to the fused append transcript. -/
private abbrev liftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) :
    Spec.Transcript (spec₁.append spec₂) → Type :=
  Spec.Transcript.liftAppendFamily spec₁ spec₂ ιₛ

/-- Lift a transcript-split oracle statement family to the fused append
transcript. -/
private abbrev liftAppendOracleFamily
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) :
    (tr : Spec.Transcript (spec₁.append spec₂)) → liftAppendOracleIdx spec₁ spec₂ ιₛ tr → Type :=
  fun tr =>
    let split := Spec.Transcript.split spec₁ spec₂ tr
    OStmt split.1 split.2

/-- Pack an oracle-family index from the split append view into the fused append
view. -/
private def packLiftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i : ιₛ tr₁ tr₂) :
    liftAppendOracleIdx spec₁ spec₂ ιₛ (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) :=
  cast (Eq.symm <| Spec.Transcript.liftAppendFamily_append spec₁ spec₂ ιₛ tr₁ tr₂) i

/-- Unpack an oracle-family index on the fused append transcript back to the
split append view. -/
private def unpackLiftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i : liftAppendOracleIdx spec₁ spec₂ ιₛ (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)) :
    ιₛ tr₁ tr₂ :=
  cast (Spec.Transcript.liftAppendFamily_append spec₁ spec₂ ιₛ tr₁ tr₂) i

/-- Pack a query to the split append oracle family into a query to the fused
append oracle family. -/
private def packLiftAppendOracleQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i : ιₛ tr₁ tr₂) (q : OracleInterface.Query (OStmt tr₁ tr₂ i)) :
    ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain := by
  simpa [OracleInterface.toOracleSpec, liftAppendOracleFamily, liftAppendOracleIdx] using
    (cast
      (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
        (Eq.symm <| Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
      (show ([OStmt tr₁ tr₂]ₒ).Domain from ⟨i, q⟩))

/-- Unpack a query to the fused append oracle family back to a query to the split
append oracle family. -/
private def unpackLiftAppendOracleQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain) :
    ([OStmt tr₁ tr₂]ₒ).Domain := by
  simpa [OracleInterface.toOracleSpec, liftAppendOracleFamily, liftAppendOracleIdx] using
    (cast
      (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
        (Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
      qOut)

/-- Accumulated oracle spec after traversing `spec` along transcript `tr`,
starting from `accSpec`. At sender nodes, adds the node's oracle interface spec.
At receiver nodes, the accumulated spec is unchanged. -/
def accSpecAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Spec.Transcript spec →
    Σ (ιₐ' : Type), OracleSpec ιₐ'
  | .done, _, _, _, accSpec, _ => ⟨_, accSpec⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odRest x)
        (accSpec + @OracleInterface.spec _ oi) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odFn x) accSpec trRest

/-- Concrete implementation of the accumulated sender-message oracle spec after
traversing a transcript. -/
def accImplAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) → QueryImpl accSpec Id →
    (tr : Spec.Transcript spec) →
    QueryImpl ((accSpecAfter spec roles od accSpec tr).2) Id
  | .done, _, _, _, _, accImpl, _ => accImpl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, accImpl, ⟨x, trRest⟩ =>
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id := fun q => (oi.toOC.impl q).run x
      accImplAfter (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, accImpl, ⟨x, trRest⟩ =>
      accImplAfter (rest x) (rRest x) (odFn x) accSpec accImpl trRest

private def runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) → QueryImpl accSpec Id →
    {OutputP OutputC : Spec.Transcript spec → Type} →
    Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC →
    OracleComp oSpec ((tr : Spec.Transcript spec) × OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, accImpl, OutputP, OutputC,
      ⟨x, cont⟩, dualFn => do
      let next ← cont
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id := fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      let tail := z.1
      let outP := z.2.1
      let outC := z.2.2
      return ⟨⟨x, tail⟩, outP, outC⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, accImpl, OutputP, OutputC,
      respond, dualSample => do
      let routeImpl :
          QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (query (spec := oSpec) q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have dualSample' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using dualSample
      let z' : Sigma (fun x =>
          Spec.Counterpart.withMonads (rest x) (rRest x)
            (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec)
            (fun p => OutputC ⟨x, p⟩)) ←
        simulateQ routeImpl dualSample'
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odFn x) accSpec accImpl next dualRest
      let tail := z.1
      let outP := z.2.1
      let outC := z.2.2
      return ⟨⟨x, tail⟩, outP, outC⟩

namespace OracleReduction

/-- Run an arbitrary prover strategy against an oracle reduction's verifier and
package the resulting plain verifier output with transcript-dependent oracle
access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementWithOracles StatementIn OStmtIn)
    {OutputP : Spec.Transcript (Context s.stmt) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context s.stmt) (Roles s.stmt) OutputP) :
    OracleComp oSpec ((tr : Spec.Transcript (Context s.stmt)) × OutputP tr ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 OStmtIn s.oracleStmt)
      (Context s.stmt) (Roles s.stmt) (OD s.stmt) []ₒ (fun q => q.elim)
      prover (reduction.verifier s.stmt []ₒ)
  pure ⟨tr, outP, ⟨stmtOutV, reduction.simulate s.stmt tr⟩⟩

/-- Execute an oracle reduction honestly and package the verifier's plain output
with transcript-dependent oracle access semantics. -/
def execute
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn) :
    OracleComp oSpec ((tr : Spec.Transcript (Context s.stmt)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr))
        (WitnessOut s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) := do
  let strategy ← reduction.prover s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 OStmtIn s.oracleStmt)
      (Context s.stmt) (Roles s.stmt) (OD s.stmt) []ₒ (fun q => q.elim)
      strategy (reduction.verifier s.stmt []ₒ)
  pure ⟨tr, proverOut, ⟨stmtOutV, reduction.simulate s.stmt tr⟩⟩

end OracleReduction

/-- `toMonadDecoration` distributes over `Spec.append`: the monad decoration for
the appended spec equals `Decoration.append` of the individual monad decorations,
where the second phase starts from the accumulated oracle spec of the first. -/
theorem toMonadDecoration_append
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)] :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    toMonadDecoration oSpec OStmtIn (spec₁.append spec₂)
      (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂) accSpec =
    Spec.Decoration.append (toMonadDecoration oSpec OStmtIn spec₁ roles₁ od₁ accSpec)
      (fun tr₁ => toMonadDecoration oSpec OStmtIn (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁)
        (accSpecAfter spec₁ roles₁ od₁ accSpec tr₁).2)
  | .done, _, _, _, _, _, _, _ => rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨oi, odRest⟩, od₂, _, accSpec => by
      simp only [Spec.append, toMonadDecoration, Spec.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩) _
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, _, accSpec => by
      simp only [Spec.append, toMonadDecoration, Spec.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩) _

/-! ## Oracle reduction composition -/

namespace OracleReduction

/-- A continuation oracle reduction over a shared input. The protocol context
depends on the shared input, while the honest prover and verifier additionally
receive their own carried local state. The input and output oracle-statement
families are fixed across the continuation. -/
structure Continuation {ι : Type} (oSpec : OracleSpec ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : (shared : SharedIn) → Type}
    (OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type) where
  prover : (shared : SharedIn) →
    StatementWithOracles (StatementIn shared) (OStmtIn shared) → WitnessIn shared →
      OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared)
        (fun tr => HonestProverOutput
          (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr))
          (WitnessOut shared tr)))
  verifier : (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    StatementIn shared →
      Spec.Counterpart.withMonads (Context shared) (Roles shared)
        (toMonadDecoration oSpec (OStmtIn shared) (Context shared)
          (Roles shared) (OD shared) accSpec)
        (fun tr => StatementOut shared tr)
  simulate : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) →
    QueryImpl [OStmtOut shared tr]ₒ
      (OracleComp ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared) (OD shared) tr))

namespace Continuation

/-- The verifier-side monad decoration induced by an oracle continuation,
starting from an accumulated sender-message oracle spec `accSpec`. -/
abbrev verifierMD
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (_reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    Spec.MonadDecoration (Context shared) :=
  toMonadDecoration oSpec (OStmtIn shared) (Context shared) (Roles shared) (OD shared) accSpec

/-- Run an arbitrary prover strategy against an oracle continuation's verifier and
package the resulting plain verifier output with transcript-dependent oracle
access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    {OutputP : Spec.Transcript (Context shared) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared) OutputP)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) × OutputP tr ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (OD shared) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (OD shared) accSpec accImpl
      prover (reduction.verifier shared accSpec stmt)
  pure ⟨tr, outP, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

/-- Execute an oracle continuation honestly and package the verifier's plain
output with transcript-dependent oracle access semantics. -/
def execute
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles (StatementIn shared) (OStmtIn shared)) (w : WitnessIn shared)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr))
        (WitnessOut shared tr) ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (OD shared) tr)))) := do
  let strategy ← reduction.prover shared s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 (OStmtIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (OD shared) accSpec accImpl
      strategy (reduction.verifier shared accSpec s.stmt)
  pure ⟨tr, proverOut, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

end Continuation

private def compSimulate
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : Continuation oSpec
      ((s : StatementIn) × Spec.Transcript (ctx₁ s))
      (fun shared => ctx₂ shared.1 shared.2)
      (fun shared => roles₂ shared.1 shared.2)
      (fun shared => OD₂ shared.1 shared.2)
      (fun shared => StmtMid shared.1 shared.2)
      (fun shared => OStmtMid shared.1 shared.2)
      (fun shared => WitMid shared.1 shared.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => OStmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2 tr₂))
    (s : StatementIn) (tr : Spec.Transcript ((ctx₁ s).append (ctx₂ s))) :
    QueryImpl
      [liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr]ₒ
      (OracleComp ([OStmtIn]ₒ + toOracleSpec ((ctx₁ s).append (ctx₂ s))
        (Spec.Decoration.append (roles₁ s) (roles₂ s))
        (Role.Refine.append (OD₁ s) (fun tr₁ => OD₂ s tr₁)) tr)) := by
  sorry

/-- Binary sequential composition of oracle reductions. The first reduction runs
over `ctx₁`, producing intermediate outputs. The second reduction is a
continuation over the shared input `(s, tr₁)`, taking the intermediate bundled
oracle statement and witness as its local input. -/
def comp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : Continuation oSpec
      ((s : StatementIn) × Spec.Transcript (ctx₁ s))
      (fun shared => ctx₂ shared.1 shared.2)
      (fun shared => roles₂ shared.1 shared.2)
      (fun shared => OD₂ shared.1 shared.2)
      (fun shared => StmtMid shared.1 shared.2)
      (fun shared => OStmtMid shared.1 shared.2)
      (fun shared => WitMid shared.1 shared.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => OStmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2 tr₂)) :
    OracleReduction oSpec StatementIn OStmtIn WitnessIn
      (fun s => (ctx₁ s).append (ctx₂ s))
      (fun s => Spec.Decoration.append (roles₁ s) (roles₂ s))
      (fun s => Role.Refine.append (OD₁ s) (fun tr₁ => OD₂ s tr₁))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s))
      (fun s tr => liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr)
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s)) where
  prover sWithOracles w := do
    let strat₁ ← reduction1.prover sWithOracles w
    let strat ← Spec.Strategy.compWithRoles strat₁
      (fun tr₁ midOut =>
        reduction2.prover ⟨sWithOracles.stmt, tr₁⟩ midOut.stmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out => by
        let splitOuter := Spec.Transcript.liftAppendProd
          (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
          (fun tr₁ tr₂ =>
            StatementWithOracles (StmtOut sWithOracles.stmt tr₁ tr₂)
              (OStmtOut sWithOracles.stmt tr₁ tr₂))
          (WitOut sWithOracles.stmt) tr out
        let splitStmtOracle := Spec.Transcript.liftAppendProd
          (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
          (StmtOut sWithOracles.stmt)
          (fun tr₁ tr₂ => OracleStatement (OStmtOut sWithOracles.stmt tr₁ tr₂))
          tr splitOuter.1
        have oracleOut :
            OracleStatement
              (liftAppendOracleFamily (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
                (ιₛₒ sWithOracles.stmt) (OStmtOut sWithOracles.stmt) tr) := by
          simpa [liftAppendOracleFamily, liftAppendOracleIdx] using
            (Spec.Transcript.unliftAppend
              (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
              (fun tr₁ tr₂ =>
                OracleStatement (OStmtOut sWithOracles.stmt tr₁ tr₂))
              tr splitStmtOracle.2)
        exact ⟨⟨splitStmtOracle.1, oracleOut⟩, splitOuter.2⟩)
      strat
  verifier s {ιₐ} accSpec := by
    sorry
  simulate := compSimulate reduction1 reduction2

/-- If the prefix reduction's simulated oracle output agrees with `midImpl`, and
the suffix continuation's simulated oracle output agrees with `outImpl` when run
against `midImpl`, then the composed reduction's simulated oracle output agrees
with `outImpl` on the appended transcript. -/
theorem simulate_comp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : Continuation oSpec
      ((s : StatementIn) × Spec.Transcript (ctx₁ s))
      (fun shared => ctx₂ shared.1 shared.2)
      (fun shared => roles₂ shared.1 shared.2)
      (fun shared => OD₂ shared.1 shared.2)
      (fun shared => StmtMid shared.1 shared.2)
      (fun shared => OStmtMid shared.1 shared.2)
      (fun shared => WitMid shared.1 shared.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => OStmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2 tr₂))
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (oStmtIn : OracleStatement OStmtIn)
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id)
    (outImpl : QueryImpl [OStmtOut s tr₁ tr₂]ₒ Id)
    (hMid : ∀ i (q : OracleInterface.Query (OStmtMid s tr₁ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (OD₁ s) oStmtIn tr₁)
        (reduction1.simulate s tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩))
    (hOut : ∀ i (q : OracleInterface.Query (OStmtOut s tr₁ tr₂ i)),
      simulateQ
        (QueryImpl.add midImpl
          (OracleDecoration.answerQuery (ctx₂ s tr₁) (roles₂ s tr₁) (OD₂ s tr₁) tr₂))
        (reduction2.simulate ⟨s, tr₁⟩ tr₂ ⟨i, q⟩) = pure (outImpl ⟨i, q⟩)) :
    ∀ i (q : OracleInterface.Query (OStmtOut s tr₁ tr₂ i)),
      let qAppend :
          ([liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s)
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)]ₒ).Domain := by
        exact packLiftAppendOracleQuery (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr₁ tr₂ i q
      simulateQ
        (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
          oStmtIn
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        ((comp reduction1 reduction2).simulate s
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂) qAppend) =
      pure (cast (by
        sorry)
        (outImpl ⟨i, q⟩)) := by
  sorry

/-- Executing a sequentially composed oracle reduction factors into executing the
prefix reduction, then executing the suffix continuation under the accumulated
sender-message oracle implementation. -/
theorem execute_comp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : Continuation oSpec
      ((s : StatementIn) × Spec.Transcript (ctx₁ s))
      (fun shared => ctx₂ shared.1 shared.2)
      (fun shared => roles₂ shared.1 shared.2)
      (fun shared => OD₂ shared.1 shared.2)
      (fun shared => StmtMid shared.1 shared.2)
      (fun shared => OStmtMid shared.1 shared.2)
      (fun shared => WitMid shared.1 shared.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => OStmtOut shared.1 shared.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2 tr₂))
    (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn) :
    (comp reduction1 reduction2).execute s w =
      (do
        let ⟨tr₁, midOut, _midVerifierOut⟩ ← reduction1.execute s w
        let prefixAccSpec :=
          (accSpecAfter (ctx₁ s.stmt) (roles₁ s.stmt) (OD₁ s.stmt) []ₒ tr₁).2
        let prefixAccImpl :
            QueryImpl prefixAccSpec Id :=
          accImplAfter (ctx₁ s.stmt) (roles₁ s.stmt) (OD₁ s.stmt)
            []ₒ (fun q => q.elim) tr₁
        let ⟨tr₂, out, outV₂⟩ ←
          Continuation.execute reduction2 ⟨s.stmt, tr₁⟩ midOut.stmt midOut.wit
            prefixAccSpec prefixAccImpl
        let tr := Spec.Transcript.append (ctx₁ s.stmt) (ctx₂ s.stmt) tr₁ tr₂
        let honestStmtCore :=
          Spec.Transcript.packAppend (ctx₁ s.stmt) (ctx₂ s.stmt)
            (StmtOut s.stmt) tr₁ tr₂ out.stmt.stmt
        let honestStmt :
            StatementWithOracles
              (Spec.Transcript.liftAppend (ctx₁ s.stmt) (ctx₂ s.stmt)
                (StmtOut s.stmt)
                (Spec.Transcript.append (ctx₁ s.stmt) (ctx₂ s.stmt) tr₁ tr₂))
              (liftAppendOracleFamily (ctx₁ s.stmt) (ctx₂ s.stmt)
                (ιₛₒ s.stmt) (OStmtOut s.stmt)
                (Spec.Transcript.append (ctx₁ s.stmt) (ctx₂ s.stmt) tr₁ tr₂)) :=
          ⟨honestStmtCore, by sorry⟩
        let honestWit :=
          Spec.Transcript.packAppend (ctx₁ s.stmt) (ctx₂ s.stmt)
            (WitOut s.stmt) tr₁ tr₂ out.wit
        let stmtOutV :=
          Spec.Transcript.packAppend (ctx₁ s.stmt) (ctx₂ s.stmt)
            (StmtOut s.stmt) tr₁ tr₂ outV₂.1
        pure ⟨tr, ⟨honestStmt, honestWit⟩,
          ⟨stmtOutV, compSimulate reduction1 reduction2 s.stmt tr⟩⟩) := by
  sorry

end OracleReduction

end OracleDecoration

end Interaction
