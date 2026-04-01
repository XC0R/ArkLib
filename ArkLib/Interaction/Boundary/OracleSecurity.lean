import ArkLib.Interaction.Boundary.Reification
import ArkLib.Interaction.OracleSecurity

/-!
# Interaction-Native Boundaries: Oracle Security Transport

This file packages the verifier-side and honest-execution consequences of an
oracle boundary.

The key split mirrors the rest of the boundary layer:

- `Boundary.OracleStatementAccess` handles verifier-side oracle simulation.
- `Boundary.OracleStatementReification` handles concrete oracle materialization.
- `Boundary.OracleStatementReification.Realizes` is the coherence law relating
  the two views.

The theorems here say that once a concrete oracle family realizes the inner
simulation, boundary pullback preserves that fact on the outer side as well.
The same idea will later feed completeness and soundness transport theorems.
-/

namespace Interaction
namespace Boundary

namespace OracleDecoration

/-! ### Verifier-Side Simulation -/

namespace OracleVerifier

/-- If a concrete inner output-oracle family realizes the inner verifier's
simulation, then materializing that oracle family across the boundary realizes
the pulled-back verifier's simulation as well.

The verifier's behavior is unchanged. Pullback only:
- reroutes inner input-oracle queries through `boundary.access`, and
- reinterprets the concrete inner output oracle as an outer one via
  `boundary.reification.materializeOut`. -/
theorem simulates_pullback
    {ι : Type _} {oSpec : OracleSpec ι}
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {oracleDec : OracleDecoration pSpec roles}
    {OuterStmtIn InnerStmtIn : Type}
    {InnerStmtOut : InnerStmtIn → Spec.Transcript pSpec → Type}
    (toStatement :
      Boundary.Statement OuterStmtIn InnerStmtIn (fun _ => pSpec) InnerStmtOut)
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ : Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) → (tr : Spec.Transcript pSpec) → Innerιₛₒ → Type}
    {Outerιₛₒ : Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) → (tr : Spec.Transcript pSpec) → Outerιₛₒ → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      Interaction.OracleDecoration.OracleVerifier
        oSpec pSpec roles oracleDec
        InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut)
    (outer : OuterStmtIn)
    (oStmtIn : Interaction.OracleStatement OuterOStmtIn)
    (tr : Spec.Transcript pSpec)
    (innerOStmtOut :
      Interaction.OracleStatement (InnerOStmtOut (toStatement.proj outer) tr))
    (hInner :
      Interaction.OracleDecoration.OracleVerifier.Simulates
        verifier
        (toStatement.proj outer)
        (boundary.reification.materializeIn outer oStmtIn)
        tr
        innerOStmtOut) :
    Interaction.OracleDecoration.OracleVerifier.Simulates
      (Interaction.OracleDecoration.OracleVerifier.pullback
        toStatement
        boundary.access
        verifier)
      outer
      oStmtIn
      tr
      (boundary.reification.materializeOut outer oStmtIn tr innerOStmtOut) := by
  intro i q
  simpa [Interaction.OracleDecoration.OracleVerifier.Simulates,
    Interaction.OracleDecoration.OracleVerifier.pullback] using
    Boundary.OracleStatementReification.pullbackSimulate_materialize
      boundary.access
      boundary.reification
      boundary.coherent
      outer
      oStmtIn
      tr
      (OracleDecoration.toOracleSpec pSpec roles oracleDec tr)
      (OracleDecoration.answerQuery pSpec roles oracleDec tr)
      innerOStmtOut
      (verifier.simulate (toStatement.proj outer) tr)
      (by
        intro q'
        rcases q' with ⟨i, q⟩
        simpa [Interaction.OracleDecoration.OracleVerifier.Simulates,
          OracleDecoration.oracleContextImpl, QueryImpl.add] using hInner i q)
      ⟨i, q⟩

end OracleVerifier

namespace OracleReduction

/-! ### Honest Execution Views -/

/-- The dependent output package produced by honest execution of the inner
oracle reduction, before any boundary transport back to the outer interface. -/
private abbrev InnerExecuteView
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    (outerStmt : StatementWithOracles OuterStmtIn OuterOStmtIn) :=
  (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outerStmt.stmt))) ×
    HonestProverOutput
      (StatementWithOracles
        (InnerStmtOut (toContext.stmt.proj outerStmt.stmt) tr)
        (InnerOStmtOut (toContext.stmt.proj outerStmt.stmt) tr))
      (InnerWitOut (toContext.stmt.proj outerStmt.stmt) tr) ×
    ((InnerStmtOut (toContext.stmt.proj outerStmt.stmt) tr) ×
      QueryImpl
        [InnerOStmtOut (toContext.stmt.proj outerStmt.stmt) tr]ₒ
        (OracleComp
          ([InnerOStmtIn]ₒ +
            OracleDecoration.toOracleSpec
              (InnerContext (toContext.stmt.proj outerStmt.stmt))
              (InnerRoles (toContext.stmt.proj outerStmt.stmt))
              (InnerOD (toContext.stmt.proj outerStmt.stmt))
              tr)))

/-- The dependent output package produced by honest execution of the pulled-back
outer oracle reduction after transporting all prover and verifier outputs across
the boundary. -/
private abbrev OuterExecuteView
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (outerStmt : StatementWithOracles OuterStmtIn OuterOStmtIn) :=
  (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outerStmt.stmt))) ×
    HonestProverOutput
      (StatementWithOracles
        (toContext.StmtOut outerStmt.stmt tr)
        (OuterOStmtOut outerStmt.stmt tr))
      (toContext.WitOut outerStmt.stmt tr) ×
    ((toContext.StmtOut outerStmt.stmt tr) ×
      QueryImpl
        [OuterOStmtOut outerStmt.stmt tr]ₒ
        (OracleComp
          ([OuterOStmtIn]ₒ +
            OracleDecoration.toOracleSpec
              (InnerContext (toContext.stmt.proj outerStmt.stmt))
              (InnerRoles (toContext.stmt.proj outerStmt.stmt))
              (InnerOD (toContext.stmt.proj outerStmt.stmt))
              tr)))

/-- Project an outer statement-with-oracles to the inner statement and
materialize its input oracle family across the boundary. -/
private def materializedInput
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerStmt : StatementWithOracles OuterStmtIn OuterOStmtIn) :
    StatementWithOracles InnerStmtIn InnerOStmtIn :=
  ⟨toContext.stmt.proj outerStmt.stmt,
    boundary.reification.stmt.materializeIn
      outerStmt.stmt
      outerStmt.oracleStmt⟩

/-- Transport the honest execution output of the inner reduction back across
the boundary.

It
- lifts the honest prover's plain statement and witness through `toContext.lift`,
- materializes the concrete outer output oracle family,
- lifts the verifier's plain output statement, and
- reroutes the verifier's output-oracle simulation through `pullbackSimulate`. -/
private def mapExecuteOutput
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      Interaction.OracleDecoration.OracleReduction oSpec
        InnerStmtIn InnerOStmtIn InnerWitIn
        InnerContext InnerRoles InnerOD
        InnerStmtOut InnerOStmtOut InnerWitOut)
    (outerStmt : StatementWithOracles OuterStmtIn OuterOStmtIn)
    (outerWit : OuterWitIn)
    (z :
      InnerExecuteView
        (toContext := toContext)
        (OuterOStmtIn := OuterOStmtIn)
        (InnerOStmtIn := InnerOStmtIn)
        (InnerRoles := InnerRoles)
        (InnerOD := InnerOD)
        (InnerOStmtOut := InnerOStmtOut)
        outerStmt) :
    OuterExecuteView
      (toContext := toContext)
      (OuterOStmtIn := OuterOStmtIn)
      (InnerOStmtIn := InnerOStmtIn)
      (InnerRoles := InnerRoles)
      (InnerOD := InnerOD)
      (InnerOStmtOut := InnerOStmtOut)
      (OuterOStmtOut := OuterOStmtOut)
      outerStmt :=
  let out :=
    toContext.lift
      outerStmt.stmt
      outerWit
      z.1
      z.2.1.stmt.stmt
      z.2.1.wit
  ⟨z.1,
    ⟨⟨out.1,
        boundary.reification.stmt.materializeOut
          outerStmt.stmt
          outerStmt.oracleStmt
          z.1
          z.2.1.stmt.oracleStmt⟩,
      out.2⟩,
    ⟨toContext.stmt.lift outerStmt.stmt z.1 z.2.2.1,
      Boundary.OracleStatementAccess.pullbackSimulate
        (access := boundary.access.stmt)
        outerStmt.stmt
        z.1
        (OracleDecoration.toOracleSpec
          (InnerContext (toContext.stmt.proj outerStmt.stmt))
          (InnerRoles (toContext.stmt.proj outerStmt.stmt))
          (InnerOD (toContext.stmt.proj outerStmt.stmt))
          z.1)
        (reduction.simulate (toContext.stmt.proj outerStmt.stmt) z.1)⟩⟩

/-- Running the pulled-back verifier counterpart against concrete outer input
oracles is extensionally the same as running the original inner verifier against
the materialized inner input oracles, then lifting only the final plain
verifier output through the statement boundary.

This isolates the verifier-side transport from the prover-side witness and
output-oracle materialization handled by `mapExecuteOutput`. -/
private theorem runWithOracleCounterpart_pullbackVerifier
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerStmt : StatementWithOracles OuterStmtIn OuterOStmtIn)
    {ιₐ : Type}
    (accSpec : OracleSpec ιₐ)
    (accImpl : QueryImpl accSpec Id)
    {OutputP :
      Spec.Transcript (InnerContext (toContext.stmt.proj outerStmt.stmt)) → Type}
    (strat :
      Spec.Strategy.withRoles
        (OracleComp oSpec)
        (InnerContext (toContext.stmt.proj outerStmt.stmt))
        (InnerRoles (toContext.stmt.proj outerStmt.stmt))
        OutputP)
    (verifier :
      Spec.Counterpart.withMonads
        (InnerContext (toContext.stmt.proj outerStmt.stmt))
        (InnerRoles (toContext.stmt.proj outerStmt.stmt))
        (OracleDecoration.toMonadDecoration
          oSpec
          InnerOStmtIn
          (InnerContext (toContext.stmt.proj outerStmt.stmt))
          (InnerRoles (toContext.stmt.proj outerStmt.stmt))
          (InnerOD (toContext.stmt.proj outerStmt.stmt))
          accSpec)
        (fun tr => InnerStmtOut (toContext.stmt.proj outerStmt.stmt) tr)) :
    OracleDecoration.runWithOracleCounterpart
        (OracleInterface.simOracle0 OuterOStmtIn outerStmt.oracleStmt)
        (InnerContext (toContext.stmt.proj outerStmt.stmt))
        (InnerRoles (toContext.stmt.proj outerStmt.stmt))
        (InnerOD (toContext.stmt.proj outerStmt.stmt))
        accSpec
        accImpl
        strat
        (Boundary.pullbackCounterpart
          boundary.access.stmt.simulateIn
          (InnerContext (toContext.stmt.proj outerStmt.stmt))
          (InnerRoles (toContext.stmt.proj outerStmt.stmt))
          (InnerOD (toContext.stmt.proj outerStmt.stmt))
          (fun tr stmtOut => toContext.stmt.lift outerStmt.stmt tr stmtOut)
          accSpec
          verifier) =
      (fun z =>
        ⟨z.1, z.2.1, toContext.stmt.lift outerStmt.stmt z.1 z.2.2⟩) <$>
        OracleDecoration.runWithOracleCounterpart
          (OracleInterface.simOracle0
            InnerOStmtIn
            (boundary.reification.stmt.materializeIn
              outerStmt.stmt
              outerStmt.oracleStmt))
          (InnerContext (toContext.stmt.proj outerStmt.stmt))
          (InnerRoles (toContext.stmt.proj outerStmt.stmt))
          (InnerOD (toContext.stmt.proj outerStmt.stmt))
          accSpec
          accImpl
          strat
          verifier := by
  sorry

/-! ### Reduction-Side Simulation -/

/-- If a concrete inner output-oracle family realizes the inner reduction's
simulation, then materializing that oracle family across the boundary realizes
the pulled-back reduction's simulation as well.

This is the reduction analogue of `OracleVerifier.simulates_pullback`: it
tracks only the verifier-side oracle semantics, not the full honest execution
trace. -/
theorem simulates_pullback
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      Interaction.OracleDecoration.OracleReduction oSpec
        InnerStmtIn InnerOStmtIn InnerWitIn
        InnerContext InnerRoles InnerOD
        InnerStmtOut InnerOStmtOut InnerWitOut)
    (outer : OuterStmtIn)
    (oStmtIn : Interaction.OracleStatement OuterOStmtIn)
    (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer)))
    (innerOStmtOut :
      Interaction.OracleStatement (InnerOStmtOut (toContext.stmt.proj outer) tr))
    (hInner :
      Interaction.OracleDecoration.OracleReduction.Simulates
        reduction
        (toContext.stmt.proj outer)
        (boundary.reification.stmt.materializeIn outer oStmtIn)
        tr
        innerOStmtOut) :
    Interaction.OracleDecoration.OracleReduction.Simulates
      (Interaction.OracleDecoration.OracleReduction.pullback
        toContext
        boundary
        reduction)
      outer
      oStmtIn
      tr
      (boundary.reification.stmt.materializeOut outer oStmtIn tr innerOStmtOut) := by
  intro i q
  simpa [Interaction.OracleDecoration.OracleReduction.Simulates,
    Interaction.OracleDecoration.OracleReduction.pullback] using
    Boundary.OracleStatementReification.pullbackSimulate_materialize
      boundary.access.stmt
      boundary.reification.stmt
      boundary.coherent
      outer
      oStmtIn
      tr
      (OracleDecoration.toOracleSpec
        (InnerContext (toContext.stmt.proj outer))
        (InnerRoles (toContext.stmt.proj outer))
        (InnerOD (toContext.stmt.proj outer))
        tr)
      (OracleDecoration.answerQuery
        (InnerContext (toContext.stmt.proj outer))
        (InnerRoles (toContext.stmt.proj outer))
        (InnerOD (toContext.stmt.proj outer))
        tr)
      innerOStmtOut
      (reduction.simulate (toContext.stmt.proj outer) tr)
      (by
        intro q'
        rcases q' with ⟨i, q⟩
        simpa [Interaction.OracleDecoration.OracleReduction.Simulates,
          OracleDecoration.oracleContextImpl, QueryImpl.add] using hInner i q)
      ⟨i, q⟩

end OracleReduction
end OracleDecoration

end Boundary
end Interaction
