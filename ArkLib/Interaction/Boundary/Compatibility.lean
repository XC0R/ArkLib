import ArkLib.Interaction.Boundary.Reification

namespace Interaction
namespace Boundary

class Statement.IsSound
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut)
    (outerLangIn : Set OuterStmtIn)
    (innerLangIn : Set InnerStmtIn)
    (outerLangOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (boundary.proj outer))) →
        Set (boundary.StmtOut outer tr))
    (innerLangOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerContext inner)) →
        Set (InnerStmtOut inner tr))
    (compat :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (boundary.proj outer))) →
        InnerStmtOut (boundary.proj outer) tr →
        Prop) where
  proj_sound :
    ∀ outer, outer ∉ outerLangIn → boundary.proj outer ∉ innerLangIn
  lift_sound :
    ∀ outer tr innerStmtOut,
      compat outer tr innerStmtOut →
      innerStmtOut ∉ innerLangOut (boundary.proj outer) tr →
      boundary.lift outer tr innerStmtOut ∉ outerLangOut outer tr

class Context.IsComplete
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary : Context OuterStmtIn InnerStmtIn
      OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outer))) →
        boundary.StmtOut outer tr →
        boundary.WitOut outer tr →
        Prop)
    (innerRelOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerContext inner)) →
        InnerStmtOut inner tr →
        InnerWitOut inner tr →
        Prop)
    (compat :
      (outer : OuterStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outer))) →
        InnerStmtOut (boundary.stmt.proj outer) tr →
        InnerWitOut (boundary.stmt.proj outer) tr →
        Prop) where
  proj_complete :
    ∀ outerStmt outerWit,
      (outerStmt, outerWit) ∈ outerRelIn →
      (boundary.stmt.proj outerStmt,
        boundary.wit.proj outerStmt outerWit) ∈ innerRelIn
  lift_complete :
    ∀ outerStmt outerWit tr innerStmtOut innerWitOut,
      compat outerStmt outerWit tr innerStmtOut innerWitOut →
      (outerStmt, outerWit) ∈ outerRelIn →
      innerRelOut
        (boundary.stmt.proj outerStmt)
        tr
        innerStmtOut
        innerWitOut →
      let out := boundary.lift outerStmt outerWit tr innerStmtOut innerWitOut
      outerRelOut outerStmt tr out.1 out.2

namespace OracleStatement

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {toStatement :
      Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
        (tr : Spec.Transcript (InnerContext s)) →
        Innerιₛₒ s tr →
        Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
        Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
        Outerιₛₒ outer tr →
        Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]

@[inline] def toConcreteStatement
    (boundary :
      OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    Statement
      (StatementWithOracles OuterStmtIn OuterOStmtIn)
      (StatementWithOracles InnerStmtIn InnerOStmtIn)
      (fun inner => InnerContext inner.stmt)
      (fun inner tr =>
        StatementWithOracles
          (InnerStmtOut inner.stmt tr)
          (InnerOStmtOut inner.stmt tr)) where
  proj := fun outer =>
    ⟨toStatement.proj outer.stmt,
      boundary.reification.materializeIn outer.stmt outer.oracleStmt⟩
  StmtOut := fun outer tr =>
    StatementWithOracles
      (toStatement.StmtOut outer.stmt tr)
      (OuterOStmtOut outer.stmt tr)
  lift := fun outer tr innerOut =>
    ⟨toStatement.lift outer.stmt tr innerOut.stmt,
      boundary.reification.materializeOut
        outer.stmt
        outer.oracleStmt
        tr
        innerOut.oracleStmt⟩

abbrev IsSound
    (boundary :
      OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerLangIn :
      Set (StatementWithOracles OuterStmtIn OuterOStmtIn))
    (innerLangIn :
      Set (StatementWithOracles InnerStmtIn InnerOStmtIn))
    (outerLangOut :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerContext (toStatement.proj outer.stmt))) →
        Set
          (StatementWithOracles
            (toStatement.StmtOut outer.stmt tr)
            (OuterOStmtOut outer.stmt tr)))
    (innerLangOut :
      (inner : StatementWithOracles InnerStmtIn InnerOStmtIn) →
        (tr : Spec.Transcript (InnerContext inner.stmt)) →
        Set
          (StatementWithOracles
            (InnerStmtOut inner.stmt tr)
            (InnerOStmtOut inner.stmt tr)))
    (compat :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerContext (toStatement.proj outer.stmt))) →
        StatementWithOracles
          (InnerStmtOut (toStatement.proj outer.stmt) tr)
          (InnerOStmtOut (toStatement.proj outer.stmt) tr) →
        Prop) :=
  Statement.IsSound
    boundary.toConcreteStatement
    outerLangIn
    innerLangIn
    outerLangOut
    innerLangOut
    compat

end OracleStatement

namespace OracleContext

variable
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {toContext :
      Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
        (tr : Spec.Transcript (InnerContext s)) →
        Innerιₛₒ s tr →
        Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
        Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
        Outerιₛₒ outer tr →
        Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]

@[inline] def toConcreteContext
    (boundary :
      OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    Context
      (StatementWithOracles OuterStmtIn OuterOStmtIn)
      (StatementWithOracles InnerStmtIn InnerOStmtIn)
      OuterWitIn
      InnerWitIn
      (fun inner => InnerContext inner.stmt)
      (fun inner tr =>
        StatementWithOracles
          (InnerStmtOut inner.stmt tr)
          (InnerOStmtOut inner.stmt tr))
      (fun inner tr => InnerWitOut inner.stmt tr) where
  stmt := {
    proj := fun outer =>
      ⟨toContext.stmt.proj (StatementWithOracles.stmt outer),
        boundary.reification.stmt.materializeIn
          (StatementWithOracles.stmt outer)
          (StatementWithOracles.oracleStmt outer)⟩
    StmtOut := fun outer tr =>
      StatementWithOracles
        (toContext.stmt.StmtOut (StatementWithOracles.stmt outer) tr)
        (OuterOStmtOut (StatementWithOracles.stmt outer) tr)
    lift := fun outer tr innerOut =>
      ⟨toContext.stmt.lift
          (StatementWithOracles.stmt outer)
          tr
          (StatementWithOracles.stmt innerOut),
        boundary.reification.stmt.materializeOut
          (StatementWithOracles.stmt outer)
          (StatementWithOracles.oracleStmt outer)
          tr
          (StatementWithOracles.oracleStmt innerOut)⟩
  }
  wit := {
    WitOut := fun outer tr =>
      toContext.wit.WitOut (StatementWithOracles.stmt outer) tr
    proj := fun outer outerWit =>
      toContext.wit.proj (StatementWithOracles.stmt outer) outerWit
    lift := fun outer outerWit tr innerStmtOut innerWitOut =>
      toContext.wit.lift
        (StatementWithOracles.stmt outer)
        outerWit
        tr
        (StatementWithOracles.stmt innerStmtOut)
        innerWitOut
  }

abbrev IsComplete
    (boundary :
      OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerRelIn :
      Set
        (StatementWithOracles OuterStmtIn OuterOStmtIn × OuterWitIn))
    (innerRelIn :
      Set
        (StatementWithOracles InnerStmtIn InnerOStmtIn × InnerWitIn))
    (outerRelOut :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer.stmt))) →
        StatementWithOracles
          (toContext.stmt.StmtOut outer.stmt tr)
          (OuterOStmtOut outer.stmt tr) →
        toContext.wit.WitOut outer.stmt tr →
        Prop)
    (innerRelOut :
      (inner : StatementWithOracles InnerStmtIn InnerOStmtIn) →
        (tr : Spec.Transcript (InnerContext inner.stmt)) →
        StatementWithOracles
          (InnerStmtOut inner.stmt tr)
          (InnerOStmtOut inner.stmt tr) →
        InnerWitOut inner.stmt tr →
        Prop)
    (compat :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer.stmt))) →
        StatementWithOracles
          (InnerStmtOut (toContext.stmt.proj outer.stmt) tr)
          (InnerOStmtOut (toContext.stmt.proj outer.stmt) tr) →
        InnerWitOut (toContext.stmt.proj outer.stmt) tr →
        Prop) :=
  Context.IsComplete
    boundary.toConcreteContext
    outerRelIn
    innerRelIn
    outerRelOut
    innerRelOut
    compat

end OracleContext

end Boundary
end Interaction
