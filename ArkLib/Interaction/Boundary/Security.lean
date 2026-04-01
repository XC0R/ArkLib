import ArkLib.Interaction.Boundary.Compatibility
import ArkLib.Interaction.Security

/-!
# Interaction-Native Boundaries: Plain Security Transport

This file records the basic operational and security consequences of pulling
back a verifier or reduction along a plain `Boundary.Statement` or
`Boundary.Context`.

The guiding pattern is:

- run or execute the pulled-back outer protocol;
- observe that this is just the inner protocol run on projected inputs;
- lift the resulting outputs back across the boundary;
- transport completeness or soundness hypotheses through the compatibility
  predicates from `Boundary.Compatibility`.
-/

namespace Interaction
namespace Boundary

namespace Verifier

/-- Running a pulled-back verifier is the same as running the original inner
verifier on the projected outer input and then lifting only the final plain
statement output through the boundary. -/
theorem run_pullback
    {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    {OuterStmtIn InnerStmtIn : Type}
    {Context : InnerStmtIn → Spec}
    {Roles : (s : InnerStmtIn) → RoleDecoration (Context s)}
    {StmtOut : (s : InnerStmtIn) → Spec.Transcript (Context s) → Type}
    (boundary : Statement OuterStmtIn InnerStmtIn Context StmtOut)
    (verifier : Interaction.Verifier m InnerStmtIn Context Roles StmtOut)
    (outer : OuterStmtIn)
    {OutputP : Spec.Transcript (Context (boundary.proj outer)) → Type}
    (prover :
      Spec.Strategy.withRoles m
        (Context (boundary.proj outer))
        (Roles (boundary.proj outer))
        OutputP) :
    Interaction.Verifier.run (pullback boundary verifier) outer prover =
      (fun z => ⟨z.1, z.2.1, boundary.lift outer z.1 z.2.2⟩) <$>
        Interaction.Verifier.run verifier (boundary.proj outer) prover := by
  simpa [Interaction.Verifier.run, pullback] using
    (Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput
      (fP := fun _ out => out)
      (fC := fun tr stmtOut => boundary.lift outer tr stmtOut)
      prover
      (verifier (boundary.proj outer)))

/-- Soundness for a pulled-back verifier reduces to soundness of the inner
verifier once accepting outer outputs are known to satisfy the boundary
compatibility predicate. -/
theorem probAccept_pullback_le
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {OuterStmtIn InnerStmtIn : Type}
    {Context : InnerStmtIn → Spec}
    {Roles : (s : InnerStmtIn) → RoleDecoration (Context s)}
    {StmtOut : (s : InnerStmtIn) → Spec.Transcript (Context s) → Type}
    (boundary : Statement OuterStmtIn InnerStmtIn Context StmtOut)
    (verifier : Interaction.Verifier m InnerStmtIn Context Roles StmtOut)
    (outerLangIn : Set OuterStmtIn)
    (innerLangIn : Set InnerStmtIn)
    (outerLangOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (Context (boundary.proj outer))) →
        Set (boundary.StmtOut outer tr))
    (innerLangOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (Context inner)) →
        Set (StmtOut inner tr))
    (compat :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (Context (boundary.proj outer))) →
        StmtOut (boundary.proj outer) tr →
        Prop)
    [boundarySound :
      Statement.IsSound
        boundary
        outerLangIn
        innerLangIn
        outerLangOut
        innerLangOut
        compat]
    (compatOfAccept :
      ∀ outer tr innerStmtOut,
        boundary.lift outer tr innerStmtOut ∈ outerLangOut outer tr →
        compat outer tr innerStmtOut)
    (outer : OuterStmtIn)
    {OutputP : Spec.Transcript (Context (boundary.proj outer)) → Type}
    (prover :
      Spec.Strategy.withRoles m
        (Context (boundary.proj outer))
        (Roles (boundary.proj outer))
        OutputP) :
    Pr[fun z => z.2.2 ∈ outerLangOut outer z.1 |
      Interaction.Verifier.run (pullback boundary verifier) outer prover] ≤
      Pr[fun z => z.2.2 ∈ innerLangOut (boundary.proj outer) z.1 |
        Interaction.Verifier.run verifier (boundary.proj outer) prover] := by
  rw [run_pullback, probEvent_map]
  apply probEvent_mono
  intro z hz hOuter
  by_contra hInner
  exact
    boundarySound.lift_sound
      outer
      z.1
      z.2.2
      (compatOfAccept outer z.1 z.2.2 hOuter)
      hInner
      hOuter

end Verifier

namespace Reduction

/-- Compatibility hypothesis used by `completeness_pullback`.

It says that whenever an honest outer input is valid and the inner execution
produces an output satisfying the inner relation, the boundary-specific
compatibility predicate also holds.  The final completeness theorem then
combines this with `Boundary.Context.IsComplete`. -/
private abbrev CompletenessCompat
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {StmtOut WitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext StmtOut WitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerContext inner)) →
        StmtOut inner tr →
        WitOut inner tr →
        Prop)
    (compat :
      (outer : OuterStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outer))) →
        StmtOut (boundary.stmt.proj outer) tr →
        WitOut (boundary.stmt.proj outer) tr →
        Prop) : Prop :=
  (outerStmt : OuterStmtIn) →
    (outerWit : OuterWitIn) →
    (outerStmt, outerWit) ∈ outerRelIn →
    (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outerStmt))) →
    (innerStmtOut : StmtOut (boundary.stmt.proj outerStmt) tr) →
    (innerWitOut : WitOut (boundary.stmt.proj outerStmt) tr) →
    innerRelOut
      (boundary.stmt.proj outerStmt)
      tr
      innerStmtOut
      innerWitOut →
    compat outerStmt outerWit tr innerStmtOut innerWitOut

/-- Honest execution of a pulled-back reduction is just honest execution of the
inner reduction on projected inputs, followed by lifting the prover and
verifier outputs through the boundary. -/
theorem execute_pullback
    {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {Roles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {StmtOut WitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext StmtOut WitOut)
    (reduction :
      Interaction.Reduction m
        InnerStmtIn InnerWitIn InnerContext Roles StmtOut WitOut)
    (outerStmt : OuterStmtIn)
    (outerWit : OuterWitIn) :
    Interaction.Reduction.execute (pullback boundary reduction) outerStmt outerWit =
      (fun z =>
        let out :=
          boundary.lift outerStmt outerWit z.1 z.2.1.stmt z.2.1.wit
        ⟨z.1, out, boundary.stmt.lift outerStmt z.1 z.2.2⟩) <$>
        Interaction.Reduction.execute reduction
          (boundary.stmt.proj outerStmt)
          (boundary.wit.proj outerStmt outerWit) := by
  simp [Interaction.Reduction.execute, pullback, Prover.pullback, Verifier.pullback,
    Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput]

section Completeness

variable
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {Roles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {StmtOut WitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}

variable
    (boundary :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext StmtOut WitOut)
    (reduction :
      Interaction.Reduction m
        InnerStmtIn InnerWitIn InnerContext Roles StmtOut WitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))

variable
    (outerRelOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outer))) →
        boundary.StmtOut outer tr →
        boundary.WitOut outer tr →
        Prop)
    (innerRelOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerContext inner)) →
        StmtOut inner tr →
        WitOut inner tr →
        Prop)
    (compat :
      (outer : OuterStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outer))) →
        StmtOut (boundary.stmt.proj outer) tr →
        WitOut (boundary.stmt.proj outer) tr →
        Prop)

variable
    (eps : ENNReal)

/-- Completeness transports across a context boundary once:

- valid outer inputs project to valid inner inputs,
- successful inner outputs can be lifted back to successful outer outputs via
  `Boundary.Context.IsComplete`, and
- the compatibility witness required by that lifting is available from
  `CompletenessCompat`. -/
theorem completeness_pullback
    (boundaryComplete :
      Boundary.Context.IsComplete
        boundary
        outerRelIn
        innerRelIn
        outerRelOut
        innerRelOut
        compat)
    (compatOfValid :
      CompletenessCompat boundary outerRelIn innerRelOut compat)
    (hComplete :
      reduction.completeness innerRelIn innerRelOut eps) :
    (pullback boundary reduction).completeness
      outerRelIn
      outerRelOut
      eps := by
  intro outerStmt outerWit hOuterIn
  have hInnerIn :
      (boundary.stmt.proj outerStmt,
        boundary.wit.proj outerStmt outerWit) ∈ innerRelIn :=
    boundaryComplete.proj_complete outerStmt outerWit hOuterIn
  let innerGood :
      ((tr : Spec.Transcript (InnerContext (boundary.stmt.proj outerStmt))) ×
        HonestProverOutput
          (StmtOut (boundary.stmt.proj outerStmt) tr)
          (WitOut (boundary.stmt.proj outerStmt) tr) ×
        StmtOut (boundary.stmt.proj outerStmt) tr) →
      Prop :=
    fun z =>
      z.2.1.stmt = z.2.2 ∧
        innerRelOut
          (boundary.stmt.proj outerStmt)
          z.1
          z.2.2
          z.2.1.wit
  let outerGood :
      ((tr : Spec.Transcript (InnerContext (boundary.stmt.proj outerStmt))) ×
        HonestProverOutput
          (boundary.StmtOut outerStmt tr)
          (boundary.WitOut outerStmt tr) ×
        boundary.StmtOut outerStmt tr) →
      Prop :=
    fun z =>
      z.2.1.stmt = z.2.2 ∧
        outerRelOut outerStmt z.1 z.2.2 z.2.1.wit
  have hmono :
      Pr[innerGood |
        Interaction.Reduction.execute reduction
          (boundary.stmt.proj outerStmt)
          (boundary.wit.proj outerStmt outerWit)] ≤
        Pr[outerGood |
          Interaction.Reduction.execute (pullback boundary reduction)
            outerStmt
            outerWit] := by
    rw [execute_pullback]
    rw [probEvent_map]
    apply probEvent_mono
    intro z hz hInnerGood
    rcases hInnerGood with ⟨hEq, hRel⟩
    constructor
    · simpa using congrArg (boundary.stmt.lift outerStmt z.1) hEq
    · have hCompat :
          compat outerStmt outerWit z.1 z.2.2 z.2.1.wit :=
        compatOfValid outerStmt outerWit hOuterIn z.1 z.2.2 z.2.1.wit hRel
      simpa [hEq] using
        (boundaryComplete.lift_complete
          outerStmt
          outerWit
          z.1
          z.2.2
          z.2.1.wit
          hCompat
          hOuterIn
          hRel)
  calc
    1 - eps ≤
        Pr[innerGood |
          Interaction.Reduction.execute reduction
            (boundary.stmt.proj outerStmt)
            (boundary.wit.proj outerStmt outerWit)] :=
      hComplete
        (boundary.stmt.proj outerStmt)
        (boundary.wit.proj outerStmt outerWit)
        hInnerIn
    _ ≤ Pr[outerGood |
          Interaction.Reduction.execute (pullback boundary reduction)
            outerStmt
            outerWit] :=
      hmono

theorem perfectCompleteness_pullback
    (boundaryComplete :
      Boundary.Context.IsComplete
        boundary
        outerRelIn
        innerRelIn
        outerRelOut
        innerRelOut
        compat)
    (compatOfValid :
      CompletenessCompat boundary outerRelIn innerRelOut compat)
    (hPerfect :
      reduction.perfectCompleteness innerRelIn innerRelOut) :
    (pullback boundary reduction).perfectCompleteness
      outerRelIn
      outerRelOut := by
  exact
    completeness_pullback
      boundary
      reduction
      outerRelIn
      innerRelIn
      outerRelOut
      innerRelOut
      compat
      0
      boundaryComplete
      compatOfValid
      hPerfect

end Completeness

end Reduction

end Boundary
end Interaction
