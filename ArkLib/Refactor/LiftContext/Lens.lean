/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Reduction

/-!
# Lift-Context Lenses

Lenses for transporting statement/witness/oracle contexts between an outer and inner
protocol interface in the refactored framework.
-/

open OracleComp OracleSpec

namespace ProtocolSpec

/-! ## Plain statement/witness lenses -/

@[ext]
structure Statement.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) where
  proj : OuterStmtIn → InnerStmtIn
  lift : OuterStmtIn → InnerStmtOut → OuterStmtOut

@[ext]
structure Witness.Lens
    (OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  proj : OuterStmtIn × OuterWitIn → InnerWitIn
  lift : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut

@[ext]
structure Witness.InvLens
    (OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  proj : OuterStmtIn × OuterWitOut → InnerWitOut
  lift : OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn

@[ext]
structure Context.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  wit : Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace Context.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline] def proj
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  fun ctxIn => (lens.stmt.proj ctxIn.1, lens.wit.proj ctxIn)

@[inline] def lift
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut :=
  fun ctxIn ctxOut => (lens.stmt.lift ctxIn.1 ctxOut.1, lens.wit.lift ctxIn ctxOut)

end Context.Lens

@[ext]
structure Extractor.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  wit : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace Extractor.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline] def proj
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitOut → InnerStmtIn × InnerWitOut :=
  fun ⟨stmtIn, witOut⟩ => (lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witOut))

end Extractor.Lens

/-! ## Oracle statement/context lenses -/

@[ext]
structure OracleStatement.Lens
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    where
  projStmt : OuterStmtIn → InnerStmtIn
  liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut
  simIn : QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
  simOut : QueryImpl [OuterOStmtOut]ₒ (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ))
  reifyIn : (∀ i, OuterOStmtIn i) → (∀ i, InnerOStmtIn i)
  reifyOut : (∀ i, OuterOStmtIn i) → (∀ i, InnerOStmtOut i) → (∀ i, OuterOStmtOut i)

namespace OracleStatement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]

@[inline] def proj
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i) :=
  fun ⟨stmtIn, oStmtIn⟩ => (lens.projStmt stmtIn, lens.reifyIn oStmtIn)

@[inline] def lift
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OuterStmtIn × (∀ i, OuterOStmtIn i) →
      (InnerStmtOut × (∀ i, InnerOStmtOut i)) →
      (OuterStmtOut × (∀ i, OuterOStmtOut i)) :=
  fun ⟨stmtIn, oStmtIn⟩ ⟨stmtOut, oStmtOut⟩ =>
    (lens.liftStmt stmtIn stmtOut, lens.reifyOut oStmtIn oStmtOut)

@[inline] def toStatementLens
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    Statement.Lens (OuterStmtIn × (∀ i, OuterOStmtIn i)) (OuterStmtOut × (∀ i, OuterOStmtOut i))
      (InnerStmtIn × (∀ i, InnerOStmtIn i)) (InnerStmtOut × (∀ i, InnerOStmtOut i)) where
  proj := lens.proj
  lift := lens.lift

@[inline, reducible] protected def id :
    OracleStatement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
      OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut where
  projStmt := id
  liftStmt := fun _ s => s
  simIn := fun q => liftM (query (spec := [OuterOStmtIn]ₒ) q)
  simOut := fun q =>
    liftM (query (spec := [OuterOStmtIn]ₒ + [OuterOStmtOut]ₒ) (Sum.inr q))
  reifyIn := id
  reifyOut := fun _ innerOStmtOut => innerOStmtOut

alias trivial := OracleStatement.Lens.id

@[inline] def ofInputOnly
    (projStmt : OuterStmtIn → InnerStmtIn)
    (simIn : QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (reifyIn : (∀ i, OuterOStmtIn i) → (∀ i, InnerOStmtIn i)) :
    OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn OuterOStmtOut where
  projStmt := projStmt
  liftStmt := fun _ s => s
  simIn := simIn
  simOut := fun q =>
    liftM (query (spec := [OuterOStmtIn]ₒ + [OuterOStmtOut]ₒ) (Sum.inr q))
  reifyIn := reifyIn
  reifyOut := fun _ innerOStmtOut => innerOStmtOut

@[inline] def ofOutputOnly
    (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut)
    (simOut : QueryImpl [OuterOStmtOut]ₒ (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ)))
    (reifyOut :
      (∀ i, OuterOStmtIn i) → (∀ i, InnerOStmtOut i) → (∀ i, OuterOStmtOut i)) :
    OracleStatement.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut OuterOStmtIn InnerOStmtOut where
  projStmt := id
  liftStmt := liftStmt
  simIn := fun q => liftM (query (spec := [OuterOStmtIn]ₒ) q)
  simOut := simOut
  reifyIn := id
  reifyOut := reifyOut

end OracleStatement.Lens

@[ext]
structure OracleContext.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  wit : Witness.Lens
      (OuterStmtIn × (∀ i, OuterOStmtIn i))
      (InnerStmtOut × (∀ i, InnerOStmtOut i))
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContext.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline] def proj
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
      (InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn :=
  fun ctxIn => (lens.stmt.proj ctxIn.1, lens.wit.proj ctxIn)

@[inline] def lift
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn) →
      ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut) →
      ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut) :=
  fun ctxIn ctxOut => (lens.stmt.lift ctxIn.1 ctxOut.1, lens.wit.lift ctxIn ctxOut)

@[inline] def toContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    Context.Lens
      (OuterStmtIn × (∀ i, OuterOStmtIn i))
      (OuterStmtOut × (∀ i, OuterOStmtOut i))
      (InnerStmtIn × (∀ i, InnerOStmtIn i))
      (InnerStmtOut × (∀ i, InnerOStmtOut i))
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut where
  stmt := lens.stmt.toStatementLens
  wit := lens.wit

@[inline, reducible] protected def id :
    OracleContext.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
      OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut
      OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := OracleStatement.Lens.id
  wit := { proj := Prod.snd, lift := fun _ z => z.2 }

alias trivial := OracleContext.Lens.id

@[inline] def ofInputOnly
    (stmtProj : OuterStmtIn → InnerStmtIn)
    (simIn : QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (reifyIn : (∀ i, OuterOStmtIn i) → (∀ i, InnerOStmtIn i))
    (witProj : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn → InnerWitIn) :
    OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn OuterOStmtOut
      OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  stmt := OracleStatement.Lens.ofInputOnly stmtProj simIn reifyIn
  wit := { proj := witProj, lift := fun _ z => z.2 }

@[inline] def ofOutputOnly
    (stmtLift : OuterStmtIn → InnerStmtOut → OuterStmtOut)
    (simOut : QueryImpl [OuterOStmtOut]ₒ (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ)))
    (reifyOut :
      (∀ i, OuterOStmtIn i) → (∀ i, InnerOStmtOut i) → (∀ i, OuterOStmtOut i))
    (witLift :
      ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn) →
        ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut) → OuterWitOut) :
    OracleContext.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut OuterOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  stmt := OracleStatement.Lens.ofOutputOnly stmtLift simOut reifyOut
  wit := { proj := Prod.snd, lift := witLift }

end OracleContext.Lens

/-! ## Lens soundness/completeness side-conditions -/

class Context.Lens.IsComplete
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compat : (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop)
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where
  proj_complete : ∀ stmtIn witIn,
    (stmtIn, witIn) ∈ outerRelIn →
      (lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)) ∈ innerRelIn
  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
      (outerStmtIn, outerWitIn) ∈ outerRelIn →
      (innerStmtOut, innerWitOut) ∈ innerRelOut →
      (lens.stmt.lift outerStmtIn innerStmtOut,
        lens.wit.lift (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut)) ∈ outerRelOut

@[reducible, simp] def OracleContext.Lens.IsComplete
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn))
    (innerRelIn : Set ((InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn))
    (outerRelOut : Set ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut))
    (innerRelOut : Set ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut))
    (compat : ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn) →
      ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut) → Prop)
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :=
  Context.Lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut compat lens.toContext

class Statement.Lens.IsSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where
  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn
  lift_sound : ∀ outerStmtIn innerStmtOut,
    compatStmt outerStmtIn innerStmtOut →
      innerStmtOut ∉ innerLangOut →
      lens.lift outerStmtIn innerStmtOut ∉ outerLangOut

@[reducible, simp] def OracleStatement.Lens.IsSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i)))
    (outerLangOut : Set (OuterStmtOut × (∀ i, OuterOStmtOut i)))
    (innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i)))
    (innerLangOut : Set (InnerStmtOut × (∀ i, InnerOStmtOut i)))
    (compatStmt :
      (OuterStmtIn × (∀ i, OuterOStmtIn i)) →
        (InnerStmtOut × (∀ i, InnerOStmtOut i)) → Prop)
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :=
  Statement.Lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut compatStmt
    lens.toStatementLens

class Extractor.Lens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where
  proj_knowledgeSound : ∀ outerStmtIn innerStmtOut outerWitOut,
    compatStmt outerStmtIn innerStmtOut →
      (lens.stmt.lift outerStmtIn innerStmtOut, outerWitOut) ∈ outerRelOut →
      (innerStmtOut, lens.wit.proj (outerStmtIn, outerWitOut)) ∈ innerRelOut
  lift_knowledgeSound : ∀ outerStmtIn outerWitOut innerWitIn,
    compatWit outerWitOut innerWitIn →
      (lens.stmt.proj outerStmtIn, innerWitIn) ∈ innerRelIn →
      (outerStmtIn, lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn) ∈ outerRelIn

/-! ## Convenience constructors -/

namespace Statement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}

@[inline, reducible] protected def id :
    Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut where
  proj := id
  lift := fun _ s => s

alias trivial := Statement.Lens.id

@[inline] def ofInputOnly (projStmt : OuterStmtIn → InnerStmtIn) :
    Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut where
  proj := projStmt
  lift := fun _ s => s

@[inline] def ofOutputOnly (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut where
  proj := id
  lift := liftStmt

end Statement.Lens

namespace Witness.Lens

variable {OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline, reducible] protected def id :
    Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  proj := Prod.snd
  lift := fun _ z => z.2

alias trivial := Witness.Lens.id

@[inline] def ofInputOnly (projWit : OuterStmtIn × OuterWitIn → InnerWitIn) :
    Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  proj := projWit
  lift := fun _ z => z.2

@[inline] def ofOutputOnly
    (liftWit : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut) :
    Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  proj := Prod.snd
  lift := liftWit

end Witness.Lens

namespace Witness.InvLens

variable {OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline, reducible] protected def id :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  proj := Prod.snd
  lift := fun _ w => w

alias trivial := Witness.InvLens.id

@[inline] def ofOutputOnly (projWit : OuterStmtIn × OuterWitOut → InnerWitOut) :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  proj := projWit
  lift := fun _ w => w

@[inline] def ofInputOnly
    (liftWit : OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn) :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  proj := Prod.snd
  lift := liftWit

end Witness.InvLens

namespace Context.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline, reducible] protected def id :
    Context.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
      OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := Statement.Lens.id
  wit := Witness.Lens.id

alias trivial := Context.Lens.id

@[inline] def ofInputOnly
    (stmtProj : OuterStmtIn → InnerStmtIn)
    (witProj : OuterStmtIn × OuterWitIn → InnerWitIn) :
    Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
      OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  stmt := Statement.Lens.ofInputOnly stmtProj
  wit := Witness.Lens.ofInputOnly witProj

@[inline] def ofOutputOnly
    (stmtLift : OuterStmtIn → InnerStmtOut → OuterStmtOut)
    (witLift : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut) :
    Context.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
      OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  stmt := Statement.Lens.ofOutputOnly stmtLift
  wit := Witness.Lens.ofOutputOnly witLift

end Context.Lens

namespace Extractor.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

@[inline, reducible] def idWit
    (stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) :
    Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := stmtLens
  wit := Witness.InvLens.id

alias trivialWit := Extractor.Lens.idWit

end Extractor.Lens

end ProtocolSpec
