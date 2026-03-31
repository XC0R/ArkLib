/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Continuation

namespace Interaction

namespace OracleDecoration

/-- `toMonadDecoration` distributes over `Spec.stateChain`: the monad decoration for
the chained spec equals `Decoration.stateChain` of per-stage monad decorations,
where each stage starts from the accumulated oracle spec of preceding stages. -/
private theorem toMonadDecoration_chain
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {Stage : Nat → Type} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s))
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    toMonadDecoration oSpec OStmtIn (Spec.stateChain Stage spec advance n i s)
      (RoleDecoration.stateChain roles n i s) (Role.Refine.stateChain od n i s) accSpec =
    Spec.Decoration.stateChain
      (fun j st => toMonadDecoration oSpec OStmtIn (spec j st) (roles j st) (od j st) accSpec)
      n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [Spec.stateChain_succ, Spec.Decoration.stateChain, Role.Refine.stateChain]
      rw [toMonadDecoration_append]
      congr 1; funext tr
      sorry

/-- N-ary state chain composition of oracle reductions. At each stage, the step
functions transform prover state and verifier state. Each stage's verifier sees
oracle access from `oSpec + [OStmtIn]ₒ` plus the accumulated spec. -/
def OracleReduction.stateChainComp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Stage : Nat → Type}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s)}
    {ProverState VerifierState : (i : Nat) → Stage i → Type}
    (n : Nat)
    (initStage : StatementIn → Stage 0)
    {ιₛₒ : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) → Type}
    {OStmtOut :
      (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (proverInit : (s : StatementWithOracles StatementIn OStmtIn) → WitnessIn →
      OracleComp oSpec (ProverState 0 (initStage s.stmt)))
    (proverStep : (i : Nat) → (st : Stage i) → ProverState i st →
      OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec) (spec i st) (roles i st)
        (fun tr => ProverState (i + 1) (advance i st tr))))
    (stmtResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      Spec.Transcript.stateChainFamily VerifierState n 0 (initStage s) tr)
    (proverOStmtResult : (s : StatementWithOracles StatementIn OStmtIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s.stmt))) →
      OracleStatement (OStmtOut s.stmt tr))
    (verifierInit : (s : StatementIn) → VerifierState 0 (initStage s))
    (verifierStep : {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      (i : Nat) → (st : Stage i) → VerifierState i st →
      Spec.Counterpart.withMonads (spec i st) (roles i st)
        (toMonadDecoration oSpec OStmtIn (spec i st) (roles i st) (od i st) accSpec)
        (fun tr => VerifierState (i + 1) (advance i st tr)))
    (simulateResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      QueryImpl [OStmtOut s tr]ₒ
        (OracleComp ([OStmtIn]ₒ + toOracleSpec
          (Spec.stateChain Stage spec advance n 0 (initStage s))
          (RoleDecoration.stateChain roles n 0 (initStage s))
          (Role.Refine.stateChain (fun i st => od i st) n 0 (initStage s)) tr))) :
    OracleReduction oSpec StatementIn OStmtIn WitnessIn
      (fun s => Spec.stateChain Stage spec advance n 0 (initStage s))
      (fun s => RoleDecoration.stateChain roles n 0 (initStage s))
      (fun s => Role.Refine.stateChain (fun i st => od i st) n 0 (initStage s))
      (fun s => Spec.Transcript.stateChainFamily VerifierState n 0 (initStage s))
      OStmtOut
      (fun s => Spec.Transcript.stateChainFamily ProverState n 0 (initStage s)) where
  prover sWithOracles w := do
    let a ← proverInit sWithOracles w
    let strat ← Spec.Strategy.stateChainCompWithRoles proverStep n 0 (initStage sWithOracles.stmt) a
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr pOut => ⟨⟨stmtResult sWithOracles.stmt tr, proverOStmtResult sWithOracles tr⟩, pOut⟩)
      strat
  verifier s {ιₐ} accSpec := by
    let raw :=
      Spec.Counterpart.withMonads.stateChainComp (verifierStep accSpec)
        n 0 (initStage s) (verifierInit s)
    simpa [toMonadDecoration_chain (oSpec := oSpec) (OStmtIn := OStmtIn)
      od accSpec n 0 (initStage s)] using raw
  simulate := simulateResult

end OracleDecoration

end Interaction
