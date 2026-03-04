/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Defs
import ArkLib.Refactor.FiatShamir

/-!
# State-Restoration Security (Refactor)

Dedicated state-restoration security notions and constructive bridge
to basic outside-sampling security.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

/-! ## SR oracle and challenge replay infrastructure -/

abbrev srChallengeOracle (StmtIn : Type) (pSpec : ProtocolSpec) :=
  fsChallengeOracle StmtIn pSpec

def srReplayChallengeAux
    {StmtIn : Type}
    : (acc : List Type) → (pSpec : ProtocolSpec) →
      Challenges pSpec → (i : FSIdx StmtIn acc pSpec) → fsOracleSpec StmtIn acc pSpec i
  | _, [], _, i => nomatch i
  | acc, (.P_to_V T _) :: tl, chs, i =>
      srReplayChallengeAux (StmtIn := StmtIn) (acc ++ [T]) tl chs i
  | _, (.V_to_P _) :: _, chs, Sum.inl _ => chs.head
  | acc, (.V_to_P _) :: tl, chs, Sum.inr i =>
      srReplayChallengeAux (StmtIn := StmtIn) acc tl chs.tail i

@[simp] theorem srReplayChallengeAux_nil
    {StmtIn : Type} {acc : List Type} {chs : Challenges ([] : ProtocolSpec)}
    (i : FSIdx StmtIn acc ([] : ProtocolSpec)) :
    srReplayChallengeAux (StmtIn := StmtIn) acc ([] : ProtocolSpec) chs i = nomatch i := by
  cases i

@[simp] theorem srReplayChallengeAux_cons_P_to_V
    {StmtIn : Type} {acc : List Type} {T : Type} {oi : OracleInterface T} {tl : ProtocolSpec}
    (chs : Challenges ((.P_to_V T oi) :: tl))
    (i : FSIdx StmtIn (acc ++ [T]) tl) :
    srReplayChallengeAux (StmtIn := StmtIn) acc ((.P_to_V T oi) :: tl) chs i =
      srReplayChallengeAux (StmtIn := StmtIn) (acc ++ [T]) tl chs i := rfl

@[simp] theorem srReplayChallengeAux_cons_V_to_P_left
    {StmtIn : Type} {acc : List Type} {T : Type} {tl : ProtocolSpec}
    (chs : Challenges ((.V_to_P T) :: tl)) (q : StmtIn × HVector id acc) :
    srReplayChallengeAux (StmtIn := StmtIn) acc ((.V_to_P T) :: tl) chs (Sum.inl q) = chs.head :=
  rfl

@[simp] theorem srReplayChallengeAux_cons_V_to_P_right
    {StmtIn : Type} {acc : List Type} {T : Type} {tl : ProtocolSpec}
    (chs : Challenges ((.V_to_P T) :: tl)) (i : FSIdx StmtIn acc tl) :
    srReplayChallengeAux (StmtIn := StmtIn) acc ((.V_to_P T) :: tl) chs (Sum.inr i) =
      srReplayChallengeAux (StmtIn := StmtIn) acc tl chs.tail i := rfl

/-- Replay SR/FS challenges from a sampled `Challenges pSpec`. -/
def srReplayChallenge
    {StmtIn : Type} {pSpec : ProtocolSpec} :
    QueryImpl (srChallengeOracle StmtIn pSpec) (StateT (Challenges pSpec) ProbComp) :=
  fun q chs =>
    pure (srReplayChallengeAux (StmtIn := StmtIn) [] pSpec chs q, chs)

/-- Canonical SR initialization induced by basic outside-sampling semantics. -/
def srInitFromBasic
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {σ : Type} (init : ProbComp σ) :
    ProbComp (σ × Challenges pSpec) := do
  let σ0 ← init
  let ch ← sampleChallenges pSpec
  pure (σ0, ch)

/-- Generalized canonical replay implementation over `fsOracleSpec` at accumulator `acc`. -/
def srImplFromBasicAux
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {acc : List Type} {pSpec : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    QueryImpl (oSpec + fsOracleSpec StmtIn acc pSpec)
      (StateT (σ × Challenges pSpec) ProbComp)
  | .inl q => fun st => do
      let (a, σ') ← impl q st.1
      pure (a, (σ', st.2))
  | .inr q => fun st => do
      let a := srReplayChallengeAux (StmtIn := StmtIn) acc pSpec st.2 q
      let ch' := st.2
      pure (a, (st.1, ch'))

/-- Canonical SR query implementation induced by basic outside-sampling semantics. -/
def srImplFromBasic
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {pSpec : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
    (StateT (σ × Challenges pSpec) ProbComp) :=
  srImplFromBasicAux (StmtIn := StmtIn) (acc := []) (pSpec := pSpec) impl

@[simp] theorem srImplFromBasicAux_cons_P_to_V
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {acc : List Type}
    {T : Type} {oi : OracleInterface T} {tl : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := (.P_to_V T oi) :: tl) impl =
      srImplFromBasicAux (StmtIn := StmtIn) (acc := acc ++ [T]) (pSpec := tl) impl := by
  funext q
  cases q <;> rfl

/-! ## SR prover and extractor interfaces -/

namespace Prover

def StateRestoration.Soundness
    {ι : Type} (oSpec : OracleSpec ι) (StmtIn : Type) (pSpec : ProtocolSpec) :=
  OracleComp (oSpec + srChallengeOracle StmtIn pSpec) (StmtIn × Messages pSpec)

def StateRestoration.KnowledgeSoundness
    {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitOut : Type) (pSpec : ProtocolSpec) :=
  OracleComp (oSpec + srChallengeOracle StmtIn pSpec) (StmtIn × Messages pSpec × WitOut)

def toStateRestorationSoundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn Output : Type} {pSpec : ProtocolSpec}
    (stmtIn : StmtIn) (prover : Prover (OracleComp oSpec) Output pSpec) :
    Prover.StateRestoration.Soundness oSpec StmtIn pSpec := do
  let (msgs, _) ← Prover.runFS (oSpec := oSpec) (stmt := stmtIn)
    [] pSpec prover (HVector.nil : HVector id [])
  pure (stmtIn, msgs)

def toStateRestorationKnowledgeSoundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitOut : Type} {pSpec : ProtocolSpec}
    (stmtIn : StmtIn) (prover : Prover (OracleComp oSpec) WitOut pSpec) :
    Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec := do
  let (msgs, witOut) ← Prover.runFS (oSpec := oSpec) (stmt := stmtIn)
    [] pSpec prover (HVector.nil : HVector id [])
  pure (stmtIn, msgs, witOut)

end Prover

namespace OracleProver

@[reducible] def StateRestoration.Soundness
    {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (pSpec : ProtocolSpec) :=
  Prover.StateRestoration.Soundness oSpec (StmtIn × (∀ i, OStmtIn i)) pSpec

@[reducible] def StateRestoration.KnowledgeSoundness
    {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitOut : Type)
    (pSpec : ProtocolSpec) :=
  Prover.StateRestoration.KnowledgeSoundness oSpec (StmtIn × (∀ i, OStmtIn i)) WitOut pSpec

end OracleProver

namespace Extractor

def StateRestoration
    {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn WitOut : Type) (pSpec : ProtocolSpec) :=
  StmtIn → WitOut → Transcript pSpec → OptionT (OracleComp oSpec) WitIn

end Extractor

/-! ## SR games -/

def srSoundnessGame
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} {pSpec : ProtocolSpec}
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    OracleComp (oSpec + srChallengeOracle StmtIn pSpec) (Transcript pSpec × StmtIn) := do
  let (stmtIn, msgs) ← P
  let tr ← Messages.deriveTranscript (oSpec := oSpec) (stmt := stmtIn)
    [] pSpec (HVector.nil : HVector id []) msgs
  pure (tr, stmtIn)

def srKnowledgeSoundnessGame
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type} {pSpec : ProtocolSpec}
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    OracleComp (oSpec + srChallengeOracle StmtIn pSpec) (Transcript pSpec × StmtIn × WitOut) := do
  let (stmtIn, msgs, witOut) ← P
  let tr ← Messages.deriveTranscript (oSpec := oSpec) (stmt := stmtIn)
    [] pSpec (HVector.nil : HVector id []) msgs
  pure (tr, stmtIn, witOut)

private theorem simulateQ_srImplFromBasicAux_liftM_run
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {acc : List Type} {pSpec : ProtocolSpec}
    {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) :
    ∀ (σ0 : σ) (ch : Challenges pSpec),
        (simulateQ (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := pSpec) impl)
        (liftM oa)).run (σ0, ch) =
        ((fun z : α × σ => (z.1, (z.2, ch))) <$> (simulateQ impl oa).run σ0) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro σ0 ch
      simp
  | query_bind t oa ih =>
      intro σ0 ch
      have hquery :
          (simulateQ
              (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := pSpec) impl)
              (liftM ((liftM (query t)) : OracleComp oSpec (oSpec.Range t)))).run (σ0, ch) =
            ((fun z : oSpec.Range t × σ => (z.1, (z.2, ch))) <$> (impl t).run σ0) := by
        change (simulateQ
            (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := pSpec) impl)
            (liftM (query (spec := oSpec + fsOracleSpec StmtIn acc pSpec) (.inl t)))).run
              (σ0, ch) =
            ((fun z : oSpec.Range t × σ => (z.1, (z.2, ch))) <$> (impl t).run σ0)
        simp [simulateQ_query, srImplFromBasicAux, StateT.run, map_eq_bind_pure_comp]
      simp [hquery, ih, map_eq_bind_pure_comp, bind_assoc]

private theorem simulateQ_srImplFromBasicAux_liftFSTail_run
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {acc : List Type} {T : Type} {tl : ProtocolSpec}
    {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + fsOracleSpec StmtIn acc tl) α) :
    ∀ (σ0 : σ) (chal : T) (chTail : Challenges tl),
      (simulateQ
          (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := (.V_to_P T) :: tl) impl)
          (simulateQ (liftFSTail oSpec StmtIn acc T tl) oa)).run (σ0, chal ::ₕ chTail) =
        ((fun z : α × (σ × Challenges tl) => (z.1, (z.2.1, chal ::ₕ z.2.2))) <$>
          (simulateQ
            (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := tl) impl)
            oa).run (σ0, chTail)) := by
  sorry

private theorem runFS_deriveTranscript_eq_run
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn Output : Type} {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) :
    ∀ (acc : List Type) (pSpec : ProtocolSpec)
      (prover : Prover (OracleComp oSpec) Output pSpec)
      (accMsgs : HVector id acc)
      (ch : Challenges pSpec) (σ0 : σ),
      (simulateQ (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc) (pSpec := pSpec) impl) (do
        let (msgs, out) ← Prover.runFS (oSpec := oSpec) (stmt := stmt) acc pSpec prover accMsgs
        let tr ← Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc pSpec accMsgs msgs
        pure (tr, out))).run (σ0, ch) =
      ((fun z : (Transcript pSpec × Output) × σ => (z.1, (z.2, ch))) <$>
        (simulateQ impl (Prover.run pSpec prover ch)).run σ0) := by
  intro acc pSpec
  induction pSpec generalizing acc with
  | nil =>
      intro prover accMsgs ch σ0
      simp [Prover.runFS, Messages.deriveTranscript, Prover.run, srImplFromBasicAux]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover accMsgs ch σ0
          rcases prover with ⟨msg, cont⟩
          simp [Prover.runFS, Messages.deriveTranscript, Prover.run, bind_assoc,
            simulateQ_srImplFromBasicAux_liftM_run]
          refine bind_congr (x := (simulateQ impl cont).run σ0) (fun a => ?_)
          have hih := ih (acc := acc ++ [T]) (prover := a.1)
            (accMsgs := HVector.snoc accMsgs msg) (ch := ch) (σ0 := a.2)
          simpa [map_eq_bind_pure_comp, bind_assoc] using
            congrArg (fun mx =>
              (fun z : (Transcript tl × Output) × (σ × Challenges tl) =>
                ((Transcript.cons (r := .P_to_V T oi) msg z.1.1, z.1.2), z.2)) <$> mx) hih
      | V_to_P T =>
          intro prover accMsgs ch σ0
          cases ch with
          | mk chal chTail =>
              sorry

private theorem srSoundnessGame_adapter_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn Output : Type} {pSpec : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn)
    (prover : Prover (OracleComp oSpec) Output pSpec)
    (σ0 : σ) (ch : Challenges pSpec) :
    (simulateQ (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl)
      (srSoundnessGame
        (Prover.toStateRestorationSoundness (oSpec := oSpec) (pSpec := pSpec) stmtIn prover))).run
      (σ0, ch) =
      ((fun z : (Transcript pSpec × Output) × σ => ((z.1.1, stmtIn), (z.2, ch))) <$>
        (simulateQ impl (Prover.run pSpec prover ch)).run σ0) := by
  sorry

private theorem srKnowledgeSoundnessGame_adapter_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitOut : Type} {pSpec : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn)
    (prover : Prover (OracleComp oSpec) WitOut pSpec)
    (σ0 : σ) (ch : Challenges pSpec) :
    (simulateQ (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl)
      (srKnowledgeSoundnessGame
        (Prover.toStateRestorationKnowledgeSoundness
          (oSpec := oSpec) (pSpec := pSpec) stmtIn prover))).run (σ0, ch) =
      ((fun z : (Transcript pSpec × WitOut) × σ => ((z.1.1, stmtIn, z.1.2), (z.2, ch))) <$>
        (simulateQ impl (Prover.run pSpec prover ch)).run σ0) := by
  sorry

/-! ## SR security notions -/

namespace Verifier

def stateRestorationSoundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {pSpec : ProtocolSpec}
    {srσ : Type}
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (srInit : ProbComp srσ)
    (srImpl : QueryImpl (oSpec + srChallengeOracle StmtIn pSpec) (StateT srσ ProbComp))
    (srSoundnessError : ℝ≥0) : Prop :=
  ∀ srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec,
    Pr[(fun
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
      | do
        StateT.run'
          (simulateQ srImpl (do
            let (tr, stmtIn) ← srSoundnessGame srProver
            let stmtOut ← (verifier stmtIn tr).run
            pure (stmtIn, stmtOut)))
          (← srInit)
    ] ≤ srSoundnessError

def stateRestorationKnowledgeSoundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    {srσ : Type}
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (srInit : ProbComp srσ)
    (srImpl : QueryImpl (oSpec + srChallengeOracle StmtIn pSpec) (StateT srσ ProbComp))
    (srKnowledgeError : ℝ≥0) : Prop :=
  ∃ srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec,
  ∀ srProver : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec,
    Pr[(fun
      | (stmtIn, some witIn, some stmtOut, witOut) =>
          (stmtOut, witOut) ∈ relOut ∧ (stmtIn, witIn) ∉ relIn
      | _ => False)
      | do
        StateT.run'
          (simulateQ srImpl (do
            let (tr, stmtIn, witOut) ← srKnowledgeSoundnessGame srProver
            let stmtOut ← (verifier stmtIn tr).run
            let witIn ← (srExtractor stmtIn witOut tr).run
            pure (stmtIn, witIn, stmtOut, witOut)))
          (← srInit)
    ] ≤ srKnowledgeError

end Verifier

/-! ## Core implication theorems (constructive canonical bridge) -/

theorem stateRestorationSoundness_implies_soundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    [ChallengesSampleable pSpec]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (ε : ℝ≥0) :
    verifier.stateRestorationSoundness langIn langOut
      (srInitFromBasic (pSpec := pSpec) init)
      (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl) ε →
      verifier.soundness init impl langIn langOut ε := by
  sorry

theorem stateRestorationKnowledgeSoundness_implies_knowledgeSoundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    [ChallengesSampleable pSpec]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (ε : ℝ≥0) :
    verifier.stateRestorationKnowledgeSoundness relIn relOut
      (srInitFromBasic (pSpec := pSpec) init)
      (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl) ε →
      verifier.knowledgeSoundness init impl relIn relOut ε := by
  sorry

end ProtocolSpec
