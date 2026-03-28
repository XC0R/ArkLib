/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Defs
import ArkLib.Refactor.FiatShamir
import ToMathlib.Control.Monad.Commutative

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
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro σ0 chal chTail
      simp
  | query_bind t oa ih =>
      intro σ0 chal chTail
      cases t with
      | inl q =>
          simp only [add_apply_inl, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, liftFSTail, map_eq_bind_pure_comp, CompTriple.comp_eq,
            bind_pure, srImplFromBasicAux, bind_pure_comp, StateT.run_bind, bind_assoc]
          change
            (StateT.run
                (fun st ↦ impl q st.1 >>= pure ∘ fun a ↦ (a.1, a.2, st.2))
                (σ0, chal ::ₕ chTail) >>= fun p =>
              (simulateQ
                (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                  (pSpec := (.V_to_P T) :: tl) impl)
                (simulateQ (liftFSTail oSpec StmtIn acc T tl) (oa p.1))).run p.2) =
            (StateT.run
                (fun st ↦ impl q st.1 >>= pure ∘ fun a ↦ (a.1, a.2, st.2))
                (σ0, chTail) >>= fun x =>
              (simulateQ
                (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                  (pSpec := tl) impl)
                (oa x.1)).run x.2 >>= pure ∘
                  fun z : α × (σ × Challenges tl) =>
                    (z.1, z.2.1, chal ::ₕ z.2.2))
          have hleft :
              StateT.run
                  (fun st ↦ impl q st.1 >>= pure ∘ fun a ↦ (a.1, a.2, st.2))
                  (σ0, chal ::ₕ chTail) =
                (impl q).run σ0 >>= pure ∘ fun a ↦ (a.1, a.2, chal ::ₕ chTail) := rfl
          have hright :
              StateT.run
                  (fun st ↦ impl q st.1 >>= pure ∘ fun a ↦ (a.1, a.2, st.2))
                  (σ0, chTail) =
                (impl q).run σ0 >>= pure ∘ fun a ↦ (a.1, a.2, chTail) := rfl
          rw [hleft, hright]
          simp only [bind_assoc]
          refine bind_congr (x := (impl q).run σ0) (fun a => ?_)
          simpa [map_eq_bind_pure_comp] using ih a.1 a.2 chal chTail
      | inr q =>
          simpa [liftFSTail, srImplFromBasicAux, simulateQ_query, map_eq_bind_pure_comp,
            bind_assoc, StateT.run, StateT.run_bind]
            using ih (srReplayChallengeAux (StmtIn := StmtIn) acc tl chTail q) σ0 chal chTail

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
      simp [Prover.runFS, Messages.deriveTranscript, Prover.run]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover accMsgs ch σ0
          rcases prover with ⟨msg, cont⟩
          simp only [srImplFromBasicAux_cons_P_to_V, Prover.runFS, bind_pure_comp,
            Messages.deriveTranscript, Functor.map_map, bind_assoc, bind_map_left,
            HVector.head_cons, HVector.tail_cons, simulateQ_bind, simulateQ_map, StateT.run_bind,
            simulateQ_srImplFromBasicAux_liftM_run, StateT.run_map, Prover.run, map_bind]
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
              simp only [Prover.runFS, Prod.mk.eta, bind_pure, Messages.deriveTranscript,
                bind_pure_comp, map_bind, Functor.map_map, bind_assoc, simulateQ_bind,
                simulateQ_query, OracleQuery.input_query, add_apply_inr, Sum.elim_inl,
                OracleQuery.cont_query, id_map, simulateQ_map, id_eq, StateT.run_bind,
                StateT.run_map, Prover.run]
              have hHeadQuery :
                  (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                    (pSpec := (.V_to_P T) :: tl) impl
                    (Sum.inr (Sum.inl (stmt, accMsgs)))).run (σ0, chal, chTail) =
                    pure (chal, σ0, chal, chTail) := by
                rfl
              rw [hHeadQuery]
              have hLiftM :
                  (simulateQ
                      (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                        (pSpec := (.V_to_P T) :: tl) impl)
                      (liftM (prover chal))).run (σ0, chal, chTail) =
                    ((fun z : Prover (OracleComp oSpec) Output tl × σ =>
                        (z.1, (z.2, chal ::ₕ chTail))) <$>
                      (simulateQ impl (prover chal)).run σ0) := by
                simpa using
                  (simulateQ_srImplFromBasicAux_liftM_run (StmtIn := StmtIn) (acc := acc)
                    (pSpec := (.V_to_P T) :: tl) (impl := impl) (oa := prover chal)
                    (σ0 := σ0) (ch := chal ::ₕ chTail))
              simp only [id_eq, pure_bind]
              rw [hLiftM]
              simp only [bind_map_left]
              refine bind_congr (x := (simulateQ impl (prover chal)).run σ0) (fun a => ?_)
              have hih := ih (acc := acc) (prover := a.1)
                (accMsgs := accMsgs) (ch := chTail) (σ0 := a.2)
              have hih' :
                  ((fun z : (Transcript tl × Output) × (σ × Challenges tl) =>
                      ((Transcript.cons (r := .V_to_P T) chal z.1.1, z.1.2),
                        (z.2.1, chal ::ₕ z.2.2))) <$>
                    (simulateQ
                      (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                        (pSpec := tl) impl) (do
                          let (msgs, out) ←
                            Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs
                          let tr ←
                            Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc tl
                              accMsgs msgs
                          pure (tr, out))).run (a.2, chTail)) =
                  ((fun z : (Transcript tl × Output) × σ =>
                      ((Transcript.cons (r := .V_to_P T) chal z.1.1, z.1.2),
                        (z.2, chal ::ₕ chTail))) <$>
                    (simulateQ impl (Prover.run tl a.1 chTail)).run a.2) := by
                simpa [Prover.run, bind_assoc, map_eq_bind_pure_comp] using
                  congrArg (fun mx =>
                    (fun z : (Transcript tl × Output) × (σ × Challenges tl) =>
                      ((Transcript.cons (r := .V_to_P T) chal z.1.1, z.1.2),
                        (z.2.1, chal ::ₕ z.2.2))) <$> mx) hih
              have hRunFSTail :
                  (simulateQ
                      (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                        (pSpec := (.V_to_P T) :: tl) impl)
                      (simulateQ (liftFSTail oSpec StmtIn acc T tl)
                        (Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs))).run
                    (a.2, chal ::ₕ chTail) =
                  ((fun z : (Messages tl × Output) × (σ × Challenges tl) =>
                      (z.1, (z.2.1, chal ::ₕ z.2.2))) <$>
                    (simulateQ
                      (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                        (pSpec := tl) impl)
                      (Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs)).run
                    (a.2, chTail)) := by
                simpa [bind_assoc] using
                  (simulateQ_srImplFromBasicAux_liftFSTail_run (StmtIn := StmtIn) (acc := acc)
                    (T := T) (tl := tl) (impl := impl)
                    (oa := Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs)
                    (σ0 := a.2) (chal := chal) (chTail := chTail))
              calc
                (do
                  let p ←
                    (simulateQ
                        (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                          (pSpec := (.V_to_P T) :: tl) impl)
                        (simulateQ (liftFSTail oSpec StmtIn acc T tl)
                          (Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs))).run
                      (a.2, chal ::ₕ chTail)
                  let p_1 ←
                    (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                      (pSpec := (.V_to_P T) :: tl) impl
                      (Sum.inr (Sum.inl (stmt, accMsgs)))).run p.2
                  (fun p_2 =>
                      ((p_1.1 ::ₕ p_2.1, p.1.2), p_2.2)) <$>
                    (simulateQ
                        (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                          (pSpec := (.V_to_P T) :: tl) impl)
                        (simulateQ (liftFSTail oSpec StmtIn acc T tl)
                          (Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc tl
                            accMsgs p.1.1))).run
                      p_1.2)
                    =
                    ((fun z : (Transcript tl × Output) × (σ × Challenges tl) =>
                        ((Transcript.cons (r := .V_to_P T) chal z.1.1, z.1.2),
                          (z.2.1, chal ::ₕ z.2.2))) <$>
                      (simulateQ
                        (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                          (pSpec := tl) impl) (do
                            let (msgs, out) ←
                              Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs
                            let tr ←
                              Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc tl
                                accMsgs msgs
                            pure (tr, out))).run (a.2, chTail)) := by
                  rw [hRunFSTail]
                  simp only [map_eq_bind_pure_comp, add_apply_inr, Sum.elim_inl, bind_assoc,
                    Function.comp_apply, pure_bind, bind_pure_comp, simulateQ_bind,
                    simulateQ_pure, StateT.run_bind, StateT.run_pure]
                  refine bind_congr (x :=
                    (simulateQ
                      (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                        (pSpec := tl) impl)
                      (Prover.runFS (oSpec := oSpec) (stmt := stmt) acc tl a.1 accMsgs)).run
                      (a.2, chTail)) (fun p => ?_)
                  have hReplay :
                      (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                        (pSpec := (.V_to_P T) :: tl) impl
                        (Sum.inr (Sum.inl (stmt, accMsgs)))).run
                        (p.2.1, chal ::ₕ p.2.2) =
                      pure (chal, (p.2.1, chal ::ₕ p.2.2)) := by
                    rfl
                  rw [hReplay]
                  have hDeriveTail :
                      (simulateQ
                          (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                            (pSpec := (.V_to_P T) :: tl) impl)
                          (simulateQ (liftFSTail oSpec StmtIn acc T tl)
                            (Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc tl
                              accMsgs p.1.1))).run
                        (p.2.1, chal ::ₕ p.2.2) =
                      ((fun z : Transcript tl × (σ × Challenges tl) =>
                          (z.1, (z.2.1, chal ::ₕ z.2.2))) <$>
                        (simulateQ
                          (srImplFromBasicAux (StmtIn := StmtIn) (acc := acc)
                            (pSpec := tl) impl)
                          (Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc tl
                            accMsgs p.1.1)).run
                        (p.2.1, p.2.2)) := by
                    simpa [bind_assoc] using
                      (simulateQ_srImplFromBasicAux_liftFSTail_run (StmtIn := StmtIn)
                        (acc := acc) (T := T) (tl := tl) (impl := impl)
                        (oa := Messages.deriveTranscript (oSpec := oSpec) (stmt := stmt) acc tl
                          accMsgs p.1.1)
                        (σ0 := p.2.1) (chal := chal) (chTail := p.2.2))
                  simp only [id_eq, pure_bind]
                  rw [hDeriveTail]
                  simp [bind_assoc, map_eq_bind_pure_comp, Transcript.cons]
                _ = ((fun z : (Transcript tl × Output) × σ =>
                        ((Transcript.cons (r := .V_to_P T) chal z.1.1, z.1.2),
                          (z.2, chal ::ₕ chTail))) <$>
                      (simulateQ impl (Prover.run tl a.1 chTail)).run a.2) := hih'

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
  unfold srSoundnessGame Prover.toStateRestorationSoundness
  simpa [bind_assoc] using
    congrArg (fun mx =>
      (fun z : (Transcript pSpec × Output) × (σ × Challenges pSpec) =>
        ((z.1.1, stmtIn), z.2)) <$> mx)
      (runFS_deriveTranscript_eq_run (impl := impl) (stmt := stmtIn)
        (acc := []) (pSpec := pSpec) (prover := prover)
        (accMsgs := (HVector.nil : HVector id [])) (ch := ch) (σ0 := σ0))

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
  unfold srKnowledgeSoundnessGame Prover.toStateRestorationKnowledgeSoundness
  simpa [bind_assoc] using
    congrArg (fun mx =>
      (fun z : (Transcript pSpec × WitOut) × (σ × Challenges pSpec) =>
        ((z.1.1, stmtIn, z.1.2), z.2)) <$> mx)
      (runFS_deriveTranscript_eq_run (impl := impl) (stmt := stmtIn)
        (acc := []) (pSpec := pSpec) (prover := prover)
        (accMsgs := (HVector.nil : HVector id [])) (ch := ch) (σ0 := σ0))

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

private theorem probComp_map_bind_eq
    {α β γ : Type _} (mx : ProbComp α) (g : α → ProbComp β) (f : β → γ) :
    (mx >>= fun a => f <$> g a) = f <$> (mx >>= g) := by
  simp only [map_eq_bind_pure_comp, bind_assoc]

private theorem srSoundnessExperiment_adapter_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut Output : Type} {pSpec : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    (prover : Prover (OracleComp oSpec) Output pSpec)
    (σ0 : σ) (ch : Challenges pSpec) :
    (simulateQ (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl) (do
      let (tr, stmtIn') ← srSoundnessGame
        (Prover.toStateRestorationSoundness (oSpec := oSpec) (pSpec := pSpec) stmtIn prover)
      let stmtOut ← (verifier stmtIn' tr).run
      pure (stmtIn', stmtOut))).run' (σ0, ch) =
    (fun z : Option StmtOut × Output => (stmtIn, z.1)) <$>
      (simulateQ impl (do
        let (tr, out) ← Prover.run pSpec prover ch
        let verResult ← (verifier stmtIn tr).run
        return (verResult, out))).run' σ0 := by
  sorry

private theorem srKnowledgeSoundnessExperiment_adapter_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}
    {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (extractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn)
    (prover : Prover (OracleComp oSpec) WitOut pSpec)
    (σ0 : σ) (ch : Challenges pSpec) :
    (simulateQ (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl) (do
      let (tr, stmtIn', witOut) ← srKnowledgeSoundnessGame
        (Prover.toStateRestorationKnowledgeSoundness
          (oSpec := oSpec) (pSpec := pSpec) stmtIn prover)
      let stmtOut ← (verifier stmtIn' tr).run
      let witIn ← (extractor stmtIn' witOut tr).run
      pure (stmtIn', witIn, stmtOut, witOut))).run' (σ0, ch) =
    (fun z : Option StmtOut × WitOut × Option WitIn => (stmtIn, z.2.2, z.1, z.2.1)) <$>
      (simulateQ impl (do
        let (tr, witOut) ← Prover.run pSpec prover ch
        let verResult ← (verifier stmtIn tr).run
        let witIn ← (extractor stmtIn witOut tr).run
        return (verResult, witOut, witIn))).run' σ0 := by
  sorry

theorem stateRestorationSoundness_implies_soundness
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {pSpec : ProtocolSpec}
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
  intro hSR Output prover stmtIn hstmtIn
  let accept : Option StmtOut × Output → Prop :=
    fun z => ∃ s ∈ langOut, z.1 = some s
  let srAccept : StmtIn × Option StmtOut → Prop := fun
    | (stmt, some stmtOut) => stmtOut ∈ langOut ∧ stmt ∉ langIn
    | _ => False
  let step : Challenges pSpec → σ → ProbComp (Option StmtOut × Output) :=
    fun ch σ0 =>
      (simulateQ impl (do
        let (tr, out) ← Prover.run pSpec prover ch
        let verResult ← (verifier stmtIn tr).run
        return (verResult, out))).run' σ0
  let expInitFirst : ProbComp (Option StmtOut × Output) := do
    let σ0 ← init
    let ch ← sampleChallenges pSpec
    step ch σ0
  let expBasic : ProbComp (Option StmtOut × Output) := do
    let ch ← sampleChallenges pSpec
    step ch (← init)
  have hSrCompEq :
      (do
        StateT.run'
          (simulateQ (srImplFromBasic (StmtIn := StmtIn) (pSpec := pSpec) impl) (do
            let (tr, stmtIn') ← srSoundnessGame
              (Prover.toStateRestorationSoundness
                (oSpec := oSpec) (pSpec := pSpec) stmtIn prover)
            let stmtOut ← (verifier stmtIn' tr).run
            pure (stmtIn', stmtOut)))
          (← srInitFromBasic (pSpec := pSpec) init)) =
      (fun z : Option StmtOut × Output => (stmtIn, z.1)) <$> expInitFirst := by
    unfold expInitFirst srInitFromBasic step
    simp_rw [srSoundnessExperiment_adapter_eq (impl := impl) (verifier := verifier)
      (stmtIn := stmtIn) (prover := prover)]
    simp_rw [probComp_map_bind_eq]
    simp [bind_assoc]
  have hSRBound := hSR
    (Prover.toStateRestorationSoundness (oSpec := oSpec) (pSpec := pSpec) stmtIn prover)
  rw [hSrCompEq, probEvent_map] at hSRBound
  have hInitFirstBound : Pr[accept | expInitFirst] ≤ ε := by
    rw [probEvent_ext] at hSRBound
    · simpa using hSRBound
    · intro x hx
      cases h : x.1 <;> simp [accept, h, hstmtIn]
  have hSwap :
      Pr[accept | expInitFirst] = Pr[accept | expBasic] := by
    unfold expInitFirst expBasic
    simpa [step] using
      (probEvent_bind_bind_swap init (sampleChallenges pSpec) (fun σ0 ch => step ch σ0) accept)
  have hBasicBound : Pr[accept | expBasic] ≤ ε := by
    rw [← hSwap]
    exact hInitFirstBound
  simpa [Verifier.soundness, accept, expBasic, step] using hBasicBound

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
  -- The current SR knowledge-soundness notion only charges runs where the SR extractor
  -- returns `some witIn`; plain knowledge soundness also charges extractor failure (`none`).
  -- Repairing that mismatch requires either strengthening the SR notion or adding an
  -- explicit total-extractor hypothesis.
  sorry

end ProtocolSpec
