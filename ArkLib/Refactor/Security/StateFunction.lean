/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Defs

/-!
# Round-by-Round Security Definitions

State functions and round-by-round (RBR) soundness / knowledge soundness.

## Main definitions

- `Verifier.StateFunction` — deterministic state function
- `Verifier.rbrSoundness` — round-by-round soundness
- `Extractor.RoundByRound` — RBR extractor with intermediate witnesses
- `Verifier.KnowledgeStateFunction` — state function for knowledge soundness
- `Verifier.rbrKnowledgeSoundness` — round-by-round knowledge soundness
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

/-! ## Infrastructure -/

/-- Whether a round is a challenge (V_to_P) round. -/
def Round.isChallenge : Round → Bool
  | .V_to_P _ => true
  | .P_to_V _ _ => false

/-- Index type for challenge (V_to_P) rounds in a protocol spec. -/
def ChallengeIndex (pSpec : ProtocolSpec) : Type :=
  { i : Fin pSpec.length // (pSpec.get i).isChallenge = true }

instance (pSpec : ProtocolSpec) : Fintype (ChallengeIndex pSpec) :=
  Subtype.fintype _

/-- Convert a full transcript to a partial transcript at `pSpec.length`. -/
def PartialTranscript.ofTranscript {pSpec : ProtocolSpec} (tr : Transcript pSpec) :
    PartialTranscript pSpec pSpec.length := by
  simp only [PartialTranscript, List.take_length]
  exact tr

/-! ## State Function -/

variable {StmtIn WitIn StmtOut WitOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A deterministic state function for a verifier. -/
structure StateFunction
    (Inv : σ → Prop)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec) where
  toFun : (k : Nat) → StmtIn → PartialTranscript pSpec k → Prop
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt HVector.nil
  toFun_next : ∀ (k : Nat) (hk : k < pSpec.length),
    (pSpec.get ⟨k, hk⟩).isChallenge = false →
    ∀ stmt (tr : PartialTranscript pSpec k),
    ¬ toFun k stmt tr →
    ∀ (msg : (pSpec.get ⟨k, hk⟩).type),
    ¬ toFun (k + 1) stmt (PartialTranscript.concat pSpec hk tr msg)
  toFun_full : ∀ stmt (tr : Transcript pSpec) (σ0 : σ),
    Inv σ0 →
    ¬ toFun pSpec.length stmt (PartialTranscript.ofTranscript tr) →
    Pr[(· ∈ langOut) | OptionT.mk do
      (simulateQ impl (verifier stmt tr)).run' σ0] = 0

/-! ## RBR Soundness -/

/-- RBR soundness: there exists a state function such that for any adversary and
challenge round, the probability that a fresh challenge flips the state is bounded. -/
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (Inv : σ → Prop)
    (rbrError : ChallengeIndex pSpec → ℝ≥0) : Prop :=
  ∃ sf : StateFunction impl Inv langIn langOut verifier,
  ∀ stmtIn ∉ langIn,
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun (tr, _) =>
        ¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) ∧
          sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec tr)
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrError i

class IsRBRSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (Inv : σ → Prop) where
  rbrError : ChallengeIndex pSpec → ℝ≥0
  is_rbr_sound : rbrSoundness impl langIn langOut verifier Inv rbrError

/-! ## RBR Knowledge Soundness -/

/-- RBR extractor with intermediate witness types. -/
structure Extractor.RoundByRound
    (StmtIn WitIn WitOut : Type) (pSpec : ProtocolSpec)
    (WitMid : Fin (pSpec.length + 1) → Type) where
  eqIn : WitMid 0 = WitIn
  extractMid : (k : Fin pSpec.length) → StmtIn →
    PartialTranscript pSpec (k + 1) → WitMid k.succ → WitMid k.castSucc
  extractOut : StmtIn → Transcript pSpec → WitOut → WitMid (.last pSpec.length)

/-- A knowledge state function: maps (round, stmt, partial_transcript, witness) to Prop. -/
structure KnowledgeStateFunction
    (Inv : σ → Prop)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    {WitMid : Fin (pSpec.length + 1) → Type}
    (extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid) where
  toFun : (k : Fin (pSpec.length + 1)) → StmtIn →
    PartialTranscript pSpec k → WitMid k → Prop
  toFun_empty : ∀ stmtIn witMid,
    ⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn ↔ toFun 0 stmtIn HVector.nil witMid
  toFun_next : ∀ (k : Fin pSpec.length),
    (pSpec.get k).isChallenge = false →
    ∀ stmtIn (tr : PartialTranscript pSpec k) msg witMid,
    toFun k.succ stmtIn (PartialTranscript.concat pSpec k.isLt tr msg) witMid →
    toFun k.castSucc stmtIn tr
      (extractor.extractMid k stmtIn
        (PartialTranscript.concat pSpec k.isLt tr msg) witMid)
  toFun_full : ∀ stmtIn (tr : Transcript pSpec) witOut (σ0 : σ),
    Inv σ0 →
    Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut | OptionT.mk do
      (simulateQ impl (verifier stmtIn tr)).run' σ0] > 0 →
    toFun (.last pSpec.length) stmtIn (PartialTranscript.ofTranscript tr)
      (extractor.extractOut stmtIn tr witOut)

/-- RBR knowledge soundness with given extractor and knowledge state function.
The per-round error bound says that a fresh challenge cannot flip the knowledge
state function from bad to good with probability more than `rbrKnowledgeError i`. -/
def rbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    (Inv : σ → Prop)
    {WitMid : Fin (pSpec.length + 1) → Type}
    (extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid)
    (ksf : KnowledgeStateFunction impl Inv relIn relOut verifier extractor)
    (rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ prover : Prover (OracleComp oSpec) (StmtOut × WitOut) pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun (tr, _) =>
      ∃ witMid,
        ¬ ksf.toFun i.1.castSucc stmtIn
          (HVector.take i.1.castSucc pSpec tr)
          (extractor.extractMid i.1 stmtIn
            (HVector.take (i.1 + 1) pSpec tr) witMid) ∧
        ksf.toFun i.1.succ stmtIn
          (HVector.take (i.1 + 1) pSpec tr) witMid
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrKnowledgeError i

/-! ## Bridge: RBR Knowledge Soundness → RBR Soundness -/

/-- Derive RBR soundness from RBR knowledge soundness by existentially quantifying
out the witness in the knowledge state function. The languages are derived from the
relations: `langIn = {s | ∃ w, (s, w) ∈ relIn}`, `langOut = {s | ∃ w, (s, w) ∈ relOut}`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    [Inhabited StmtOut] [Inhabited WitOut]
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv relIn relOut verifier extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) :
    rbrSoundness impl
      {s | ∃ w, (s, w) ∈ relIn}
      {s | ∃ w, (s, w) ∈ relOut}
      verifier Inv rbrKnowledgeError := by
  classical
  let sf : StateFunction impl Inv
      {s | ∃ w, (s, w) ∈ relIn}
      {s | ∃ w, (s, w) ∈ relOut}
      verifier := {
    toFun := fun (k : Nat) (stmt : StmtIn) (tr : PartialTranscript pSpec k) =>
      if hk : k ≤ pSpec.length then
        ∃ witMid : WitMid ⟨k, Nat.lt_succ_of_le hk⟩,
          ksf.toFun ⟨k, Nat.lt_succ_of_le hk⟩ stmt tr witMid
      else
        False
    toFun_empty := by
      intro stmt
      simp only [Nat.zero_le, dite_true]
      constructor
      · intro hIn
        rcases hIn with ⟨witIn, hwitIn⟩
        refine ⟨cast extractor.eqIn.symm witIn, ?_⟩
        have : (stmt, cast extractor.eqIn (cast extractor.eqIn.symm witIn)) ∈ relIn := by
          simpa using hwitIn
        simpa using (ksf.toFun_empty stmt (cast extractor.eqIn.symm witIn)).mp this
      · intro hSf
        rcases hSf with ⟨witMid, hMid⟩
        refine ⟨cast extractor.eqIn witMid, ?_⟩
        simpa using (ksf.toFun_empty stmt witMid).mpr hMid
    toFun_next := by
      intro k hk hnon stmt tr hFalse msg hTrue
      have hkLe : k ≤ pSpec.length := Nat.le_of_lt hk
      have hkSuccLe : k + 1 ≤ pSpec.length := Nat.succ_le_of_lt hk
      rcases (by simpa [hkSuccLe] using hTrue) with ⟨witMid, hMidSucc⟩
      let ik : Fin pSpec.length := ⟨k, hk⟩
      have hMid :
          ksf.toFun ik.castSucc stmt tr
            (extractor.extractMid ik stmt
              (PartialTranscript.concat pSpec hk tr msg) witMid) :=
        ksf.toFun_next ik hnon stmt tr msg witMid (by simpa [ik] using hMidSucc)
      have hSf :
          (if hk' : k ≤ pSpec.length then
            ∃ witMid : WitMid ⟨k, Nat.lt_succ_of_le hk'⟩,
              ksf.toFun ⟨k, Nat.lt_succ_of_le hk'⟩ stmt tr witMid
          else False) := by
        simp only [hkLe, dite_true]
        refine ⟨cast (by simp [ik]) (extractor.extractMid ik stmt
            (PartialTranscript.concat pSpec hk tr msg) witMid), ?_⟩
        simpa [ik] using hMid
      exact hFalse (by simpa using hSf)
    toFun_full := by
      intro stmt tr σ0 hσ0 hFalse
      rw [probEvent_eq_zero_iff]
      intro stmtOut hStmtOut hLangOut
      rcases hLangOut with ⟨witOut, hRelOut⟩
      have hPos :
          Pr[fun s => (s, witOut) ∈ relOut
            | OptionT.mk do
              (simulateQ impl (verifier stmt tr)).run' σ0] > 0 := by
        exact (probEvent_pos_iff).2 ⟨stmtOut, hStmtOut, hRelOut⟩
      have hMidLast :
          ksf.toFun (.last pSpec.length) stmt (PartialTranscript.ofTranscript tr)
            (extractor.extractOut stmt tr witOut) :=
        ksf.toFun_full stmt tr witOut σ0 hσ0 hPos
      have hSfLast :
          (if hk' : pSpec.length ≤ pSpec.length then
            ∃ witMid : WitMid ⟨pSpec.length, Nat.lt_succ_of_le hk'⟩,
              ksf.toFun ⟨pSpec.length, Nat.lt_succ_of_le hk'⟩ stmt
                (PartialTranscript.ofTranscript tr) witMid
          else False) := by
        simp only [le_rfl, dite_true]
        exact ⟨_, hMidLast⟩
      exact hFalse (by simpa using hSfLast)
  }
  refine ⟨sf, ?_⟩
  intro stmtIn _ Output prover i σ0 hσ0
  let dummyOut : StmtOut × WitOut := default
  let prover' : Prover (OracleComp oSpec) (StmtOut × WitOut) pSpec :=
    Prover.mapOutput (fun _ : Output => dummyOut) pSpec prover
  let exp : ProbComp (Transcript pSpec × Output) := do
    let challenges ← sampleChallenges pSpec
    (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
  let exp' : ProbComp (Transcript pSpec × (StmtOut × WitOut)) := do
    let challenges ← sampleChallenges pSpec
    (simulateQ impl (Prover.run pSpec prover' challenges)).run' σ0
  let flipSF : ChallengeIndex pSpec → (Transcript pSpec × Output) → Prop := fun j z =>
    ¬ sf.toFun j.1 stmtIn (HVector.take j.1 pSpec z.1) ∧
      sf.toFun (j.1 + 1) stmtIn (HVector.take (j.1 + 1) pSpec z.1)
  let flipSF' : ChallengeIndex pSpec → (Transcript pSpec × (StmtOut × WitOut)) → Prop := fun j z =>
    ¬ sf.toFun j.1 stmtIn (HVector.take j.1 pSpec z.1) ∧
      sf.toFun (j.1 + 1) stmtIn (HVector.take (j.1 + 1) pSpec z.1)
  let flipKSF : ChallengeIndex pSpec → (Transcript pSpec × (StmtOut × WitOut)) → Prop := fun j z =>
    ∃ witMid,
      ¬ ksf.toFun j.1.castSucc stmtIn
        (HVector.take j.1.castSucc pSpec z.1)
        (extractor.extractMid j.1 stmtIn
          (HVector.take (j.1 + 1) pSpec z.1) witMid) ∧
      ksf.toFun j.1.succ stmtIn
        (HVector.take (j.1 + 1) pSpec z.1) witMid
  have run'_map_local :
      ∀ {α β : Type} (f : α → β) (x : StateT σ ProbComp α) (s : σ),
        (f <$> x).run' s = f <$> x.run' s := by
    intro α β f x s
    change (fun x : β × σ => x.1) <$> (f <$> x).run s =
      f <$> ((fun x : α × σ => x.1) <$> x.run s)
    rw [StateT.run_map]
    simp [Functor.map_map]
  have hExpMap : exp' = (fun z : Transcript pSpec × Output => (z.1, dummyOut)) <$> exp := by
    simp [exp', exp, prover', Prover.run_mapOutput, simulateQ_map]
  have hFlipEq : Pr[flipSF i | exp] = Pr[flipSF' i | exp'] := by
    rw [hExpMap, probEvent_map]
    rfl
  have hFlipLe : Pr[flipSF' i | exp'] ≤ Pr[flipKSF i | exp'] := by
    refine probEvent_mono ?_
    intro z _ hz
    rcases hz with ⟨hPrev, hSucc⟩
    have hiLe : i.1 ≤ pSpec.length := Nat.le_of_lt i.1.isLt
    have hiSuccLe : i.1 + 1 ≤ pSpec.length := Nat.succ_le_of_lt i.1.isLt
    rcases (by simpa [flipSF', sf, hiSuccLe] using hSucc) with ⟨witMid, hSuccKsf⟩
    refine ⟨witMid, ?_, ?_⟩
    · intro hPrevKsf
      have hPrevSf :
          sf.toFun i.1 stmtIn (HVector.take i.1 pSpec z.1) := by
        simp only [sf, hiLe, dite_true]
        exact ⟨_, hPrevKsf⟩
      exact hPrev hPrevSf
    · simpa using hSuccKsf
  have hKsfBound : Pr[flipKSF i | exp'] ≤ rbrKnowledgeError i := by
    simpa [flipKSF, exp', prover'] using h stmtIn prover' i σ0 hσ0
  calc
    Pr[flipSF i | exp] = Pr[flipSF' i | exp'] := hFlipEq
    _ ≤ Pr[flipKSF i | exp'] := hFlipLe
    _ ≤ rbrKnowledgeError i := hKsfBound

end ProtocolSpec
