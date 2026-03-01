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
    Pr[fun tr =>
        ¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) ∧
          sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec tr)
      | do
        let challenges ← sampleChallenges pSpec
        Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
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
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun tr =>
      ∃ witMid,
        ¬ ksf.toFun i.1.castSucc stmtIn
          (HVector.take i.1.castSucc pSpec tr)
          (extractor.extractMid i.1 stmtIn
            (HVector.take (i.1 + 1) pSpec tr) witMid) ∧
        ksf.toFun i.1.succ stmtIn
          (HVector.take (i.1 + 1) pSpec tr) witMid
      | do
        let challenges ← sampleChallenges pSpec
        Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrKnowledgeError i

/-! ## Bridge: RBR Knowledge Soundness → RBR Soundness -/

/-- Derive RBR soundness from RBR knowledge soundness by existentially quantifying
out the witness in the knowledge state function. The languages are derived from the
relations: `langIn = {s | ∃ w, (s, w) ∈ relIn}`, `langOut = {s | ∃ w, (s, w) ∈ relOut}`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
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
  let exp : ProbComp (Transcript pSpec) := do
    let challenges ← sampleChallenges pSpec
    Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
  let flipSF : ChallengeIndex pSpec → Transcript pSpec → Prop := fun j tr =>
    ¬ sf.toFun j.1 stmtIn (HVector.take j.1 pSpec tr) ∧
      sf.toFun (j.1 + 1) stmtIn (HVector.take (j.1 + 1) pSpec tr)
  let flipKSF : ChallengeIndex pSpec → Transcript pSpec → Prop := fun j tr =>
    ∃ witMid,
      ¬ ksf.toFun j.1.castSucc stmtIn
        (HVector.take j.1.castSucc pSpec tr)
        (extractor.extractMid j.1 stmtIn
          (HVector.take (j.1 + 1) pSpec tr) witMid) ∧
      ksf.toFun j.1.succ stmtIn
        (HVector.take (j.1 + 1) pSpec tr) witMid
  have hFlipLe : Pr[flipSF i | exp] ≤ Pr[flipKSF i | exp] := by
    refine probEvent_mono ?_
    intro tr _ hz
    rcases hz with ⟨hPrev, hSucc⟩
    have hiLe : i.1 ≤ pSpec.length := Nat.le_of_lt i.1.isLt
    have hiSuccLe : i.1 + 1 ≤ pSpec.length := Nat.succ_le_of_lt i.1.isLt
    rcases (by simpa [flipSF, sf, hiSuccLe] using hSucc) with ⟨witMid, hSuccKsf⟩
    refine ⟨witMid, ?_, ?_⟩
    · intro hPrevKsf
      have hPrevSf :
          sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) := by
        simp only [sf, hiLe, dite_true]
        exact ⟨_, hPrevKsf⟩
      exact hPrev hPrevSf
    · simpa using hSuccKsf
  have hKsfBound : Pr[flipKSF i | exp] ≤ rbrKnowledgeError i := by
    simpa [flipKSF, exp] using h stmtIn Output prover i σ0 hσ0
  calc
    Pr[flipSF i | exp] ≤ Pr[flipKSF i | exp] := hFlipLe
    _ ≤ rbrKnowledgeError i := hKsfBound

/-! ## Oracle-aware variants -/

/-- Oracle-aware state function where the predicate can depend on the verifier-start
oracle state `σ0`. -/
structure OracleAwareStateFunction
    (Inv : σ → Prop)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec) where
  toFun : (k : Nat) → StmtIn → PartialTranscript pSpec k → σ → Prop
  toFun_empty : ∀ stmt σ0,
    Inv σ0 →
    ((stmt ∈ langIn) ↔ toFun 0 stmt HVector.nil σ0)
  toFun_next : ∀ (k : Nat) (hk : k < pSpec.length),
    (pSpec.get ⟨k, hk⟩).isChallenge = false →
    ∀ stmt (tr : PartialTranscript pSpec k) σ0,
    ¬ toFun k stmt tr σ0 →
    ∀ (msg : (pSpec.get ⟨k, hk⟩).type),
    ¬ toFun (k + 1) stmt (PartialTranscript.concat pSpec hk tr msg) σ0
  toFun_full : ∀ stmt (tr : Transcript pSpec) (σ0 : σ),
    Inv σ0 →
    ¬ toFun pSpec.length stmt (PartialTranscript.ofTranscript tr) σ0 →
    Pr[(· ∈ langOut) | OptionT.mk do
      (simulateQ impl (verifier stmt tr)).run' σ0] = 0

/-- Oracle-aware RBR soundness. -/
def oracleAwareRbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (Inv : σ → Prop)
    (rbrError : ChallengeIndex pSpec → ℝ≥0) : Prop :=
  ∃ sf : OracleAwareStateFunction impl Inv langIn langOut verifier,
  ∀ stmtIn ∉ langIn,
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun tr =>
        ¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) σ0 ∧
          sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec tr) σ0
      | do
        let challenges ← sampleChallenges pSpec
        Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrError i

/-- Oracle-aware RBR extractor/state-function path for knowledge soundness. -/
structure OracleAwareKnowledgeStateFunction
    (Inv : σ → Prop)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    {WitMid : Fin (pSpec.length + 1) → Type}
    (extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid) where
  toFun : (k : Fin (pSpec.length + 1)) → StmtIn →
    PartialTranscript pSpec k → σ → WitMid k → Prop
  toFun_empty : ∀ stmtIn witMid σ0,
    Inv σ0 →
    ((⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn) ↔
      toFun 0 stmtIn HVector.nil σ0 witMid)
  toFun_next : ∀ (k : Fin pSpec.length),
    (pSpec.get k).isChallenge = false →
    ∀ stmtIn (tr : PartialTranscript pSpec k) msg σ0 witMid,
    toFun k.succ stmtIn (PartialTranscript.concat pSpec k.isLt tr msg) σ0 witMid →
    toFun k.castSucc stmtIn tr σ0
      (extractor.extractMid k stmtIn
        (PartialTranscript.concat pSpec k.isLt tr msg) witMid)
  toFun_full : ∀ stmtIn (tr : Transcript pSpec) witOut (σ0 : σ),
    Inv σ0 →
    Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut | OptionT.mk do
      (simulateQ impl (verifier stmtIn tr)).run' σ0] > 0 →
    toFun (.last pSpec.length) stmtIn (PartialTranscript.ofTranscript tr) σ0
      (extractor.extractOut stmtIn tr witOut)

/-- Oracle-aware RBR knowledge soundness. -/
def oracleAwareRbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    (Inv : σ → Prop)
    {WitMid : Fin (pSpec.length + 1) → Type}
    (extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid)
    (ksf : OracleAwareKnowledgeStateFunction impl Inv relIn relOut verifier extractor)
    (rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun tr =>
      ∃ witMid,
        ¬ ksf.toFun i.1.castSucc stmtIn
          (HVector.take i.1.castSucc pSpec tr) σ0
          (extractor.extractMid i.1 stmtIn
            (HVector.take (i.1 + 1) pSpec tr) witMid) ∧
        ksf.toFun i.1.succ stmtIn
          (HVector.take (i.1 + 1) pSpec tr) σ0 witMid
      | do
        let challenges ← sampleChallenges pSpec
        Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrKnowledgeError i

/-! ## Oracle-aware trace variants (for compositional oracle-state reasoning)

These definitions explicitly quantify over prefix-reachable oracle states produced by
prover execution up to round `k`. They are additive and do not replace the existing
definitions yet. -/

/-- `PrefixReachable` means: starting from `σ0`, there exists sampled challenges for
the first `k` rounds such that running the prover to round `k` can produce transcript
prefix `tr` and oracle state `σk`. -/
def PrefixReachable
    {Output : Type}
    (prover : Prover (OracleComp oSpec) Output pSpec)
    (k : Nat) (σ0 σk : σ) (tr : PartialTranscript pSpec k) : Prop :=
  ∃ (ch : Challenges (pSpec.take k)) (rem : Prover (OracleComp oSpec) Output (pSpec.drop k)),
    ((tr, rem), σk) ∈ support ((simulateQ impl (Prover.runToRound pSpec k prover ch)).run σ0)

/-- Trace-aware oracle state function: the predicate can depend on both verifier-start
state `σ0` and a prefix-reachable oracle state `σk` at round `k`. -/
structure OracleAwareTraceStateFunction
    (Inv : σ → Prop)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec) where
  toFun : (k : Nat) → StmtIn → PartialTranscript pSpec k → σ → σ → Prop
  toFun_empty : ∀ stmt σ0,
    Inv σ0 →
    ((stmt ∈ langIn) ↔ toFun 0 stmt HVector.nil σ0 σ0)
  toFun_next : ∀ (k : Nat) (hk : k < pSpec.length),
    (pSpec.get ⟨k, hk⟩).isChallenge = false →
    ∀ stmt (tr : PartialTranscript pSpec k) σ0 σk,
    ¬ toFun k stmt tr σ0 σk →
    ∀ (msg : (pSpec.get ⟨k, hk⟩).type) σk',
    ¬ toFun (k + 1) stmt (PartialTranscript.concat pSpec hk tr msg) σ0 σk'
  toFun_full : ∀ stmt (tr : Transcript pSpec) (σ0 σv : σ),
    Inv σ0 →
    ¬ toFun pSpec.length stmt (PartialTranscript.ofTranscript tr) σ0 σv →
    Pr[(· ∈ langOut) | OptionT.mk do
      (simulateQ impl (verifier stmt tr)).run' σv] = 0

/-- Trace-aware OracleAware RBR soundness. The bad event uses existential prefix-reachable
states at rounds `i` and `i+1`. -/
def oracleAwareTraceRbrSoundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (Inv : σ → Prop)
    (rbrError : ChallengeIndex pSpec → ℝ≥0) : Prop :=
  ∃ sf : OracleAwareTraceStateFunction impl Inv langIn langOut verifier,
  ∀ stmtIn ∉ langIn,
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun tr =>
        ∃ σi σi1,
          PrefixReachable (impl := impl) prover i.1 σ0 σi (HVector.take i.1 pSpec tr) ∧
          PrefixReachable (impl := impl) prover (i.1 + 1) σ0 σi1
            (HVector.take (i.1 + 1) pSpec tr) ∧
          ¬ sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) σ0 σi ∧
            sf.toFun (i.1 + 1) stmtIn (HVector.take (i.1 + 1) pSpec tr) σ0 σi1
      | do
        let challenges ← sampleChallenges pSpec
        Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrError i

/-- Trace-aware oracle-aware knowledge state function. -/
structure OracleAwareTraceKnowledgeStateFunction
    (Inv : σ → Prop)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    {WitMid : Fin (pSpec.length + 1) → Type}
    (extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid) where
  toFun : (k : Fin (pSpec.length + 1)) → StmtIn →
    PartialTranscript pSpec k → σ → σ → WitMid k → Prop
  toFun_empty : ∀ stmtIn witMid σ0,
    Inv σ0 →
    ((⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn) ↔
      toFun 0 stmtIn HVector.nil σ0 σ0 witMid)
  toFun_next : ∀ (k : Fin pSpec.length),
    (pSpec.get k).isChallenge = false →
    ∀ stmtIn (tr : PartialTranscript pSpec k) msg σ0 σk σk' witMid,
    toFun k.succ stmtIn (PartialTranscript.concat pSpec k.isLt tr msg) σ0 σk' witMid →
    toFun k.castSucc stmtIn tr σ0 σk
      (extractor.extractMid k stmtIn
        (PartialTranscript.concat pSpec k.isLt tr msg) witMid)
  toFun_full : ∀ stmtIn (tr : Transcript pSpec) witOut (σ0 σv : σ),
    Inv σ0 →
    Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut | OptionT.mk do
      (simulateQ impl (verifier stmtIn tr)).run' σv] > 0 →
    toFun (.last pSpec.length) stmtIn (PartialTranscript.ofTranscript tr) σ0 σv
      (extractor.extractOut stmtIn tr witOut)

/-- Trace-aware OracleAware RBR knowledge soundness. -/
def oracleAwareTraceRbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    (Inv : σ → Prop)
    {WitMid : Fin (pSpec.length + 1) → Type}
    (extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid)
    (ksf : OracleAwareTraceKnowledgeStateFunction impl Inv relIn relOut verifier extractor)
    (rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ i : ChallengeIndex pSpec,
  ∀ σ0 : σ,
  Inv σ0 →
    Pr[fun tr =>
      ∃ σi σi1 witMid,
        PrefixReachable (impl := impl) prover i.1 σ0 σi (HVector.take i.1 pSpec tr) ∧
        PrefixReachable (impl := impl) prover (i.1 + 1) σ0 σi1
          (HVector.take (i.1 + 1) pSpec tr) ∧
        ¬ ksf.toFun i.1.castSucc stmtIn
          (HVector.take i.1.castSucc pSpec tr) σ0 σi
          (extractor.extractMid i.1 stmtIn
            (HVector.take (i.1 + 1) pSpec tr) witMid) ∧
        ksf.toFun i.1.succ stmtIn
          (HVector.take (i.1 + 1) pSpec tr) σ0 σi1 witMid
      | do
        let challenges ← sampleChallenges pSpec
        Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
    ] ≤ rbrKnowledgeError i

namespace StateFunction

/-- Promote a legacy state function to an oracle-aware one by ignoring `σ0`. -/
def toOracleAware
    {Inv : σ → Prop}
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    (sf : StateFunction impl Inv langIn langOut verifier) :
    OracleAwareStateFunction impl Inv langIn langOut verifier where
  toFun := fun k stmt tr _ => sf.toFun k stmt tr
  toFun_empty := by
    intro stmt σ0 hσ0
    simpa using sf.toFun_empty stmt
  toFun_next := by
    intro k hk hnon stmt tr σ0 hFalse msg
    simpa using sf.toFun_next k hk hnon stmt tr hFalse msg
  toFun_full := by
    intro stmt tr σ0 hσ0 hFalse
    simpa using sf.toFun_full stmt tr σ0 hσ0 hFalse

end StateFunction

namespace KnowledgeStateFunction

/-- Promote a legacy knowledge state function to an oracle-aware one by ignoring `σ0`. -/
def toOracleAware
    {Inv : σ → Prop}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid}
    (ksf : KnowledgeStateFunction impl Inv relIn relOut verifier extractor) :
    OracleAwareKnowledgeStateFunction impl Inv relIn relOut verifier extractor where
  toFun := fun k stmt tr _ witMid => ksf.toFun k stmt tr witMid
  toFun_empty := by
    intro stmtIn witMid σ0 hσ0
    simpa using ksf.toFun_empty stmtIn witMid
  toFun_next := by
    intro k hnon stmtIn tr msg σ0 witMid hStep
    simpa using ksf.toFun_next k hnon stmtIn tr msg witMid hStep
  toFun_full := by
    intro stmtIn tr witOut σ0 hσ0 hPos
    simpa using ksf.toFun_full stmtIn tr witOut σ0 hσ0 hPos

end KnowledgeStateFunction

/-- Legacy RBR soundness implies oracle-aware RBR soundness. -/
theorem rbrSoundness_implies_oracleAwareRbrSoundness
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (h : rbrSoundness impl langIn langOut verifier Inv rbrError) :
    oracleAwareRbrSoundness impl langIn langOut verifier Inv rbrError := by
  rcases h with ⟨sf, hsf⟩
  refine ⟨sf.toOracleAware, ?_⟩
  intro stmtIn hstmtIn Output prover i σ0 hσ0
  simpa [StateFunction.toOracleAware] using hsf stmtIn hstmtIn Output prover i σ0 hσ0

/-- Legacy RBR knowledge soundness implies oracle-aware RBR knowledge soundness. -/
theorem rbrKnowledgeSoundness_implies_oracleAwareRbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv relIn relOut verifier extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) :
    oracleAwareRbrKnowledgeSoundness impl Inv extractor ksf.toOracleAware rbrKnowledgeError := by
  intro stmtIn Output prover i σ0 hσ0
  simpa [KnowledgeStateFunction.toOracleAware] using h stmtIn Output prover i σ0 hσ0

/-- Oracle-aware bridge: RBR knowledge soundness implies oracle-aware RBR soundness. -/
theorem oracleAwareRbrKnowledgeSoundness_implies_oracleAwareRbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid}
    {ksf : OracleAwareKnowledgeStateFunction impl Inv relIn relOut verifier extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (h : oracleAwareRbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) :
    oracleAwareRbrSoundness impl
      {s | ∃ w, (s, w) ∈ relIn}
      {s | ∃ w, (s, w) ∈ relOut}
      verifier Inv rbrKnowledgeError := by
  classical
  let sf : OracleAwareStateFunction impl Inv
      {s | ∃ w, (s, w) ∈ relIn}
      {s | ∃ w, (s, w) ∈ relOut}
      verifier := {
    toFun := fun (k : Nat) (stmt : StmtIn) (tr : PartialTranscript pSpec k) (σ0 : σ) =>
      if hk : k ≤ pSpec.length then
        ∃ witMid : WitMid ⟨k, Nat.lt_succ_of_le hk⟩,
          ksf.toFun ⟨k, Nat.lt_succ_of_le hk⟩ stmt tr σ0 witMid
      else
        False
    toFun_empty := by
      intro stmt σ0 hσ0
      simp only [Nat.zero_le, dite_true]
      constructor
      · intro hIn
        rcases hIn with ⟨witIn, hwitIn⟩
        refine ⟨cast extractor.eqIn.symm witIn, ?_⟩
        have : (stmt, cast extractor.eqIn (cast extractor.eqIn.symm witIn)) ∈ relIn := by
          simpa using hwitIn
        have hEmpty := (ksf.toFun_empty stmt (cast extractor.eqIn.symm witIn) σ0) hσ0
        exact hEmpty.mp this
      · intro hSf
        rcases hSf with ⟨witMid, hMid⟩
        refine ⟨cast extractor.eqIn witMid, ?_⟩
        have hEmpty := (ksf.toFun_empty stmt witMid σ0) hσ0
        exact hEmpty.mpr hMid
    toFun_next := by
      intro k hk hnon stmt tr σ0 hFalse msg hTrue
      have hkLe : k ≤ pSpec.length := Nat.le_of_lt hk
      have hkSuccLe : k + 1 ≤ pSpec.length := Nat.succ_le_of_lt hk
      rcases (by simpa [hkSuccLe] using hTrue) with ⟨witMid, hMidSucc⟩
      let ik : Fin pSpec.length := ⟨k, hk⟩
      have hMid :
          ksf.toFun ik.castSucc stmt tr σ0
            (extractor.extractMid ik stmt
              (PartialTranscript.concat pSpec hk tr msg) witMid) :=
        ksf.toFun_next ik hnon stmt tr msg σ0 witMid (by simpa [ik] using hMidSucc)
      have hSf :
          (if hk' : k ≤ pSpec.length then
            ∃ witMid : WitMid ⟨k, Nat.lt_succ_of_le hk'⟩,
              ksf.toFun ⟨k, Nat.lt_succ_of_le hk'⟩ stmt tr σ0 witMid
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
          ksf.toFun (.last pSpec.length) stmt (PartialTranscript.ofTranscript tr) σ0
            (extractor.extractOut stmt tr witOut) :=
        ksf.toFun_full stmt tr witOut σ0 hσ0 hPos
      have hSfLast :
          (if hk' : pSpec.length ≤ pSpec.length then
            ∃ witMid : WitMid ⟨pSpec.length, Nat.lt_succ_of_le hk'⟩,
              ksf.toFun ⟨pSpec.length, Nat.lt_succ_of_le hk'⟩ stmt
                (PartialTranscript.ofTranscript tr) σ0 witMid
          else False) := by
        simp only [le_rfl, dite_true]
        exact ⟨_, hMidLast⟩
      exact hFalse (by simpa using hSfLast)
  }
  refine ⟨sf, ?_⟩
  intro stmtIn _ Output prover i σ0 hσ0
  let exp : ProbComp (Transcript pSpec) := do
    let challenges ← sampleChallenges pSpec
    Prod.fst <$> (simulateQ impl (Prover.run pSpec prover challenges)).run' σ0
  let flipSF : ChallengeIndex pSpec → Transcript pSpec → Prop := fun j tr =>
    ¬ sf.toFun j.1 stmtIn (HVector.take j.1 pSpec tr) σ0 ∧
      sf.toFun (j.1 + 1) stmtIn (HVector.take (j.1 + 1) pSpec tr) σ0
  let flipKSF : ChallengeIndex pSpec → Transcript pSpec → Prop := fun j tr =>
    ∃ witMid,
      ¬ ksf.toFun j.1.castSucc stmtIn
        (HVector.take j.1.castSucc pSpec tr) σ0
        (extractor.extractMid j.1 stmtIn
          (HVector.take (j.1 + 1) pSpec tr) witMid) ∧
      ksf.toFun j.1.succ stmtIn
        (HVector.take (j.1 + 1) pSpec tr) σ0 witMid
  have hFlipLe : Pr[flipSF i | exp] ≤ Pr[flipKSF i | exp] := by
    refine probEvent_mono ?_
    intro tr _ hz
    rcases hz with ⟨hPrev, hSucc⟩
    have hiLe : i.1 ≤ pSpec.length := Nat.le_of_lt i.1.isLt
    have hiSuccLe : i.1 + 1 ≤ pSpec.length := Nat.succ_le_of_lt i.1.isLt
    rcases (by simpa [flipSF, sf, hiSuccLe] using hSucc) with ⟨witMid, hSuccKsf⟩
    refine ⟨witMid, ?_, ?_⟩
    · intro hPrevKsf
      have hPrevSf :
          sf.toFun i.1 stmtIn (HVector.take i.1 pSpec tr) σ0 := by
        simp only [sf, hiLe, dite_true]
        exact ⟨_, hPrevKsf⟩
      exact hPrev hPrevSf
    · simpa using hSuccKsf
  have hKsfBound : Pr[flipKSF i | exp] ≤ rbrKnowledgeError i := by
    simpa [flipKSF, exp] using h stmtIn Output prover i σ0 hσ0
  calc
    Pr[flipSF i | exp] ≤ Pr[flipKSF i | exp] := hFlipLe
    _ ≤ rbrKnowledgeError i := hKsfBound

end ProtocolSpec
