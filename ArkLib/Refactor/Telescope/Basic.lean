/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.ProtocolSpec
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Telescopic Protocol Specifications

`ProtocolCtx` is a W-type that generalizes `ProtocolSpec` (= `List Round`) so that
the type of each round can depend on the values exchanged in earlier rounds. When the
`rest` functions are constant, a `ProtocolCtx` degenerates to the current list-based
`ProtocolSpec`.

## Main definitions

- `ProtocolCtx` — telescopic protocol specification (W-type over `Round`)
- `ProtocolCtx.Transcript` — dependent sigma chain of exchanged values
- `ProtocolCtx.Prover` — prover with transcript-dependent output
- `ProtocolCtx.Challenger` — interactive challenger (dual of prover)
- `ProtocolCtx.Verifier` — verifier with transcript-dependent output
- `ProtocolCtx.Prover.run` — execute prover against a challenger
- `ProtocolCtx.Prover.splitPrefix` — extract first-stage prover from a composition
- `ProtocolCtx.append` — dependent concatenation
- `ProtocolCtx.Prover.comp` — sequential composition over dependent append
- `ProtocolCtx.ofList` — embed a non-dependent `ProtocolSpec`
- `ProtocolCtx.PartialTranscript` — prefix of a transcript (first `n` entries)
- `ProtocolCtx.SF` — recursive state function for round-by-round soundness
- `ProtocolCtx.Transcript.split` / `join` — decompose/recompose transcripts
- `ProtocolCtx.Verifier.comp` — sequential composition of verifiers
- `ProtocolCtx.Challenger.comp` — sequential composition of challengers
- `ProtocolCtx.SF.comp` — sequential composition of state functions
- `ProtocolCtx.chain` — indexed stage-family concatenation
- `ProtocolCtx.Verifier.compFrom` — iterate a stage-indexed verifier family
- `ProtocolCtx.replicate` — n-fold replication of a protocol context
- `ProtocolCtx.Verifier.compNth` — n-fold verifier self-composition
- `ProtocolCtxM` — variant where the monad can change between rounds

## Design notes

### Blockers from dependent types

1. **Pre-sampling impossible**: `sampleChallenges` cannot be defined for general
   `ProtocolCtx` because challenge types depend on earlier values. Use
   `randomChallenger` (interleaved sampling) instead. For non-dependent protocols
   (via `ofList`), the two are distributionally equivalent (proof deferred).

2. **No static `ChallengeIndex`**: In a telescope, whether round `k` is `V_to_P`
   depends on the values exchanged in earlier rounds. The recursive `SF` approach
   avoids `ChallengeIndex` entirely — each `V_to_P` node carries its own bound.

3. **`splitPrefix` resolved**: With transcript-dependent output types, `splitPrefix`
   is defined cleanly — the first-stage output IS a `Prover` for the second stage,
   absorbing the path-dependence without sigma types.

4. **`ofList` bridge deferred**: Proving `rbrSoundness` for `ProtocolCtx.ofList pSpec`
   implies list-based `rbrSoundness` for `pSpec` requires a distributional equivalence
   argument.

### Statement-dependent protocols

When the protocol structure depends on the statement (e.g., the number of rounds is
`log n` where `n` is in the statement, or messages are elements of `F_p` where `p` is
in the statement), use an external family `ctx : StmtIn → ProtocolCtx`. All definitions
in this file lift pointwise by fixing `s : StmtIn` and working with `ctx s`:

- `Prover`: `fun s => Prover m (ctx s) (Output s)`
- `Verifier`: `fun s tr => verifier s tr` where `tr : Transcript (ctx s)`
- `append`: `fun s => (ctx₁ s).append (ctx₂ s)`
- `rbrSoundness`: `∀ s, rbrSoundness (ctx s) (lang s) (rejects s) (v s)`

This approach avoids parameterizing `ProtocolCtx` by `StmtIn` (which would break
`append` — different statement values can yield different protocol shapes that cannot
be merged into a single inductive value) and keeps the `Prover` type free of `StmtIn`
(preserving the honest/cheating separation).
-/

open OracleComp

/-! ## Core inductive type -/

/-- A telescopic protocol specification. Each constructor carries a function
`rest : T → ProtocolCtx` so that the remaining protocol can depend on the value
exchanged at this round. -/
inductive ProtocolCtx : Type 1 where
  | nil : ProtocolCtx
  | P_to_V (T : Type) (oi : OracleInterface T) (rest : T → ProtocolCtx) : ProtocolCtx
  | V_to_P (T : Type) (rest : T → ProtocolCtx) : ProtocolCtx

namespace ProtocolCtx

/-! ## Transcript -/

/-- The transcript of a telescopic protocol is a chain of dependent pairs.
The type of each entry depends on the values of all preceding entries. -/
def Transcript : ProtocolCtx → Type
  | .nil => PUnit
  | .P_to_V T _ rest => (t : T) × Transcript (rest t)
  | .V_to_P T rest => (t : T) × Transcript (rest t)

/-! ## Prover -/

/-- Coinductive prover type with transcript-dependent output, defined by structural
recursion on `ProtocolCtx`. At each step the output dependency is "curried": after
the prover sends `t`, the remaining output depends on `fun trRest => Output ⟨t, trRest⟩`.
For a non-dependent output, use `Prover m ctx (fun _ => A)`. -/
def Prover (m : Type → Type) : (ctx : ProtocolCtx) → (Transcript ctx → Type) → Type
  | .nil, Output => Output ⟨⟩
  | .P_to_V T _ rest, Output =>
      (t : T) × m (Prover m (rest t) (fun trRest => Output ⟨t, trRest⟩))
  | .V_to_P T rest, Output =>
      (t : T) → m (Prover m (rest t) (fun trRest => Output ⟨t, trRest⟩))

/-! ## Challenger -/

/-- Interactive challenger, dual of the prover. At `P_to_V` rounds the challenger
observes the prover's message (pure). At `V_to_P` rounds the challenger monadically
produces a challenge. -/
def Challenger (m : Type → Type) : ProtocolCtx → Type
  | .nil => PUnit
  | .P_to_V T _ rest => (t : T) → Challenger m (rest t)
  | .V_to_P T rest => m ((t : T) × Challenger m (rest t))

/-! ## Verifier -/

/-- A verifier receives a statement and the full dependent transcript, and decides
whether to accept (with a transcript-dependent output) or reject (`none`).
For a non-dependent output, use `Verifier m StmtIn ctx (fun _ => StmtOut)`. -/
def Verifier (m : Type → Type) (StmtIn : Type) (ctx : ProtocolCtx)
    (StmtOut : Transcript ctx → Type) :=
  StmtIn → (tr : Transcript ctx) → OptionT m (StmtOut tr)

/-! ## Smart constructors -/

/-- Non-dependent prover message round: the rest of the protocol does not depend on
the message value. -/
abbrev msg (T : Type) [oi : OracleInterface T] (rest : ProtocolCtx) : ProtocolCtx :=
  .P_to_V T oi (fun _ => rest)

/-- Non-dependent verifier challenge round: the rest of the protocol does not depend on
the challenge value. -/
abbrev chal (T : Type) (rest : ProtocolCtx) : ProtocolCtx :=
  .V_to_P T (fun _ => rest)

/-! ## Embedding from `ProtocolSpec` -/

/-- Embed a non-dependent `ProtocolSpec` (= `List Round`) as a degenerate `ProtocolCtx`
where all `rest` functions are constant. -/
def ofList : ProtocolSpec → ProtocolCtx
  | [] => .nil
  | (.P_to_V T oi) :: tl => .P_to_V T oi (fun _ => ofList tl)
  | (.V_to_P T) :: tl => .V_to_P T (fun _ => ofList tl)

/-! ## Prover.run -/

namespace Prover

/-- Execute a prover against an interactive challenger. Returns a dependent pair
of the transcript and the output whose type depends on it. -/
def run {m : Type → Type} [Monad m] :
    (ctx : ProtocolCtx) → {Output : Transcript ctx → Type} →
    Prover m ctx Output → Challenger m ctx →
    m ((tr : Transcript ctx) × Output tr)
  | .nil, _, output, _ => pure ⟨⟨⟩, output⟩
  | .P_to_V _ _ rest, _, ⟨msg, cont⟩, chal => do
      let next ← cont
      let ⟨tr, out⟩ ← run (rest msg) next (chal msg)
      return ⟨⟨msg, tr⟩, out⟩
  | .V_to_P _ rest, _, recv, chal => do
      let ⟨challenge, chalRest⟩ ← chal
      let next ← recv challenge
      let ⟨tr, out⟩ ← run (rest challenge) next chalRest
      return ⟨⟨challenge, tr⟩, out⟩

/-! ## mapOutput -/

/-- Map the output of a prover. The mapping function is dependent: it receives
the transcript and transforms the output at that transcript. -/
def mapOutput {m : Type → Type} [Functor m] :
    {ctx : ProtocolCtx} → {A B : Transcript ctx → Type} →
    (∀ tr, A tr → B tr) → Prover m ctx A → Prover m ctx B
  | .nil, _, _, f, a => f ⟨⟩ a
  | .P_to_V _ _ _, _, _, f, ⟨msg, cont⟩ =>
      ⟨msg, (mapOutput (fun trRest => f ⟨msg, trRest⟩) ·) <$> cont⟩
  | .V_to_P _ _, _, _, f, recv =>
      fun ch => (mapOutput (fun trRest => f ⟨ch, trRest⟩) ·) <$> recv ch

end Prover

/-! ## Dependent append -/

/-- Dependent concatenation: the second protocol can depend on the full transcript
of the first. When `ctx₂` is constant, this reduces to non-dependent append. -/
def append (ctx₁ : ProtocolCtx) (ctx₂ : Transcript ctx₁ → ProtocolCtx) :
    ProtocolCtx :=
  match ctx₁ with
  | .nil => ctx₂ ⟨⟩
  | .P_to_V T oi rest =>
      .P_to_V T oi (fun t => (rest t).append (fun trRest => ctx₂ ⟨t, trRest⟩))
  | .V_to_P T rest =>
      .V_to_P T (fun t => (rest t).append (fun trRest => ctx₂ ⟨t, trRest⟩))

/-- Join a transcript of the first context with a transcript of the second
(dependent on the first) into a transcript of the appended context.
Defined early so that `Prover.comp` and `splitPrefix` can reference it. -/
def Transcript.join :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    (tr₁ : Transcript ctx₁) → Transcript (ctx₂ tr₁) →
    Transcript (ctx₁.append ctx₂)
  | .nil, _, _, tr₂ => tr₂
  | .P_to_V _ _ rest, ctx₂, ⟨t, tr₁⟩, tr₂ =>
      ⟨t, join (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr₁ tr₂⟩
  | .V_to_P _ rest, ctx₂, ⟨t, tr₁⟩, tr₂ =>
      ⟨t, join (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr₁ tr₂⟩

/-- Build an `n`-stage telescope by iterating a public stage-state transition. The
current stage index and public state choose the next local protocol context, while the
transition computes the next public state from the realized stage transcript. -/
def chain {Stage : Nat → Type}
    (Ctx : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Ctx i stage) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → ProtocolCtx
  | 0, _, _ => .nil
  | n + 1, i, stage =>
      (Ctx i stage).append (fun tr => chain Ctx advance n (i + 1) (advance i stage tr))

/-! ## Prover.comp -/

namespace Prover

/-- Sequential composition of two provers over a dependent append. Both the
intermediate and final output types are transcript-dependent. The continuation
constructs the second prover from the first transcript and intermediate output;
the final output threads through `Transcript.join`. -/
def comp {m : Type → Type} [Monad m] :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {Mid : Transcript ctx₁ → Type} →
    {Output : Transcript (ctx₁.append ctx₂) → Type} →
    Prover m ctx₁ Mid →
    ((tr₁ : Transcript ctx₁) → Mid tr₁ →
      m (Prover m (ctx₂ tr₁)
        (fun tr₂ => Output (Transcript.join ctx₁ ctx₂ tr₁ tr₂)))) →
    m (Prover m (ctx₁.append ctx₂) Output)
  | .nil, _, _, _, output, f => f ⟨⟩ output
  | .P_to_V _ _ rest, ctx₂, _, _, ⟨msg, cont⟩, f =>
      pure ⟨msg, do
        let next ← cont
        comp (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩) next
          (fun trRest mid => f ⟨msg, trRest⟩ mid)⟩
  | .V_to_P _ rest, ctx₂, _, _, recv, f =>
      pure fun ch => do
        let next ← recv ch
        comp (rest ch) (fun trRest => ctx₂ ⟨ch, trRest⟩) next
          (fun trRest mid => f ⟨ch, trRest⟩ mid)

/-- Iterate a prover family over an indexed stage chain while returning a constant
output type `S`. Intermediate stage outputs are discarded; only the terminal `done`
value is returned after all stages finish. This is useful for honest-prover code
whose recursive structure is controlled entirely by the public transcript. -/
def compFromConst {m : Type → Type} [Monad m] {Stage : Nat → Type} {S : Type}
    (Ctx : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Ctx i stage) → Stage (i + 1))
    (step : (i : Nat) → (stage : Stage i) → Prover m (Ctx i stage) (fun _ => S))
    (done : (i : Nat) → (stage : Stage i) → S) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    m (Prover m (ProtocolCtx.chain Ctx advance n i stage) (fun _ => S))
  | 0, i, stage => pure (done i stage)
  | n + 1, i, stage =>
      comp (Ctx i stage)
        (fun tr₁ => ProtocolCtx.chain Ctx advance n (i + 1) (advance i stage tr₁))
        (step i stage)
        (fun tr₁ _ => compFromConst Ctx advance step done n (i + 1) (advance i stage tr₁))

/-- Extract the first-stage prover from a composed prover. The output of the first
stage is itself a prover for the second stage — the dependent output absorbs the
path-dependence naturally, with no sigma type needed. -/
def splitPrefix {m : Type → Type} [Functor m] :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {Output : Transcript (ctx₁.append ctx₂) → Type} →
    Prover m (ctx₁.append ctx₂) Output →
    Prover m ctx₁ (fun tr₁ =>
      Prover m (ctx₂ tr₁) (fun tr₂ => Output (Transcript.join ctx₁ ctx₂ tr₁ tr₂)))
  | .nil, _, _, p => p
  | .P_to_V _ _ rest, ctx₂, _, ⟨msg, cont⟩ =>
      ⟨msg, (splitPrefix (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩) ·) <$> cont⟩
  | .V_to_P _ rest, ctx₂, _, recv =>
      fun ch => (splitPrefix (rest ch) (fun trRest => ctx₂ ⟨ch, trRest⟩) ·) <$> recv ch

end Prover

/-! ## Partial transcript -/

/-- Auxiliary definition for `PartialTranscript`. `Nat` is the first match argument
so that `PartialTranscript ctx 0 = PUnit` reduces definitionally for arbitrary `ctx`. -/
def PartialTranscript.aux : Nat → ProtocolCtx → Type
  | 0, _ => PUnit
  | _ + 1, .nil => PUnit
  | n + 1, .P_to_V T _ rest => (t : T) × PartialTranscript.aux n (rest t)
  | n + 1, .V_to_P T rest => (t : T) × PartialTranscript.aux n (rest t)

/-- A partial transcript of a telescopic protocol: the first `n` exchanged values.
Because the protocol is dependent, the types of later entries depend on the values
of earlier ones — the partial transcript carries these values. -/
abbrev PartialTranscript (ctx : ProtocolCtx) (n : Nat) : Type :=
  PartialTranscript.aux n ctx

/-- The protocol context remaining after `n` steps along a partial transcript. -/
def PartialTranscript.remaining : (n : Nat) → (ctx : ProtocolCtx) →
    PartialTranscript ctx n → ProtocolCtx
  | 0, ctx, _ => ctx
  | _ + 1, .nil, _ => .nil
  | n + 1, .P_to_V _ _ rest, ⟨t, ptr⟩ => remaining n (rest t) ptr
  | n + 1, .V_to_P _ rest, ⟨t, ptr⟩ => remaining n (rest t) ptr

/-- Truncate a full transcript to its first `n` entries. -/
def Transcript.truncate : (n : Nat) → (ctx : ProtocolCtx) →
    Transcript ctx → PartialTranscript ctx n
  | 0, _, _ => ⟨⟩
  | _ + 1, .nil, _ => ⟨⟩
  | n + 1, .P_to_V _ _ rest, ⟨t, tr⟩ => ⟨t, truncate n (rest t) tr⟩
  | n + 1, .V_to_P _ rest, ⟨t, tr⟩ => ⟨t, truncate n (rest t) tr⟩

/-- The type of the next value to be exchanged, given the remaining context. -/
def headType : ProtocolCtx → Type
  | .nil => PEmpty
  | .P_to_V T _ _ => T
  | .V_to_P T _ => T

/-- Extend a partial transcript by one entry whose type is determined by the
remaining context. -/
def PartialTranscript.concat : (n : Nat) → (ctx : ProtocolCtx) →
    (ptr : PartialTranscript ctx n) →
    headType (PartialTranscript.remaining n ctx ptr) →
    PartialTranscript ctx (n + 1)
  | 0, .nil, _, v => PEmpty.elim v
  | 0, .P_to_V _ _ _, _, v => ⟨v, ⟨⟩⟩
  | 0, .V_to_P _ _, _, v => ⟨v, ⟨⟩⟩
  | _ + 1, .nil, _, v => PEmpty.elim v
  | n + 1, .P_to_V _ _ rest, ⟨t, ptr⟩, v => ⟨t, concat n (rest t) ptr v⟩
  | n + 1, .V_to_P _ rest, ⟨t, ptr⟩, v => ⟨t, concat n (rest t) ptr v⟩

/-- The suffix of a full transcript starting after the first `n` entries. -/
def Transcript.suffix : (n : Nat) → (ctx : ProtocolCtx) →
    (tr : Transcript ctx) →
    Transcript (PartialTranscript.remaining n ctx (Transcript.truncate n ctx tr))
  | 0, _, tr => tr
  | _ + 1, .nil, tr => tr
  | n + 1, .P_to_V _ _ rest, ⟨_, tr⟩ => suffix n (rest _) tr
  | n + 1, .V_to_P _ rest, ⟨_, tr⟩ => suffix n (rest _) tr

/-- Bridge lemma: truncating at `n + 1` equals concatenating the `n`-truncation
with the `(n+1)`-th entry. Proof deferred (requires dependent transport). -/
theorem Transcript.truncate_succ {T : Type} {oi : OracleInterface T}
    {rest : T → ProtocolCtx} (n : Nat) (t : T) (tr : Transcript (rest t)) :
    truncate (n + 1) (.P_to_V T oi rest) ⟨t, tr⟩ =
      ⟨t, truncate n (rest t) tr⟩ := rfl

theorem Transcript.truncate_succ' {T : Type}
    {rest : T → ProtocolCtx} (n : Nat) (t : T) (tr : Transcript (rest t)) :
    truncate (n + 1) (.V_to_P T rest) ⟨t, tr⟩ =
      ⟨t, truncate n (rest t) tr⟩ := rfl

/-! ## Helpers on ProtocolCtx -/

/-- Whether the head of a protocol context is a prover message round. -/
def isMessage : ProtocolCtx → Bool
  | .P_to_V _ _ _ => true
  | _ => false

/-- Whether the head of a protocol context is a verifier challenge round. -/
def isChallenge : ProtocolCtx → Bool
  | .V_to_P _ _ => true
  | _ => false

/-! ## Random challenger -/

/-- A random challenger that samples challenges from a provided sampler.
The `sample` function provides a `ProbComp T` for each challenge type `T`.
In practice, instantiate with `fun T => $ᵗ T` when `SampleableType` instances
are available. This replaces pre-sampled `Challenges`, which is impossible for
dependent protocols where challenge types depend on earlier values. -/
noncomputable def randomChallenger (sample : (T : Type) → ProbComp T) :
    (ctx : ProtocolCtx) → Challenger ProbComp ctx
  | .nil => ⟨⟩
  | .P_to_V _ _ rest => fun t => randomChallenger sample (rest t)
  | .V_to_P T rest => do
      let t ← sample T
      return ⟨t, randomChallenger sample (rest t)⟩

/-! ## Claim tree -/

open scoped NNReal ENNReal

/-- A recursive soundness witness whose local claim type can change with the transcript.
At prover-message nodes and verifier-challenge nodes, `advance` maps the current claim
into the root claim of the selected child subtree. -/
inductive ClaimTree : (ctx : ProtocolCtx) → (Claim : Type) → Type 1 where
  | nil
      {Claim : Type}
      (good : Claim → Prop) :
      ClaimTree .nil Claim
  | message
      {Claim : Type}
      {T : Type} {oi : OracleInterface T} {rest : T → ProtocolCtx}
      (good : Claim → Prop)
      (NextClaim : (msg : T) → Type)
      (next : (msg : T) → ClaimTree (rest msg) (NextClaim msg))
      (advance : (claim : Claim) → (msg : T) → NextClaim msg) :
      ClaimTree (.P_to_V T oi rest) Claim
  | challenge
      {Claim : Type}
      {T : Type} {rest : T → ProtocolCtx}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : (challenge : T) → Type)
      (next : (challenge : T) → ClaimTree (rest challenge) (NextClaim challenge))
      (advance : (claim : Claim) → (challenge : T) → NextClaim challenge) :
      ClaimTree (.V_to_P T rest) Claim

namespace ClaimTree

/-- The "good" predicate at the root claim of a claim tree. -/
def good {ctx : ProtocolCtx} {Claim : Type} : ClaimTree ctx Claim → Claim → Prop
  | .nil good => good
  | .message good _ _ _ => good
  | .challenge good _ _ _ _ => good

/-- The claim type reached at the end of a full transcript. -/
def Terminal : {ctx : ProtocolCtx} → {Claim : Type} →
    ClaimTree ctx Claim → Transcript ctx → Type
  | _, Claim, tree, tr => by
      cases tree with
      | nil =>
          exact Claim
      | @message _ T oi rest _ NextClaim next _ =>
          rcases tr with ⟨msg, trRest⟩
          exact Terminal (Claim := NextClaim msg) (next msg) trRest
      | @challenge _ T rest _ _ NextClaim next _ =>
          rcases tr with ⟨challenge, trRest⟩
          exact Terminal (Claim := NextClaim challenge) (next challenge) trRest

/-- Transport a root claim along a full transcript to the terminal claim. -/
def follow : {ctx : ProtocolCtx} → {Claim : Type} → (tree : ClaimTree ctx Claim) →
    (tr : Transcript ctx) → Claim → tree.Terminal tr
  | _, _, tree, tr, claim => by
      cases tree with
      | nil =>
          exact claim
      | @message _ T oi rest _ NextClaim next advance =>
          rcases tr with ⟨msg, trRest⟩
          exact follow (Claim := NextClaim msg) (next msg) trRest (advance claim msg)
      | @challenge _ T rest _ _ NextClaim next advance =>
          rcases tr with ⟨challenge, trRest⟩
          exact follow (Claim := NextClaim challenge) (next challenge) trRest
            (advance claim challenge)

/-- The "good" predicate at the terminal claim reached by a full transcript. -/
def terminalGood {ctx : ProtocolCtx} {Claim : Type} :
    (tree : ClaimTree ctx Claim) → (tr : Transcript ctx) → tree.Terminal tr → Prop
  | tree, tr => by
      cases tree with
      | nil good =>
          intro claim
          exact good claim
      | @message _ T oi rest _ NextClaim next _ =>
          rcases tr with ⟨msg, trRest⟩
          exact terminalGood (Claim := NextClaim msg) (next msg) trRest
      | @challenge _ T rest _ _ NextClaim next _ =>
          rcases tr with ⟨challenge, trRest⟩
          exact terminalGood (Claim := NextClaim challenge) (next challenge) trRest

/-- The worst-case sum of challenge-node error bounds over a root-to-leaf path. -/
noncomputable def maxPathError : {ctx : ProtocolCtx} → {Claim : Type} →
    ClaimTree ctx Claim → ℝ≥0∞
  | _, _, tree =>
      match tree with
      | .nil _ => 0
      | .message _ _ next _ => ⨆ msg, maxPathError (next msg)
      | .challenge _ error _ next _ => error + ⨆ challenge, maxPathError (next challenge)

/-- Structural soundness of a claim tree. Message steps must preserve badness, and
challenge steps may flip badness to goodness with probability at most `error`. -/
noncomputable def IsSound
    (sample : (T : Type) → ProbComp T) :
    {ctx : ProtocolCtx} → {Claim : Type} → ClaimTree ctx Claim → Prop
  | _, _, tree =>
      match tree with
      | .nil _ => True
      | .message good _ next advance =>
          (∀ claim, ¬ good claim → ∀ msg, ¬ (next msg).good (advance claim msg)) ∧
          (∀ msg, IsSound sample (next msg))
      | .challenge good error _ next advance =>
          (∀ claim, ¬ good claim →
            Pr[(fun challenge =>
              (next challenge).good (advance claim challenge)) | sample _] ≤ error) ∧
          (∀ challenge, IsSound sample (next challenge))

/-- Precompose the root claim of a claim tree with a typed boundary map. The child
subtrees are unchanged; only the current root claim type is replaced. -/
def pullback {ctx : ProtocolCtx} {Claim : Type} (tree : ClaimTree ctx Claim) :
    (Root : Type) → (Root → Claim) → ClaimTree ctx Root := by
  cases tree with
  | nil good =>
      intro Root lift
      exact .nil (fun root => good (lift root))
  | message good NextClaim next advance =>
      intro Root lift
      exact .message (fun root => good (lift root)) NextClaim next
        (fun root msg => advance (lift root) msg)
  | challenge good error NextClaim next advance =>
      intro Root lift
      exact .challenge (fun root => good (lift root)) error NextClaim next
        (fun root challenge => advance (lift root) challenge)

@[simp] theorem maxPathError_pullback {ctx : ProtocolCtx} {Claim : Type}
    (tree : ClaimTree ctx Claim) {Root : Type} (lift : Root → Claim) :
    (tree.pullback Root lift).maxPathError = tree.maxPathError := by
  cases tree <;> rfl

@[simp] theorem good_pullback {ctx : ProtocolCtx} {Claim : Type}
    (tree : ClaimTree ctx Claim) {Root : Type} (lift : Root → Claim) (root : Root) :
    (tree.pullback Root lift).good root ↔ tree.good (lift root) := by
  cases tree <;> rfl

theorem pullback_isSound {ctx : ProtocolCtx} {Claim : Type}
    (tree : ClaimTree ctx Claim) (sample : (T : Type) → ProbComp T)
    (hTree : tree.IsSound sample) {Root : Type} (lift : Root → Claim) :
    (tree.pullback Root lift).IsSound sample := by
  cases tree with
  | nil good =>
      trivial
  | message good NextClaim next advance =>
      rcases hTree with ⟨hStep, hChildren⟩
      refine ⟨?_, ?_⟩
      · intro root hBad msg
        exact hStep (lift root) hBad msg
      · intro msg
        exact hChildren msg
  | challenge good error NextClaim next advance =>
      rcases hTree with ⟨hStep, hChildren⟩
      refine ⟨?_, ?_⟩
      · intro root hBad
        exact hStep (lift root) hBad
      · intro challenge
        exact hChildren challenge

/-- Sequential composition of claim trees over a dependent append. The typed `lift`
map converts the terminal claim of the first stage into the root claim of the second. -/
def comp :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {Claim₁ : Type} → {Claim₂ : (tr₁ : Transcript ctx₁) → Type} →
    (tree₁ : ClaimTree ctx₁ Claim₁) →
    (tree₂ : (tr₁ : Transcript ctx₁) → ClaimTree (ctx₂ tr₁) (Claim₂ tr₁)) →
    ((tr₁ : Transcript ctx₁) → tree₁.Terminal tr₁ → Claim₂ tr₁) →
    ClaimTree (ctx₁.append ctx₂) Claim₁
  | .nil, _, _, _, .nil _, tree₂, lift =>
      (tree₂ PUnit.unit).pullback _ (fun claim => lift PUnit.unit claim)
  | .P_to_V _ _ rest, ctx₂, _, _, .message good NextClaim next advance, tree₂, lift =>
      .message good NextClaim
        (fun msg =>
          comp (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩) (next msg)
            (fun trRest => tree₂ ⟨msg, trRest⟩)
            (fun trRest => lift ⟨msg, trRest⟩))
        advance
  | .V_to_P _ rest, ctx₂, _, _, .challenge good error NextClaim next advance, tree₂, lift =>
      .challenge good error NextClaim
        (fun challenge =>
          comp (rest challenge) (fun trRest => ctx₂ ⟨challenge, trRest⟩)
            (next challenge) (fun trRest => tree₂ ⟨challenge, trRest⟩)
            (fun trRest => lift ⟨challenge, trRest⟩))
        advance

theorem comp_not_good_of_not_good :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {Claim₁ : Type} → {Claim₂ : (tr₁ : Transcript ctx₁) → Type} →
    (tree₁ : ClaimTree ctx₁ Claim₁) →
    (tree₂ : (tr₁ : Transcript ctx₁) → ClaimTree (ctx₂ tr₁) (Claim₂ tr₁)) →
    (lift : (tr₁ : Transcript ctx₁) → tree₁.Terminal tr₁ → Claim₂ tr₁) →
    (∀ tr₁ terminalClaim,
      ¬ tree₁.terminalGood tr₁ terminalClaim →
      ¬ (tree₂ tr₁).good (lift tr₁ terminalClaim)) →
    ∀ claim, ¬ tree₁.good claim → ¬ (ClaimTree.comp ctx₁ ctx₂ tree₁ tree₂ lift).good claim
  | .nil, _, _, _, .nil _, tree₂, lift, hLift, claim, hBad => by
      intro hGood
      change
        ((tree₂ PUnit.unit).pullback _ (fun terminalClaim => lift PUnit.unit terminalClaim)).good
          claim at hGood
      have hGood' : (tree₂ PUnit.unit).good (lift PUnit.unit claim) := by
        simpa using hGood
      exact hLift PUnit.unit claim hBad hGood'
  | .P_to_V _ _ _, _, _, _, .message _ _ _ _, _, _, _, _, hBad => hBad
  | .V_to_P _ _, _, _, _, .challenge _ _ _ _ _, _, _, _, _, hBad => hBad

/-- The max-path error of a composed claim tree is bounded by the first-stage error
plus the worst second-stage error over all first-stage transcripts. -/
theorem maxPathError_comp :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {Claim₁ : Type} → {Claim₂ : (tr₁ : Transcript ctx₁) → Type} →
    (tree₁ : ClaimTree ctx₁ Claim₁) →
    (tree₂ : (tr₁ : Transcript ctx₁) → ClaimTree (ctx₂ tr₁) (Claim₂ tr₁)) →
    (lift : (tr₁ : Transcript ctx₁) → tree₁.Terminal tr₁ → Claim₂ tr₁) →
    maxPathError (ClaimTree.comp ctx₁ ctx₂ tree₁ tree₂ lift) ≤
      maxPathError tree₁ + ⨆ tr₁, maxPathError (tree₂ tr₁)
  | .nil, ctx₂, _, _, .nil good, tree₂, lift => by
      calc
        maxPathError (ClaimTree.comp .nil ctx₂ (.nil good) tree₂ lift)
            = maxPathError (tree₂ PUnit.unit) := by
              simp [ClaimTree.comp]
        _ ≤ 0 + ⨆ tr₁, maxPathError (tree₂ tr₁) := by
              simpa using add_le_add_left
                (le_iSup (f := fun tr₁ => ClaimTree.maxPathError (tree₂ tr₁)) PUnit.unit) 0
  | .P_to_V T oi rest, ctx₂, Claim₁, Claim₂,
      .message good NextClaim next advance, tree₂, lift => by
      simp only [ClaimTree.comp, ClaimTree.maxPathError]
      apply iSup_le
      intro msg
      calc
        maxPathError
            (ClaimTree.comp (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩)
              (next msg) (fun trRest => tree₂ ⟨msg, trRest⟩)
              (fun trRest => lift ⟨msg, trRest⟩))
          ≤ maxPathError (next msg) +
              ⨆ trRest, maxPathError (tree₂ ⟨msg, trRest⟩) :=
            maxPathError_comp (rest msg) _ (next msg) _ _
        _ ≤ (⨆ msg', maxPathError (next msg')) + ⨆ tr₁, maxPathError (tree₂ tr₁) := by
            gcongr
            · exact le_iSup (f := fun msg' => maxPathError (next msg')) msg
            · apply iSup_le
              intro trRest
              exact le_iSup (f := fun tr₁ => maxPathError (tree₂ tr₁)) ⟨msg, trRest⟩
  | .V_to_P T rest, ctx₂, Claim₁, Claim₂,
      .challenge good error NextClaim next advance, tree₂, lift => by
      simp only [ClaimTree.comp, ClaimTree.maxPathError]
      rw [add_assoc]
      gcongr
      apply iSup_le
      intro challenge
      calc
        maxPathError
            (ClaimTree.comp (rest challenge) (fun trRest => ctx₂ ⟨challenge, trRest⟩)
              (next challenge) (fun trRest => tree₂ ⟨challenge, trRest⟩)
              (fun trRest => lift ⟨challenge, trRest⟩))
          ≤ maxPathError (next challenge) +
              ⨆ trRest, maxPathError (tree₂ ⟨challenge, trRest⟩) :=
            maxPathError_comp (rest challenge) _ (next challenge) _ _
        _ ≤ (⨆ challenge', maxPathError (next challenge')) + ⨆ tr₁, maxPathError (tree₂ tr₁) := by
            gcongr
            · exact le_iSup (f := fun challenge' => maxPathError (next challenge')) challenge
            · apply iSup_le
              intro trRest
              exact le_iSup (f := fun tr₁ => maxPathError (tree₂ tr₁)) ⟨challenge, trRest⟩

end ClaimTree

/-! ## Transcript.split -/

/-- Split a transcript of an appended context into the transcript of the first
context and the transcript of the second (which depends on the first). -/
def Transcript.split :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    Transcript (ctx₁.append ctx₂) → (tr₁ : Transcript ctx₁) × Transcript (ctx₂ tr₁)
  | .nil, _, tr => ⟨⟨⟩, tr⟩
  | .P_to_V _ _ rest, ctx₂, ⟨t, tr⟩ =>
      let ⟨tr₁, tr₂⟩ := split (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr
      ⟨⟨t, tr₁⟩, tr₂⟩
  | .V_to_P _ rest, ctx₂, ⟨t, tr⟩ =>
      let ⟨tr₁, tr₂⟩ := split (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr
      ⟨⟨t, tr₁⟩, tr₂⟩

@[simp]
theorem Transcript.split_join :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    (tr₁ : Transcript ctx₁) → (tr₂ : Transcript (ctx₂ tr₁)) →
    split ctx₁ ctx₂ (join ctx₁ ctx₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩
  | .nil, _, _, _ => rfl
  | .P_to_V _ _ rest, ctx₂, ⟨t, tr₁⟩, tr₂ => by
      simp only [split, join]; rw [split_join]
  | .V_to_P _ rest, ctx₂, ⟨t, tr₁⟩, tr₂ => by
      simp only [split, join]; rw [split_join]

/-! ## Verifier.comp -/

/-- Compose two verifiers over a dependent append. Defined by structural recursion
on `ctx₁` to maintain definitional equalities with dependent output types (avoiding
the need for transport via `Transcript.join_split`). The second verifier's output
threads through `Transcript.join`. -/
def Verifier.comp {m : Type → Type} [Monad m] {S₁ : Type} :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    {S₂ : Transcript ctx₁ → Type} →
    (S₃ : Transcript (ctx₁.append ctx₂) → Type) →
    Verifier m S₁ ctx₁ S₂ →
    ((tr₁ : Transcript ctx₁) → Verifier m (S₂ tr₁) (ctx₂ tr₁)
      (fun tr₂ => S₃ (Transcript.join ctx₁ ctx₂ tr₁ tr₂))) →
    Verifier m S₁ (ctx₁.append ctx₂) S₃
  | .nil, _, _, _, v₁, v₂ => fun stmt tr => do
      let mid ← v₁ stmt ⟨⟩
      v₂ ⟨⟩ mid tr
  | .P_to_V _ _ rest, ctx₂, _, S₃, v₁, v₂ => fun stmt ⟨t, trFull⟩ =>
      comp (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩)
        (fun trFull => S₃ ⟨t, trFull⟩)
        (fun stmt' trRest => v₁ stmt' ⟨t, trRest⟩)
        (fun trRest => v₂ ⟨t, trRest⟩) stmt trFull
  | .V_to_P _ rest, ctx₂, _, S₃, v₁, v₂ => fun stmt ⟨t, trFull⟩ =>
      comp (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩)
        (fun trFull => S₃ ⟨t, trFull⟩)
        (fun stmt' trRest => v₁ stmt' ⟨t, trRest⟩)
        (fun trRest => v₂ ⟨t, trRest⟩) stmt trFull

/-! ## Challenger.comp -/

/-- Compose two challengers over a dependent append. The second challenger depends
on the first transcript (accumulated during the first phase). At `P_to_V` rounds
the composed challenger observes the message and threads it through. At `V_to_P`
rounds it produces a challenge and continues composing. -/
def Challenger.comp {m : Type → Type} [Monad m] :
    (ctx₁ : ProtocolCtx) → (ctx₂ : Transcript ctx₁ → ProtocolCtx) →
    Challenger m ctx₁ → ((tr₁ : Transcript ctx₁) → Challenger m (ctx₂ tr₁)) →
    Challenger m (ctx₁.append ctx₂)
  | .nil, _, _, c₂ => c₂ ⟨⟩
  | .P_to_V _ _ rest, ctx₂, obsv, c₂ =>
      fun t => comp (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) (obsv t)
        (fun trRest => c₂ ⟨t, trRest⟩)
  | .V_to_P _ rest, ctx₂, chal, c₂ => do
      let ⟨t, chalRest⟩ ← chal
      return ⟨t, comp (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) chalRest
        (fun trRest => c₂ ⟨t, trRest⟩)⟩

/-! ## Replicate and compNth -/

/-- Recursive family obtained by iterating a type family along an indexed stage chain
for `n` stages. The next stage index/state is recovered by repeatedly splitting the
full transcript into its local stage pieces. -/
def chainFamily {Stage : Nat → Type}
    (Ctx : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Ctx i stage) → Stage (i + 1))
    (Family : (i : Nat) → Stage i → Type) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Transcript (ProtocolCtx.chain Ctx advance n i stage) → Type
  | 0, i, stage, _ => Family i stage
  | n + 1, i, stage, tr =>
      let parts :=
        Transcript.split (Ctx i stage)
          (fun tr₁ => ProtocolCtx.chain Ctx advance n (i + 1) (advance i stage tr₁)) tr
      chainFamily Ctx advance Family n (i + 1) (advance i stage parts.1) parts.2

namespace Verifier

/-- Iterate a verifier family whose local protocol, live statement type, and public
stage state may all vary by round. The next stage is selected using only the realized
stage transcript, preserving the same public/private split as `Reduction.comp`. -/
def compFrom {m : Type → Type} [Monad m] {Stage : Nat → Type}
    (Ctx : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Ctx i stage) → Stage (i + 1))
    (Stmt : (i : Nat) → Stage i → Type)
    (step : (i : Nat) → (stage : Stage i) →
      Verifier m (Stmt i stage) (Ctx i stage)
        (fun tr => Stmt (i + 1) (advance i stage tr))) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Verifier m (Stmt i stage) (ProtocolCtx.chain Ctx advance n i stage)
      (ProtocolCtx.chainFamily Ctx advance Stmt n i stage)
  | 0, _, _ => fun stmt _ => pure stmt
  | n + 1, i, stage => fun stmt tr => do
      let parts :=
        Transcript.split (Ctx i stage)
          (fun tr₁ => ProtocolCtx.chain Ctx advance n (i + 1) (advance i stage tr₁)) tr
      let stmt' ← step i stage stmt parts.1
      compFrom Ctx advance Stmt step n (i + 1) (advance i stage parts.1) stmt' parts.2

/-- Constant-statement specialization of `compFrom`. This is the stage-family analogue
of the old self-composition helper: contexts may still vary with the public stage
state, but each stage consumes and returns the same live statement type `S`. -/
def compFromConst {m : Type → Type} [Monad m] {Stage : Nat → Type} {S : Type}
    (Ctx : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Ctx i stage) → Stage (i + 1))
    (step : (i : Nat) → (stage : Stage i) → Verifier m S (Ctx i stage) (fun _ => S)) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Verifier m S (ProtocolCtx.chain Ctx advance n i stage) (fun _ => S)
  | 0, _, _ => fun stmt _ => pure stmt
  | n + 1, i, stage => fun stmt tr => do
      let parts :=
        Transcript.split (Ctx i stage)
          (fun tr₁ => ProtocolCtx.chain Ctx advance n (i + 1) (advance i stage tr₁)) tr
      let stmt' ← step i stage stmt parts.1
      compFromConst Ctx advance step n (i + 1) (advance i stage parts.1) stmt' parts.2

end Verifier

/-- Replicate a protocol context `n` times. Each copy is independent (non-dependent
concatenation). -/
def replicate (ctx : ProtocolCtx) : Nat → ProtocolCtx
  | n => chain
      (Stage := fun _ => PUnit)
      (fun _ _ => ctx)
      (fun _ _ _ => PUnit.unit)
      n 0 PUnit.unit

/-- Compose a verifier with itself `n` times over the replicated context.
Self-composition requires non-dependent output (`fun _ => S`). -/
def Verifier.compNth {m : Type → Type} [Monad m] {S : Type}
    {ctx : ProtocolCtx} : (n : Nat) →
    Verifier m S ctx (fun _ => S) → Verifier m S (ctx.replicate n) (fun _ => S)
  | n, v =>
      Verifier.compFromConst
        (Stage := fun _ => PUnit)
        (Ctx := fun _ _ => ctx)
        (advance := fun _ _ _ => PUnit.unit)
        (step := fun _ _ => v)
        n 0 PUnit.unit

/-! ## Telescopic monads (sketch)

In an IOP, after the prover commits a polynomial the verifier gains oracle access
to it — the oracle spec (and hence the monad `OracleComp oSpec`) changes between
rounds. A `ProtocolCtxM` variant bundles a per-round monad into the spec itself.
-/

/-- A monad bundled with its `Monad` instance, so it can be stored inside an
inductive type (where typeclass parameters are not allowed). -/
structure BundledMonad where
  M : Type → Type
  instMonad : Monad M

instance (bm : BundledMonad) : Monad bm.M := bm.instMonad

/-- Telescopic protocol specification with per-round monads. Each constructor
carries a `BundledMonad` that the prover/challenger uses for the continuation
after this round. -/
inductive ProtocolCtxM : Type 1 where
  | nil : ProtocolCtxM
  | P_to_V (T : Type) (oi : OracleInterface T)
      (contMonad : BundledMonad)
      (rest : T → ProtocolCtxM) : ProtocolCtxM
  | V_to_P (T : Type)
      (contMonad : BundledMonad)
      (rest : T → ProtocolCtxM) : ProtocolCtxM

namespace ProtocolCtxM

/-! ### Transcript -/

/-- Transcript for a telescopic protocol with per-round monads. Identical in
structure to `ProtocolCtx.Transcript` — the monad does not affect the transcript. -/
def Transcript : ProtocolCtxM → Type
  | .nil => PUnit
  | .P_to_V T _ _ rest => (t : T) × Transcript (rest t)
  | .V_to_P T _ rest => (t : T) × Transcript (rest t)

/-! ### Prover -/

/-- Prover for a telescopic protocol with per-round monads. Each round's continuation
uses the `BundledMonad` stored in that round's constructor. Output is
transcript-dependent. -/
def Prover : (ctx : ProtocolCtxM) → (Transcript ctx → Type) → Type
  | .nil, Output => Output ⟨⟩
  | .P_to_V T _ bm rest, Output =>
      (t : T) × bm.M (Prover (rest t) (fun trRest => Output ⟨t, trRest⟩))
  | .V_to_P T bm rest, Output =>
      (t : T) → bm.M (Prover (rest t) (fun trRest => Output ⟨t, trRest⟩))

/-! ### Challenger -/

/-- Interactive challenger for a telescopic protocol with per-round monads. At
`P_to_V` rounds the challenger observes the prover's message (pure). At `V_to_P`
rounds the challenger monadically produces a challenge using that round's monad. -/
def Challenger : ProtocolCtxM → Type
  | .nil => PUnit
  | .P_to_V T _ _ rest => (t : T) → Challenger (rest t)
  | .V_to_P T bm rest => bm.M ((t : T) × Challenger (rest t))

/-! ### Verifier -/

/-- A verifier receives a statement and the full dependent transcript. The verifier
uses a fixed base monad `m` (not the per-round monads). Output is
transcript-dependent. -/
def Verifier (m : Type → Type) (StmtIn : Type) (ctx : ProtocolCtxM)
    (StmtOut : Transcript ctx → Type) :=
  StmtIn → (tr : Transcript ctx) → OptionT m (StmtOut tr)

/-! ### Smart constructors -/

/-- Non-dependent prover message round with a fixed bundled monad. -/
abbrev msg (T : Type) [oi : OracleInterface T] (bm : BundledMonad) (rest : ProtocolCtxM) :
    ProtocolCtxM :=
  .P_to_V T oi bm (fun _ => rest)

/-- Non-dependent verifier challenge round with a fixed bundled monad. -/
abbrev chal (T : Type) (bm : BundledMonad) (rest : ProtocolCtxM) : ProtocolCtxM :=
  .V_to_P T bm (fun _ => rest)

/-! ### Embedding from `ProtocolCtx` -/

/-- Embed a `ProtocolCtx` into `ProtocolCtxM` by assigning a fixed `BundledMonad`
to every round. -/
def ofCtx (bm : BundledMonad) : ProtocolCtx → ProtocolCtxM
  | .nil => .nil
  | .P_to_V T oi rest => .P_to_V T oi bm (fun t => ofCtx bm (rest t))
  | .V_to_P T rest => .V_to_P T bm (fun t => ofCtx bm (rest t))

/-! ### Prover.run -/

namespace Prover

/-- Execute a prover against an interactive challenger. Since each round uses a
different monad, `lift` interprets each round's `BundledMonad` into the common
base monad `m`. Returns a dependent pair of transcript and output. -/
def run {m : Type → Type} [Monad m]
    (lift : ∀ (bm : BundledMonad) {α : Type}, bm.M α → m α) :
    (ctx : ProtocolCtxM) → {Output : Transcript ctx → Type} →
    Prover ctx Output → Challenger ctx →
    m ((tr : Transcript ctx) × Output tr)
  | .nil, _, output, _ => pure ⟨⟨⟩, output⟩
  | .P_to_V _ _ bm rest, _, ⟨msg, cont⟩, chal => do
      let next ← lift bm cont
      let ⟨tr, out⟩ ← run lift (rest msg) next (chal msg)
      return ⟨⟨msg, tr⟩, out⟩
  | .V_to_P _ bm rest, _, recv, chal => do
      let ⟨challenge, chalRest⟩ ← lift bm chal
      let next ← lift bm (recv challenge)
      let ⟨tr, out⟩ ← run lift (rest challenge) next chalRest
      return ⟨⟨challenge, tr⟩, out⟩

/-! ### mapOutput -/

/-- Map the output of a prover with a transcript-dependent function. -/
def mapOutput :
    {ctx : ProtocolCtxM} → {A B : Transcript ctx → Type} →
    (∀ tr, A tr → B tr) → Prover ctx A → Prover ctx B
  | .nil, _, _, f, a => f ⟨⟩ a
  | .P_to_V _ _ _ _, _, _, f, ⟨msg, cont⟩ =>
      ⟨msg, (mapOutput (fun trRest => f ⟨msg, trRest⟩) ·) <$> cont⟩
  | .V_to_P _ _ _, _, _, f, recv =>
      fun ch => (mapOutput (fun trRest => f ⟨ch, trRest⟩) ·) <$> recv ch

end Prover

/-! ### Dependent append -/

/-- Dependent concatenation for per-round-monad protocols. The per-round monads
from `ctx₁` are preserved; the second protocol provides its own. -/
def append (ctx₁ : ProtocolCtxM) (ctx₂ : Transcript ctx₁ → ProtocolCtxM) :
    ProtocolCtxM :=
  match ctx₁ with
  | .nil => ctx₂ ⟨⟩
  | .P_to_V T oi bm rest =>
      .P_to_V T oi bm (fun t => (rest t).append (fun trRest => ctx₂ ⟨t, trRest⟩))
  | .V_to_P T bm rest =>
      .V_to_P T bm (fun t => (rest t).append (fun trRest => ctx₂ ⟨t, trRest⟩))

/-- Join transcripts for appended per-round-monad protocols. -/
def Transcript.join :
    (ctx₁ : ProtocolCtxM) → (ctx₂ : Transcript ctx₁ → ProtocolCtxM) →
    (tr₁ : Transcript ctx₁) → Transcript (ctx₂ tr₁) →
    Transcript (ctx₁.append ctx₂)
  | .nil, _, _, tr₂ => tr₂
  | .P_to_V _ _ _ rest, ctx₂, ⟨t, tr₁⟩, tr₂ =>
      ⟨t, join (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr₁ tr₂⟩
  | .V_to_P _ _ rest, ctx₂, ⟨t, tr₁⟩, tr₂ =>
      ⟨t, join (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr₁ tr₂⟩

/-! ### Prover.comp -/

namespace Prover

/-- Sequential composition of two provers with dependent output. Unlike the
plain `ProtocolCtx` version, this is pure (no outer monad wrap) — each round's
continuation is mapped over using the `Functor` instance of that round's
bundled monad. -/
def comp :
    (ctx₁ : ProtocolCtxM) → (ctx₂ : Transcript ctx₁ → ProtocolCtxM) →
    {Mid : Transcript ctx₁ → Type} →
    {Output : Transcript (ctx₁.append ctx₂) → Type} →
    Prover ctx₁ Mid →
    ((tr₁ : Transcript ctx₁) → Mid tr₁ →
      Prover (ctx₂ tr₁) (fun tr₂ => Output (Transcript.join ctx₁ ctx₂ tr₁ tr₂))) →
    Prover (ctx₁.append ctx₂) Output
  | .nil, _, _, _, output, f => f ⟨⟩ output
  | .P_to_V _ _ _ rest, ctx₂, _, _, ⟨msg, cont⟩, f =>
      ⟨msg, (fun next => comp (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩) next
        (fun trRest mid => f ⟨msg, trRest⟩ mid)) <$> cont⟩
  | .V_to_P _ _ rest, ctx₂, _, _, recv, f =>
      fun ch => (fun next => comp (rest ch) (fun trRest => ctx₂ ⟨ch, trRest⟩) next
        (fun trRest mid => f ⟨ch, trRest⟩ mid)) <$> recv ch

/-- Extract the prefix prover from a composed prover. The first-stage output is the
remaining prover for the suffix protocol, with the transcript dependence carried in
the output type. -/
def splitPrefix :
    (ctx₁ : ProtocolCtxM) → (ctx₂ : Transcript ctx₁ → ProtocolCtxM) →
    {Output : Transcript (ctx₁.append ctx₂) → Type} →
    Prover (ctx₁.append ctx₂) Output →
    Prover ctx₁ (fun tr₁ =>
      Prover (ctx₂ tr₁) (fun tr₂ => Output (Transcript.join ctx₁ ctx₂ tr₁ tr₂)))
  | .nil, _, _, p => p
  | .P_to_V _ _ _ rest, ctx₂, _, ⟨msg, cont⟩ =>
      ⟨msg, (splitPrefix (rest msg) (fun trRest => ctx₂ ⟨msg, trRest⟩) ·) <$> cont⟩
  | .V_to_P _ _ rest, ctx₂, _, recv =>
      fun ch => (splitPrefix (rest ch) (fun trRest => ctx₂ ⟨ch, trRest⟩) ·) <$> recv ch

end Prover

/-! ### Transcript.split -/

/-- Split a transcript of an appended per-round-monad protocol into the transcript
of the prefix and the transcript of the dependent suffix. -/
def Transcript.split :
    (ctx₁ : ProtocolCtxM) → (ctx₂ : Transcript ctx₁ → ProtocolCtxM) →
    Transcript (ctx₁.append ctx₂) → (tr₁ : Transcript ctx₁) × Transcript (ctx₂ tr₁)
  | .nil, _, tr => ⟨⟨⟩, tr⟩
  | .P_to_V _ _ _ rest, ctx₂, ⟨t, tr⟩ =>
      let ⟨tr₁, tr₂⟩ := split (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr
      ⟨⟨t, tr₁⟩, tr₂⟩
  | .V_to_P _ _ rest, ctx₂, ⟨t, tr⟩ =>
      let ⟨tr₁, tr₂⟩ := split (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩) tr
      ⟨⟨t, tr₁⟩, tr₂⟩

/-! ### Verifier.comp -/

/-- Sequential composition of verifiers for per-round-monad protocols. The verifier
splits the combined transcript, feeds the first part to the first verifier, then
passes its output to the second verifier on the suffix transcript. -/
def Verifier.comp {m : Type → Type} [Monad m] {S₁ : Type} :
    (ctx₁ : ProtocolCtxM) → (ctx₂ : Transcript ctx₁ → ProtocolCtxM) →
    {S₂ : Transcript ctx₁ → Type} →
    (S₃ : Transcript (ctx₁.append ctx₂) → Type) →
    Verifier m S₁ ctx₁ S₂ →
    ((tr₁ : Transcript ctx₁) →
      Verifier m (S₂ tr₁) (ctx₂ tr₁)
        (fun tr₂ => S₃ (Transcript.join ctx₁ ctx₂ tr₁ tr₂))) →
    Verifier m S₁ (ctx₁.append ctx₂) S₃
  | .nil, _, _, _, v₁, v₂ => fun stmt tr => do
      let mid ← v₁ stmt ⟨⟩
      v₂ ⟨⟩ mid tr
  | .P_to_V _ _ _ rest, ctx₂, _, S₃, v₁, v₂ => fun stmt ⟨t, trFull⟩ =>
      comp (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩)
        (fun trFull => S₃ ⟨t, trFull⟩)
        (fun stmt' trRest => v₁ stmt' ⟨t, trRest⟩)
        (fun trRest => v₂ ⟨t, trRest⟩) stmt trFull
  | .V_to_P _ _ rest, ctx₂, _, S₃, v₁, v₂ => fun stmt ⟨t, trFull⟩ =>
      comp (rest t) (fun trRest => ctx₂ ⟨t, trRest⟩)
        (fun trFull => S₃ ⟨t, trFull⟩)
        (fun stmt' trRest => v₁ stmt' ⟨t, trRest⟩)
        (fun trRest => v₂ ⟨t, trRest⟩) stmt trFull

/-! ### Replicate and compNth -/

/-- Replicate a per-round-monad context `n` times by non-dependent append. -/
def replicate (ctx : ProtocolCtxM) : Nat → ProtocolCtxM
  | 0 => .nil
  | n + 1 => ctx.append (fun _ => replicate ctx n)

/-- Compose a verifier with itself `n` times over a replicated per-round-monad
context. The verifier output must be non-dependent so it can feed the next stage. -/
def Verifier.compNth {m : Type → Type} [Monad m] {S : Type}
    {ctx : ProtocolCtxM} : (n : Nat) →
    Verifier m S ctx (fun _ => S) →
    Verifier m S (ctx.replicate n) (fun _ => S)
  | 0, _ => fun stmt _ => pure stmt
  | n + 1, v =>
      Verifier.comp ctx (fun _ => replicate ctx n)
        (fun _ => S) v (fun _ => compNth n v)

end ProtocolCtxM

end ProtocolCtx
