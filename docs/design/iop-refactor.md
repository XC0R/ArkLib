# IOP Model Refactor: List-Based Protocol Specifications

**Status:** Design discussion (revised after council audit)  
**Branch:** `quang/iop-refactor`  
**Validation target:** Completeness & RBR knowledge soundness of Sumcheck

---

## Motivation

The current `ProtocolSpec n` (a `Fin n`-indexed pair of direction/type vectors) creates
pervasive friction:

1. **Casting overhead.** Composing two `ProtocolSpec n` and `ProtocolSpec m` produces
   `ProtocolSpec (n + m)`, requiring `Fin.castSucc`/`Fin.castAdd` everywhere.
2. **Rigid prover structure.** The stateful prover (`PrvState : Fin (n+1) → Type` +
   `sendMessage`/`receiveChallenge`) is unnatural to define and painful to compose.
3. **Oracle index accumulation.** The `embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx` + `hEq`
   mechanism for tracking output oracles through composition produces chains of
   `Function.Embedding.trans`/`Equiv.sumAssoc` that are hard to work with. The core
   `verify` in `OracleVerifier.append` is still `sorry`.
4. **Incomplete proofs.** Many composition and security lemmas have `sorry`s that stem
   from the indexing complexity, not from mathematical difficulty.

PR #146 (`list-based-pspec` branch) sketched the direction. This document fleshes out
the full design.

---

## 1. Protocol Specification

### Decision: `ProtocolSpec := List (Direction × Type)`

```lean
@[reducible]
def ProtocolSpec := List (Direction × Type)
```

**No length parameter.** Two protocol specs of different lengths are the same type.
Append is `List.append` — definitional, associative, with `[] ++ l = l` and
`l ++ [] = l` (the latter by a simp lemma).

### Accessors

```lean
namespace ProtocolSpec

def messageTypes : ProtocolSpec → List Type
  | [] => []
  | (.P_to_V, T) :: tl => T :: messageTypes tl
  | (.V_to_P, _) :: tl => messageTypes tl

def challengeTypes : ProtocolSpec → List Type
  | [] => []
  | (.P_to_V, _) :: tl => challengeTypes tl
  | (.V_to_P, T) :: tl => T :: challengeTypes tl

end ProtocolSpec
```

Both defined by structural recursion, so `messageTypes (p :: ps)` reduces
definitionally.

### Key lemmas needed

```
messageTypes_append : (p₁ ++ p₂).messageTypes = p₁.messageTypes ++ p₂.messageTypes
challengeTypes_append : (p₁ ++ p₂).challengeTypes = p₁.challengeTypes ++ p₂.challengeTypes
```

---

## 2. Transcripts

### Decision: Use `HVector` (heterogeneous vector) as the backbone

PR #146 proposed `List.TProd` (iterated `× PUnit`). After audit, we switch to
an inductive `HVector` (as in lean-mlir's `LeanMLIR.HVector`), which avoids the
trailing `PUnit` issue flagged by the council.

```lean
inductive HVector {α : Type*} (f : α → Type*) : List α → Type _
  | nil : HVector f []
  | cons {a : α} : (f a) → HVector f as → HVector f (a :: as)
```

For `pSpec = [(.P_to_V, Poly), (.V_to_P, R)]`:
- `Transcript pSpec = HVector Prod.snd pSpec` ≈ `Poly ::ₕ R ::ₕ .nil`
- No trailing `PUnit` — `nil` is its own constructor
- Pattern matching: `let .cons poly (.cons challenge .nil) := transcript`
- Notation: `[poly, challenge]ₕ`

**Key advantages over `TProd`:**
- Built-in `get : Fin → A` (no pair extraction)
- Built-in `append`, `map`, `mapM`, `foldl`, `ofFn`, `ext`
- `ToTupleType` conversion avoids `PUnit` for singletons: `HVector A [a] ≃ A a`
- `DecidableEq` instance derived

**Definitional behavior:**
- `append` is definitional: `(x ::ₕ xs) ++ ys = x ::ₕ (xs ++ ys)`
- Split via `head`/`tail` is definitional

**Challenges and Messages:**
```lean
def Challenges (pSpec : ProtocolSpec) := HVector id pSpec.challengeTypes
def Messages (pSpec : ProtocolSpec) := HVector id pSpec.messageTypes
```

**Source:** lean-mlir (`LeanMLIR/HVector.lean`) — to be adapted, not vendored
directly (drop the `Qq`/meta dependencies, keep core + `append` + `get` + `ofFn`).

### Open question: Partial transcripts

For round-by-round soundness, we need partial transcripts indexed by a round number.

**Option A: `takeChecked`** (what PR #146 uses)
```lean
def PartialTranscript (pSpec : ProtocolSpec) (n : Fin (pSpec.length + 1)) :=
  Transcript (pSpec.takeChecked n ...)
```
- `toFull` requires a cast: `takeChecked_length ▸ t`
- `concat` is clean: append a singleton

**Option B: Inductive prefix type**
```lean
inductive PartialTranscript : ProtocolSpec → Type
  | nil : PartialTranscript pSpec
  | cons : (pSpec.head).snd → PartialTranscript pSpec.tail → PartialTranscript pSpec
```
- No casts, but less connection to `Transcript`

**Option C: Avoid partial transcripts in the core API**
- The prover never needs partial transcripts (the `InteractOutputProver` produces
  the full transcript in one shot).
- The verifier never needs partial transcripts (public coin: sees full transcript).
- Only the **state function** for RBR soundness needs partial transcripts.
- Define partial transcripts only for the state function, using `takeChecked`.

**Current leaning: Option A** with good simp lemmas. Option C is tempting but the
state function is central enough that partial transcripts are unavoidable.

---

## 3. Prover

### Decision: Coinductive-style `InteractOutputProver`

```lean
def InteractOutputProver (m : Type → Type) (Output : Type)
    : ProtocolSpec → Type
  | [] => Output
  | (.P_to_V, MsgType) :: tl => MsgType × m (InteractOutputProver m Output tl)
  | (.V_to_P, ChalType) :: tl => ChalType → m (InteractOutputProver m Output tl)
```

An honest prover wraps this with input:
```lean
def Prover (m : Type → Type) (StmtIn WitIn StmtOut WitOut : Type)
    (pSpec : ProtocolSpec) :=
  StmtIn × WitIn → m (InteractOutputProver m (StmtOut × WitOut) pSpec)
```

### Why this is better

- **Sigma protocol prover** is just:
  ```lean
  fun (stmt, wit) => pure (computeMsg stmt wit,
    fun challenge => pure (computeResponse stmt wit challenge, (stmtOut, witOut)))
  ```
- **Sequential composition** is structural recursion on `pSpec₁`:
  ```lean
  def comp (p₁ : InteractOutputProver m Mid pSpec₁) (p₂ : Mid → m (InteractOutputProver m Out pSpec₂))
      : m (InteractOutputProver m Out (pSpec₁ ++ pSpec₂))
  ```
- **No state threading.** The monadic structure handles it.
- **No `Fin` casting.** Everything follows from list structure.

### Adversarial provers for security games

For soundness, we need adversarial provers that don't have a well-typed input.
Two options:

**Option A: Use `InteractOutputProver` with `Output = WitOut`**
- The adversary is `InteractOutputProver m WitOut pSpec` with some initial state baked in
- No input function needed

**Option B: Separate `AdversarialProver` type**
```lean
def AdversarialProver (m : Type → Type) (WitOut : Type) (pSpec : ProtocolSpec) :=
  InteractOutputProver m WitOut pSpec
```

**Current leaning: Option A.** The `InteractOutputProver` is general enough. The
soundness game just quantifies over all `InteractOutputProver m WitOut pSpec`.

### Stateful prover (optional, secondary)

For some analyses we may still want explicit state. Keep as a secondary definition
that can be converted to `InteractOutputProver`:
```lean
structure StatefulProver ... where
  PrvState : Fin (pSpec.length + 1) → Type
  ...
  toInteractOutputProver : InteractOutputProver m Output pSpec
```

---

## 4. Verifier

### Plain verifier (unchanged in spirit)

```lean
def Verifier (m : Type → Type) (StmtIn StmtOut : Type) (pSpec : ProtocolSpec) :=
  StmtIn → Transcript pSpec → OptionT m StmtOut
```

Composition:
```lean
def Verifier.comp (v₁ : Verifier m S₁ S₂ pSpec₁) (v₂ : Verifier m S₂ S₃ pSpec₂)
    : Verifier m S₁ S₃ (pSpec₁ ++ pSpec₂) :=
  fun stmt tr => do
    let mid ← v₁ stmt tr.fst
    v₂ mid tr.snd
```

---

## 5. Oracle Verifier — The Hard Problem

This is the most delicate part of the design. There are several intertwined questions:

### 5.1. How to represent oracle access

**Current model:** The oracle verifier's `verify` function has oracle access to
`oSpec + [OStmtIn]ₒ + [pSpec.Message]ₒ` — everything at once.

**Alternative: Round-by-round oracle accumulation.** Define the oracle verifier
coinductively, where oracle access grows as messages arrive. For public-coin
protocols this collapses to the end-of-protocol model (the verifier never acts
until the end), so it adds complexity without benefit for the common case.

**Decision:** Keep the deferred/end-of-protocol verification style for
public-coin protocols. The round-by-round style can be added later as a
generalization if needed for non-public-coin or Fiat-Shamir-specific constructions.

### 5.2. How to index oracles

**Current:** `ιₛᵢ : Type` with `OStmtIn : ιₛᵢ → Type` — arbitrary index type.
Composition produces `ιₛ₁ ⊕ pSpec₁.MessageIdx` for the middle step.

**Decision: Use `List Type` for oracle statements.**

**Critical constraint (from audit):** VCVio's `SubSpec`, `QueryImpl.add`, and all
simulation machinery is built on `Sum.inl`/`Sum.inr` — there are zero `SubSpec`
instances for `Fin`-indexed specs. Therefore:

**`oracleSpecOfList` must produce nested `Sum` types, NOT `Fin`-indexed specs.**

```lean
def oracleSpecOfList : List Type → (each with OracleInterface) → OracleSpec _
  | [] => []ₒ
  | T :: ts => specOfT + oracleSpecOfList ts
```

This gives:
- **Definitional** `oracleSpecOfList (l₁ ++ l₂) = oracleSpecOfList l₁ + oracleSpecOfList l₂`
- **Free** `SubSpec` instances via VCVio's `subSpec_add_left`/`subSpec_add_right`
- **Free** `QueryImpl.add`/`QueryImpl.addLift` for combined oracle implementations

The resulting index types are nested sums like `T₁ ⊕ (T₂ ⊕ (T₃ ⊕ PEmpty))` —
verbose but exactly what VCVio handles well.

**`OracleInterface` instance synthesis caveat:** Instance search through
`List.get ∘ messageTypes` fails for abstract protocol specs (the same problem
exists today with `Fin`-based indexing). Options: (a) manually restate instances
per protocol, or (b) bundle `OracleInterface` into protocol spec entries.
Defer to implementation to determine which is less painful.

### 5.3. How to specify output oracles

**Current:** `embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx` + `hEq` — the output oracle is
a subset of input oracles + messages, proven type-compatible.

**Decision (revised after audit): Use `QueryImpl`-based simulation directly.**

The initial proposal was `Sublist`, but audit revealed that `Sublist` alone is
insufficient — composition still needs query routing (a `QueryImpl`-like operation),
so `Sublist` would just add an intermediate step that always needs to be converted.
Use `QueryImpl` from the start:

Following PR #83's design, the oracle verifier has three components:

```lean
structure OracleVerifier (oSpec : OracleSpec ι)
    (StmtIn : Type) (OStmtIn : List Type) (StmtOut : Type) (OStmtOut : List Type)
    (pSpec : ProtocolSpec)
    [∀ i, OracleInterface (OStmtIn.get i)]
    [∀ i, OracleInterface (pSpec.messageTypes.get i)] where
  verify : StmtIn → Challenges pSpec →
    OptionT (OracleComp (oSpec + oracleSpecOfList OStmtIn + oracleSpecOfList pSpec.messageTypes))
      StmtOut
  simulate : QueryImpl (oracleSpecOfList OStmtOut)
               (OracleComp (oracleSpecOfList OStmtIn + oracleSpecOfList pSpec.messageTypes))
  reify : HVector id OStmtIn → Messages pSpec → OptionT m (HVector id OStmtOut)
  reify_simulate : ∀ ...,
    simulateQ simulate (query i q) = do
      let oStmtOut ← reify oStmtIn msgs
      pure ((oStmtOut.get i).answer q)
```

- **`simulate`**: How to answer output oracle queries using input oracles + messages
  (query-level, for security proofs)
- **`reify`**: How to compute the output oracle data from input oracle data + messages
  (data-level, for execution and completeness)
- **`reify_simulate`**: Proof that these two views are compatible

**Why `reify`?** All known IORs have computable output oracles (subset, linear
combination, evaluation). The `reify` field makes completeness proofs simpler
(just run the data pipeline) while `simulate` makes soundness proofs simpler
(work at the query level). PR #83 demonstrated this decomposition works well.

**Composition** is monadic: `V₂.simulate.comp (V₁.simulate.liftOracle ...)`.

For the common case where output oracles are just pass-throughs, provide a
constructor `QueryImpl.ofSublist` that builds the `QueryImpl` from a sublist
witness, and a trivial `reify` that extracts the corresponding elements.

### 5.4. Non-adaptive oracle verifier

Keep as a specialization (as currently done), but with list-based indexing:

```lean
structure OracleVerifier.NonAdaptive ... where
  queryOStmt : StmtIn → Challenges pSpec → List (Σ i, (OStmtIn.get i).Query)
  queryMsg : StmtIn → Challenges pSpec → List (Σ i, (pSpec.messageTypes.get i).Query)
  verify : StmtIn → Challenges pSpec → (query-response pairs) → ...
  outputOracles : ...
```

---

## 6. Oracle Reduction

```lean
structure OracleReduction (oSpec : OracleSpec ι)
    (StmtIn : Type) (OStmtIn : List Type) (WitIn : Type)
    (StmtOut : Type) (OStmtOut : List Type) (WitOut : Type)
    (pSpec : ProtocolSpec)
    [∀ i, OracleInterface (OStmtIn.get i)]
    [∀ i, OracleInterface (pSpec.messageTypes.get i)] where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec
```

Where `OracleProver` is just a `Prover` whose input includes oracle statement data.

### Specializations

```lean
-- IOP: output is Bool, no output oracles, trivial output witness
def OracleProof ... := OracleReduction ... Bool [] Unit ...

-- Interactive Proof: non-oracle version
def Proof ... := Reduction ... Bool Unit ...

-- Non-interactive: single P_to_V message
def NonInteractive (MsgType) ... := ... [(.P_to_V, MsgType)] ...
```

---

## 7. Security Definitions

### Completeness

Unchanged in structure. Uses `Reduction.run` which internally runs the prover
(via `InteractOutputProver.run`) and then the verifier.

### Soundness / Knowledge Soundness

Mostly unchanged, with these clarifications:

**Adversarial quantifier structure.** Soundness quantifies:
```lean
∀ (Output : Type), ∀ adversary : InteractOutputProver m Output pSpec, ∀ stmtIn ∉ langIn, ...
```
This is equivalent to the current `∀ WitIn WitOut : Type, ∀ witIn, ∀ prover`
because any prover adapted to `stmtIn` can bake its input into the
`InteractOutputProver` closure.

**Probability shape.** With outside challenge sampling, the `pImpl = impl.addLift
challengeQueryImpl` step disappears:
```lean
Pr[event | do
  let challenges ← sampleAllChallenges pSpec
  (simulateQ impl (adversary.run challenges)).run' (← init)] ≤ soundnessError
```

The extractor type becomes:
```lean
def Extractor.Straightline ... :=
  StmtIn → WitOut → Transcript pSpec → QueryLog oSpec → QueryLog oSpec →
    OptionT (OracleComp oSpec) WitIn
```

### Round-by-Round Soundness

State function:
```lean
structure StateFunction (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier m StmtIn StmtOut pSpec) where
  toFun : (k : Fin (pSpec.length + 1)) → StmtIn → PartialTranscript pSpec k → Prop
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt ()
  toFun_next : ...  -- same conditions, indexed by Fin
  toFun_full : ...
```

This still uses `Fin` indexing for the round number. The partial transcript at
round `k` is `PartialTranscript pSpec k = Transcript (pSpec.takeChecked k ...)`.

The `toFun_next` condition checks that a prover message cannot "fix" a bad state:
```lean
toFun_next : ∀ k, (pSpec.get k).fst = .P_to_V →
  ∀ stmt tr, ¬ toFun k.castSucc stmt tr →
    ∀ msg, ¬ toFun k.succ stmt (tr.concat msg)
```

Here `tr.concat msg` appends to the partial transcript — this is where
`takeChecked_succ` gives us definitional `takeChecked (k+1) = takeChecked k ++ [_]`,
making `concat` just `HVector.concat`.

---

## 8. Execution Semantics

### Prover execution (full)

```lean
def InteractOutputProver.run [Monad m] (prover : InteractOutputProver m Output pSpec)
    (challenges : Challenges pSpec) : m (Transcript pSpec × Output) :=
  match pSpec with
  | [] => pure ((), prover)
  | (.P_to_V, _) :: _ => do
    let rest ← prover.2
    let (tr, out) ← rest.run challenges
    return ((prover.1, tr), out)
  | (.V_to_P, _) :: _ => do
    let rest ← prover challenges.1
    let (tr, out) ← rest.run challenges.2
    return ((challenges.1, tr), out)
```

### Prover execution (partial — required for RBR soundness)

RBR soundness requires running the adversary to an intermediate round and
accessing the partial transcript. This was missing in the original design and
is a prerequisite for stating RBR soundness.

```lean
def InteractOutputProver.runToRound [Monad m]
    (prover : InteractOutputProver m Output pSpec)
    (k : Fin (pSpec.length + 1))
    (challenges : PartialChallenges pSpec k)
    : m (PartialTranscript pSpec k × InteractOutputProver m Output (pSpec.drop k))
```

where:
```lean
def PartialChallenges (pSpec : ProtocolSpec) (k : Fin (pSpec.length + 1)) :=
  Challenges (pSpec.takeChecked k ...)
```

Key lemmas needed:
```
challengeTypes_take : (pSpec.take k).challengeTypes = pSpec.challengeTypes.take (challengeCountUpTo k)
challengeTypes_append : (p₁ ++ p₂).challengeTypes = p₁.challengeTypes ++ p₂.challengeTypes
```

Similarly, `runWithLogToRound` wraps the monadic computation with logging:
```lean
def InteractOutputProver.runWithLogToRound [Monad m]
    (prover : InteractOutputProver m Output pSpec)
    (k : Fin (pSpec.length + 1))
    (challenges : PartialChallenges pSpec k)
    : m (PartialTranscript pSpec k × QueryLog oSpec × InteractOutputProver m Output (pSpec.drop k))
```

### `PartialTranscript.concat` — defined by structural recursion, NOT via cast

To avoid non-definitional equalities with `takeChecked`, define `concat`
directly:

```lean
def PartialTranscript.concat {pSpec : ProtocolSpec}
    (tr : PartialTranscript pSpec k)
    (val : (pSpec.get k).snd)
    : PartialTranscript pSpec (k + 1) :=
  match pSpec, k with
  | _ :: _, ⟨0, _⟩ => (val, ())
  | _ :: _, ⟨k+1, h⟩ => (tr.1, PartialTranscript.concat tr.2 val)
```

This avoids any `▸` casts in `StateFunction.toFun_next`.

### Full reduction execution

```lean
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction m StmtIn WitIn StmtOut WitOut pSpec)
    (challenges : Challenges pSpec) : m (...) := do
  let proverOutput ← reduction.prover (stmt, wit)
  let (transcript, stmtOutP, witOut) ← proverOutput.run challenges
  let stmtOutV ← reduction.verifier stmt transcript
  return (transcript, stmtOutP, witOut, stmtOutV)
```

---

## 9. Composition

### Sequential composition of provers

```lean
def Prover.comp (p₁ : Prover m S₁ W₁ S₂ W₂ pSpec₁)
                (p₂ : Prover m S₂ W₂ S₃ W₃ pSpec₂)
    : Prover m S₁ W₁ S₃ W₃ (pSpec₁ ++ pSpec₂) :=
  fun ctx => do InteractOutputProver.comp' (← p₁ ctx) p₂
```

Where `comp'` is structural recursion on `pSpec₁` (from PR #146).

### Sequential composition of n provers

```lean
def Prover.compN (n : ℕ) (Stmt Wit : Fin (n+1) → Type)
    (pSpec : Fin n → ProtocolSpec)
    (prover : ∀ i, Prover m (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    : Prover m (Stmt 0) (Wit 0) (Stmt (.last n)) (Wit (.last n))
        (List.join (List.ofFn pSpec))
```

The resulting spec uses `List.join (List.ofFn pSpec)` (right-associated) rather
than `Fin.foldl'` (left-associated), for better definitional behavior with
`List.join_cons` and `List.ofFn_succ`. For homogeneous composition (all rounds
use the same spec), use `ProtocolSpec.replicate n pSpec`.

### Sequential composition of oracle verifiers

With the `Sublist`-based oracle output:
```lean
def OracleVerifier.comp (v₁ : OracleVerifier ... OStmtIn₁ ... OStmtOut₁ ... pSpec₁)
                         (v₂ : OracleVerifier ... OStmtIn₂ ... OStmtOut₂ ... pSpec₂)
    -- where OStmtIn₂ = OStmtOut₁
    : OracleVerifier ... OStmtIn₁ ... OStmtOut₂ ... (pSpec₁ ++ pSpec₂)
```

The combined verifier:
- Has oracle access to `OStmtIn₁ ++ pSpec₁.messageTypes ++ pSpec₂.messageTypes`
- Runs `v₁.verify` to get `stmtMid`
- Simulates `v₂`'s oracle access to `OStmtOut₁` using `v₁.outputOracles`
- Runs `v₂.verify` with the simulated oracles

---

## 10. Migration Plan

### Phase 0: Infrastructure (new branch)
- [ ] `HVector` (adapted from lean-mlir): `append`, `get`, `ofFn`, `map`, `ext`, simp lemmas
- [ ] `HVector` notation (`[x, y]ₕ`) and `ToTupleType` conversion
- [ ] `List.Member` and `List.Sublist` utilities
- [ ] `ProtocolSpec` as `List (Direction × Type)` with `messageTypes`, `challengeTypes`
- [ ] `messageTypes_append`, `challengeTypes_append` (critical, blocks all composition)
- [ ] `challengeTypes_take` / `PartialChallenges` (required for RBR soundness)
- [ ] `Transcript`, `Challenges`, `Messages`, `PartialTranscript`
- [ ] `PartialTranscript.concat` by structural recursion (no `▸` casts)
- [ ] `oracleSpecOfList` using nested `Sum` (NOT `Fin`-indexed) for VCVio compatibility
- [ ] `QueryImpl.ofSublist` convenience constructor
- [ ] `OracleInterface` instances for `List.get` and `messageTypes.get`

### Phase 1: Core IOP model
- [ ] `InteractOutputProver` with `run`, `runToRound`, and `comp`
- [ ] `InteractOutputProver.runWithLogToRound` (for RBR knowledge soundness)
- [ ] `Prover` (honest prover wrapping `InteractOutputProver`)
- [ ] `Verifier` with `comp`
- [ ] `OracleVerifier` with list-based oracle indexing, `QueryImpl`-based `simulate`, and `reify`
- [ ] `OracleReduction`, `OracleProof`, `Proof` specializations
- [ ] `Reduction.run` / `OracleReduction.run` execution semantics
- [ ] Identity/trivial instances for all of the above

### Phase 2: Security definitions
- [ ] Completeness, perfect completeness
- [ ] Soundness, knowledge soundness (with `Extractor.Straightline`)
- [ ] `StateFunction`, `KnowledgeStateFunction`
- [ ] Round-by-round soundness, RBR knowledge soundness
- [ ] Trivial instances (identity reduction is perfectly secure)

### Phase 3: Composition theorems
- [ ] `Prover.comp` and `Prover.compN`
- [ ] `Verifier.comp` and `Verifier.compN`
- [ ] `OracleVerifier.comp` and `OracleVerifier.compN`
- [ ] `OracleReduction.comp` and `OracleReduction.compN`
- [ ] Completeness composes
- [ ] RBR soundness composes
- [ ] RBR knowledge soundness composes

### Phase 4: Sumcheck trial
- [ ] `SingleRound.pSpec : ProtocolSpec` = `[(.P_to_V, R⦃≤ deg⦄[X]), (.V_to_P, R)]`
- [ ] `SingleRound.prover` as an `InteractOutputProver`
- [ ] `SingleRound.oracleVerifier` with list-based oracles
- [ ] `SingleRound.oracleReduction`
- [ ] Prove single-round perfect completeness
- [ ] Prove single-round RBR knowledge soundness (error `deg / |R|`)
- [ ] `General.oracleReduction` via `compN`
- [ ] Prove full completeness and RBR knowledge soundness via composition

### Phase 5: Port remaining protocols
- [ ] FRI
- [ ] WHIR / STIR
- [ ] Spartan
- [ ] Binius protocols
- [ ] Fiat-Shamir compilation
- [ ] Commitment scheme integration

---

## 11. Open Questions

### Q1: Should `OracleInterface` be bundled into the protocol spec?

**Decision (resolved): Bundle `OracleInterface` into the spec, but NOT `SampleableType`.**

`OracleInterface` is intrinsic to the protocol (how the verifier queries messages).
`SampleableType` is a parameter of the analysis (how challenges are sampled).

```lean
inductive Round where
  | P_to_V (T : Type) (oi : OracleInterface T)
  | V_to_P (T : Type)

def ProtocolSpec := List Round
```

Smart constructors infer `OracleInterface` at construction time:
```lean
def ProtocolSpec.msg (T : Type) [oi : OracleInterface T] : Round := .P_to_V T oi
def ProtocolSpec.chal (T : Type) : Round := .V_to_P T
```

This eliminates instance synthesis through `List.get ∘ messageTypes` entirely.
Manual instance restating (currently lines 159-178 of SingleRound.lean) disappears.

**Open sub-question (deferred to BCS implementation):** Should `Round` also have
a `P_to_V_plain` constructor for messages without oracle interfaces? See Section 14
for analysis. Current decision: start with the two-constructor `Round` above, extend
if needed for BCS. Using `OracleInterface.instDefault` for plain messages is the
fallback if a third constructor is not added.

### Q2: Should challenges be sampled inside the prover or outside?

Currently challenges are sampled via `OracleComp` queries to a challenge oracle.
An alternative: sample all challenges upfront and pass them in.

The `InteractOutputProver.run` in PR #146 takes `challenges : Challenges pSpec`
as input — this is the "outside" approach.

**For execution:** Outside sampling is simpler.
**For security:** The two models are mathematically equivalent because
`challengeQueryImpl` samples independently, so lazy-interleaved vs.
eager-upfront produce the same joint distribution (by Fubini). However,
the correct "outside" completeness formulation is:

```lean
Pr[event | do
  let challenges ← sampleAllChallenges pSpec
  (simulateQ impl (reduction.run stmtIn witIn challenges)).run' (← init)]
  ≥ 1 - completenessError
```

This is a **single `Pr`** over the joint challenge + shared-oracle randomness.
It is **NOT** `∀ challenges, Pr[...] ≥ 1 - ε` (which is strictly stronger
and fails in general).

With outside sampling, the `pImpl = impl.addLift challengeQueryImpl` combining
step from the current model disappears — only `impl : QueryImpl oSpec (StateT σ ProbComp)`
is needed. This is a simplification.

**For Fiat-Shamir:** Challenges are derived from messages, so "outside" doesn't
apply directly. Fiat-Shamir is a separate transformation.

**Decision:** Sample outside for basic model. Add Fiat-Shamir as a separate
transformation.

### Q3: How to handle `oSpec` (shared oracles)?

The shared oracle `oSpec : OracleSpec ι` (random oracle, sampling oracle) is
orthogonal to the list-based refactor. Keep it as-is — it's a parameter to the
prover/verifier monads.

The prover's monad `m` should be `OracleComp (oSpec + challengeOracle)` or similar.
The exact factoring depends on VCVio's monad infrastructure.

### Q4: `Fin.foldl'` vs explicit list in `compN`

**Decision (from audit):** Use `List.join (List.ofFn pSpec)` for heterogeneous
composition. This produces right-associated appends (`pSpec 0 ++ (pSpec 1 ++ ...)`)
which have better lemma coverage (`List.join_cons`, `List.ofFn_succ`) and match
the existing recursive composition structure in `General.lean`.

For homogeneous composition (like Sumcheck), define `ProtocolSpec.replicate` with
`replicate 0 = []` and `replicate (n+1) = pSpec ++ replicate n`.

---

## 12. Audit Findings (Council Pass)

The following issues were surfaced by a 6-agent parallel audit and incorporated
into the design above. Preserved here for traceability.

### Resolved

1. **`InteractOutputProver.runToRound` was missing.** The RBR soundness game
   requires running an adversary to an intermediate round. Added to Section 8
   with `PartialChallenges` infrastructure. (Correctness + Data Flow agents)

2. **`oracleSpecOfList` must use nested `Sum`, not `Fin`.** VCVio has zero
   `SubSpec` instances for `Fin`-indexed specs. All simulation/composition
   machinery is `Sum`-based. Changed in Section 5.2. (Wildcard + Tie-breaker agents)

3. **`Sublist` alone is insufficient for output oracles.** Composition needs
   query routing (a `QueryImpl`-like operation), so `Sublist` adds an
   intermediate step. Changed to `QueryImpl` directly in Section 5.3, with
   `QueryImpl.ofSublist` as convenience. (Architecture + Wildcard agents)

4. **Probability formulation for "outside" challenges.** The correct formulation
   is a single `Pr` over joint challenge + oracle randomness, NOT `∀ challenges`.
   Clarified in Q2 and Section 7. (Data Flow agent)

5. **Adversarial quantifier structure.** Clarified that soundness quantifies
   `∀ Output, ∀ adversary : InteractOutputProver m Output pSpec`, equivalent
   to the current model. Added to Section 7. (Correctness agent)

### Open (deferred to implementation)

6. **`OracleInterface` instance synthesis through `List.get ∘ messageTypes`**
   will fail for abstract specs. The current codebase already has this problem
   (manually restated instances in `SingleRound.lean:155-178`).
   **Resolved:** Bundle `OracleInterface` into `Round` (see Q1 and Section 14).
   (API Design + Correctness agents)

7. **Trailing `PUnit` ergonomics.** Resolved by switching from `TProd` to
   `HVector` (adapted from lean-mlir). `HVector` avoids trailing `PUnit`
   entirely — `nil` is its own constructor. (API Design agent, resolved)

8. **`PartialTranscript.concat` definitional reduction.** The claim that
   `takeChecked_succ` gives definitional equality is incorrect for abstract
   `pSpec`. Solution: define `concat` by structural recursion directly.
   Added to Section 8. (Correctness agent)

9. **`Fin.foldl'` vs `List.join` for `compN`.** `Fin.foldl'` produces
   left-associated appends that Lean can't unfold. Use `List.join (List.ofFn pSpec)`
   for heterogeneous composition, `ProtocolSpec.replicate` for homogeneous.
   (Architecture agent)

---

## 13. Summary of Key Design Choices

| Aspect | Current | Proposed |
|---|---|---|
| Protocol spec | `ProtocolSpec n` (`Fin`-indexed) | `List Round` (with bundled `OracleInterface`) |
| Transcript | `(i : Fin n) → pSpec.Type i` | `HVector Round.type pSpec` |
| Prover | Stateful struct with `sendMessage`/`receiveChallenge` | Coinductive `InteractOutputProver` (renamed `Prover`) |
| Verifier | `StmtIn → FullTranscript → OptionT (OracleComp oSpec) StmtOut` | Same, with `Transcript` replacing `FullTranscript` |
| Oracle verifier | `OracleVerifier` (separate type) | Retained as separate type (dual-track) |
| Oracle indices | `ιₛᵢ : Type` (arbitrary) | `List Type` |
| Output oracles | `embed : ιₛₒ ↪ ιₛᵢ ⊕ MessageIdx` + `hEq` | `QueryImpl`-based `simulate` + `reify` |
| Composition | `seqCompose` with `Fin` reindexing | `comp` via list append |
| Partial transcript | `Transcript k` via `Fin.take` | `PartialTranscript k` via `List.take` |
| Challenge sampling | Inside (oracle query) | Outside (pre-sampled, passed to `run`) |
| Verifier tracks | Unified or separate? | **Dual-track**: `Verifier` + `OracleVerifier` |

---

## 14. BCS Transform Analysis (Council Pass #2)

A 4-agent council analyzed the BCS transform and its implications for the
oracle/plain message design. Key input: the user pointed out that BCS literally
changes message types (from oracle message `M` to commitment `C`), and commitments
have no `OracleInterface`. This section records the findings.

### 14.1. What BCS does at the type level

The BCS transform converts `OracleReduction → Reduction`:

1. **Message type change.** For each oracle message `M_i` with interface `OI_i`,
   BCS replaces it with commitment type `C_i`. The existing `renameMessage` function
   (`BCS/Basic.lean:51-54`) does exactly this — it preserves directions but swaps
   `pSpec.Type i` with `NewMessage ⟨i, h⟩` for each P_to_V index.

2. **Oracle interface removal.** Commitment types (`C_i`) have no meaningful
   `OracleInterface`. The verifier sees commitments directly, not through oracle
   queries. This is the fundamental reason BCS output is a `Reduction`, not an
   `OracleReduction`.

3. **Opening argument appendage.** For each verifier query `q` to oracle message
   `M_i`, BCS appends an opening argument — an interactive proof that the claimed
   response equals `OI_i.answer M_i q`. These opening arguments are plain `Proof`
   (= `Reduction ... Bool Unit pSpec`), not `OracleProof`.

4. **Composed protocol spec.** The result is
   `pSpec.renameMessage CommType ++ openingSpecs`, with round count
   `n + Σ_i nCom_i`. The commented-out definition (`BCS/Basic.lean:56-60`) shows
   `ProtocolSpec (n + ∑ i, nCom i)`.

### 14.2. Pipeline: IOP → BCS → Fiat-Shamir

The pipeline is strictly ordered and each step is a type-level transformation:

```
OracleReduction pSpec  --(BCS)-->  Reduction pSpec'  --(FS)-->  NonInteractiveReduction
```

- **BCS input**: `OracleReduction` with `[∀ i, OracleInterface (pSpec.Message i)]`
- **BCS output**: `Reduction` on renamed spec (commitments, no oracle interfaces)
- **FS input**: `Reduction` (all messages plain, required for hashing)
- **FS output**: `NonInteractiveReduction` in the random oracle model

**Fiat-Shamir cannot work with oracle messages.** The FS verifier
(`FiatShamir/Basic.lean:127-133`) receives all messages directly via
`∀ i, pSpec.Message i` and calls `messages.deriveTranscriptFS` to reconstruct
challenges. Oracle access would break this.

### 14.3. Verifier design: dual-track confirmed

**Decision: Keep separate `Verifier` and `OracleVerifier` types.**

Rationale:
- `Verifier` (plain) is always simpler — no oracle simulation, no `QueryImpl`
- `OracleVerifier` (oracle) adds `simulate`/`reify` for query-level reasoning
- The bridge `OracleVerifier.toVerifier` converts by simulating oracle access
- Duplication is bounded (~5 definition pairs in `Basic.lean`), and security
  definitions are pure delegation (oracle versions call `toVerifier`/`toReduction`)
- BCS maps cleanly: `OracleReduction → Reduction`
- FS maps cleanly: `Verifier → NonInteractiveVerifier`

A unified "always-oracle" verifier (with `instDefault` for plain messages) was
rejected because:
- Trivial oracle queries add noise to proofs and execution
- Commitments have no meaningful `OracleInterface`
- FS needs direct message access, not oracle queries

### 14.4. Hybrid protocol question (deferred)

**Question:** Should `Round` have a `P_to_V_plain` constructor for plain messages?

**Motivation:** BCS compilation is per-round in the original paper (BCS16,
Section 5). Each FIOP round's oracle message gets its own commitment. The
intermediate state during compilation (messages 1..i committed, i+1..n still
oracle) is inherently hybrid. The IPCP model (Kalai-Raz 2008) is a recognized
precedent for hybrid oracle/plain messages.

**Arguments for `P_to_V_plain`:**
- Clean distinction between oracle and plain at the spec level
- BCS naturally maps `P_to_V_oracle → P_to_V_plain` per message
- No meaningless `instDefault` oracle interfaces on commitments
- Enables inductive BCS compilation (per-message security proof)

**Arguments against:**
- Extra case analysis in every proof (3 constructors instead of 2)
- Unused until BCS is formalized (Sumcheck has zero plain messages)
- Monolithic BCS (compile all at once) doesn't need intermediate hybrid states

**Decision: Defer.** Start with the two-constructor `Round` (always bundle
`OracleInterface`). Both BCS approaches remain viable:
- Monolithic BCS: commitments use `instDefault`, `Verifier` ignores it
- Inductive BCS: add `P_to_V_plain` constructor later (contained breaking change
  within `Refactor/`)

### 14.5. Naming conventions

**Resolved:**
- `InteractOutputProver` → `Prover` (the core coinductive type)
- `Prover` (current) → wrap as an abbreviation: `HonestProver := StmtIn × WitIn → m (Prover ...)`
- Keep `OracleVerifier` and `Verifier` as separate types (dual-track)
- Keep `OracleReduction` and `Reduction` as separate types
- `OracleProof` / `Proof` remain as specializations (output = Bool, no output witness)
- Shorter variable names in local contexts: `chal` for challenges, `tr` for transcript,
  `ptr` for partial transcript

---

## 15. eprint 2025/902 — FIOP + FC Pipeline (Chiesa-Guan-Knabenhans-Yu)

This paper formalizes the generalized BCS transform and is directly relevant to
ArkLib's BCS implementation.

### 15.1. Key definitions

**FIOP (Definition 3.10):** A public-coin IOP parameterized by *query classes*
`Q_1, ..., Q_k` (instead of point queries). Each prover message `Π_i` is oracle-
accessible via queries `α ∈ Q_i` returning `α(Π_i)`. All prover messages are oracle
messages (no hybrid). Standard IOPs are FIOPs with point query classes; polynomial
IOPs use evaluation query classes.

**Functional Commitment (FC):** An FC scheme for query class `Q` has `Gen`, `Commit`,
`Open`, `Check` algorithms. The security notion is **function binding** (not
extractability): no adversary can produce a commitment with two valid openings for
the same query that give different answers, unless there exists a single consistent
underlying message.

**Batched FC:** Supports opening a set of queries at once via `Batch[Q, m]`. Used
in the actual compilation.

### 15.2. The "Funky" protocol (Construction 4.1)

The compilation `Funky[FIOP, bFC]` produces an interactive argument:

1. **Commitment phase** (simulates FIOP): For each FIOP round `i`, prover commits
   `Π_i` to get `cm_i`, sends `cm_i` (plain). Verifier sends random `ρ_i`.
2. **Query-answer phase**: Prover determines verifier's queries `Q_i`, computes
   evaluations `β_i = {α(Π_i) : α ∈ Q_i}`, sends `(Q_i, β_i)` (plain).
3. **Opening phase**: Run batched FC opening protocol (interactive, `k_bFC` rounds).
4. **Verifier checks**: FIOP verifier accepts with given evaluations AND all FC
   openings verify.

**All messages in the compiled protocol are plain.** The commitments, query-answer
pairs, and opening proofs are all sent as standard messages. Total rounds:
`k_FIOP + 1 + k_bFC`.

### 15.3. Security proof structure

The proof is a **direct reduction** (not inductive over rounds):

- Uses **state-restoration (SR) soundness** throughout (equivalent to FS security
  in the ROM). RBR soundness implies SR soundness [CY24], so any FIOP proven to
  have RBR soundness automatically qualifies.
- The reductor, given an SR adversary against the Funky protocol, constructs an SR
  adversary against the underlying FIOP by:
  1. Rewinding the adversary up to `N` times per move
  2. Collecting valid query-answer pairs from successful rewinds
  3. Using a query-class-specific `SolverQ` to reconstruct FIOP strings
  4. Forwarding reconstructed strings to the FIOP SR game
- Error bound: `ε_ARG ≤ ε_FIOP + Σ_i [ε_bFC + ε_tail(ℓ_i, q_i, N)]`
  where `ε_tail` is the "tail error" (probability that `N` rewinds don't yield
  enough constraints).

**Key insight for ArkLib:** The security notion for FC schemes is **function
binding** (weaker than extractability, falsifiable). This differs from ArkLib's
current `extractability` definition in `CommitmentScheme/Basic.lean`.

### 15.4. Implications for ArkLib design

1. **All-oracle FIOP model is standard.** The paper confirms that all prover messages
   in an FIOP are oracle messages — no per-message hybrid annotation needed at the
   FIOP level. Hybrid states only arise during compilation.

2. **BCS is monolithic per the paper.** The Funky protocol compiles all oracle
   messages at once (one commitment per round). The security proof is a single
   reduction, not inductive. However, the error bound sums over rounds, suggesting
   an inductive proof structure could also work.

3. **Query class = `OracleInterface` generalization.** ArkLib's `OracleInterface`
   corresponds to a query class. The paper's `SolverQ` (reconstruct data from
   query-answer pairs) could be formalized as a field in `OracleInterface` or as
   a separate typeclass.

4. **Function binding vs extractability.** ArkLib should define function binding
   alongside extractability for commitment schemes.

5. **State-restoration soundness should be added.** ArkLib currently has RBR
   soundness. The paper's pipeline goes through SR soundness. Adding SR soundness
   definitions (or proving RBR → SR → FS) closes the loop.

6. **The compiled protocol's `ProtocolSpec`** is naturally expressed as
   `pSpec.renameMessage CommType ++ queryAnswerRound ++ openingSpecs`, matching
   ArkLib's `List.append`-based composition.

### 15.5. Remaining questions for BCS formalization

- Should `SolverQ` be bundled into `OracleInterface` or a separate typeclass?
- Is function binding the right default security notion for commitment schemes?
- Should the "query-answer phase" be a single round or per-message rounds?
- How to formalize batched FC schemes in the list-based model?
