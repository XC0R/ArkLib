# Core Rebuild: Porting Progress

Tracking the replacement of ArkLib's core IOR layer with one built on
`Interaction.Spec` (W-type game trees) + `RoleDecoration`.
Branch: `quang/core-rebuild`, based on `quang/bump-comppoly`.

Reference branch: `quang/iop-refactor` (old Refactor/ approach, archived).

## Architecture

```
Interaction/             ← generic, standalone (future VCVio)
  Basic.lean               Spec.{u} (W-type), Transcript, Strategy, Decoration,
                           Decoration.map, Decoration.Refine, BundledMonad,
                           MonadDecoration,                            append/replicate/Chain (continuation-style),
                           stateChain (state-indexed), liftAppend,
                           stateChainLiftJoin, stateChainFamily, role-free
                           composition — universe-polymorphic throughout
  TwoParty.lean            Role, RoleDecoration (= Decoration on Spec),
                           Strategy.withRoles, Counterpart (with Output param),
                           runWithRoles (returns both outputs),
                           SenderDecoration (= Refine over RoleDecoration),
                           per-node monad variants, role-aware
                           append/replicate/stateChain combinators
  Multiparty.lean          PartyDecoration, PartyDecoration.toRoles (via
                           Decoration.map), ThreeParty examples
  Reduction.lean           Prover (monadic setup, plain WitnessIn),
                           Verifier (= Counterpart with transcript-indexed leaf
                           output), transcript-indexed StatementOut/WitnessOut,
                           Reduction, Reduction.Continuation, Proof, execute,
                           Verifier.run, comp, stateChainComp,
                           stateChainCompUniform, ofChain (stateless
                           chain-based reduction)
  Security.lean            randomChallenger, completeness /
                           perfectCompleteness / soundness /
                           knowledgeSoundness (HasEvalSPMF),
                           completeness/soundness composition for `comp`,
                           `Extractor.Straightline`, ClaimTree,
                           KnowledgeClaimTree, rbrSoundness /
                           rbrKnowledgeSoundness (currently via random
                           challenger + transcript predicates)
  Oracle.lean              OracleDecoration (OracleInterface at sender nodes),
                           QueryHandle, toOracleSpec, answerQuery,
                           OracleCounterpart (with Output param, growing oracle
                           access), InteractiveOracleVerifier (= OracleCounterpart
                           with OptionT verify output at `.done`),
                           OracleVerifier (batch: iov + simulate + reify),
                           OracleProver, OracleReduction

OracleReduction/         ← ArkLib-specific (old core, to be replaced)
  OracleInterface.lean     Stable, reused by Interaction/Oracle.lean
  (TODO) Security/         Completeness, soundness, knowledge soundness, RBR

ProofSystem/             ← concrete protocols on top of the above
  Sumcheck/Interaction/    Interaction-native sumcheck: CompPoly types,
                           single-round spec/prover/verifier, n-round
                           stateChain composition, oracle layer (WIP)
  (TODO) FRI, Binius, ...
```

No `ProtocolSpec` or `Direction` wrapper — `Spec` + `RoleDecoration` replaces
`ProtocolSpec n` entirely. No separate `TwoParty` or `Multiparty` inductive —
roles are a decoration on `Spec`.

## Completed

- [x] **Phase 1: Interaction foundation** — `Spec`, `Transcript`, `Strategy`,
  `Decoration`, `append`, `comp` in `Basic.lean`, universe-polymorphic
- [x] **Phase 2: Two-party and reduction** — `Role`, `RoleDecoration`,
  `Strategy.withRoles`, `Counterpart`, `runWithRoles` in `TwoParty.lean`;
  `Prover`, `Verifier`, `Reduction`, `execute` in `Reduction.lean`
- [x] **Phase 2b: Kill TwoParty / Multiparty inductives** — removed both
  separate inductives; roles are now a `Decoration (fun _ => Role)` on `Spec`;
  N-party is `Spec` + `PartyDecoration` + `Decoration.map`; all `rfl` examples
  pass through the projection
- [x] **Phase 2c: Monad decoration generalization** — `BundledMonad` standalone
  at root; `Counterpart.withMonads` fully monadic (uses node monad at all roles);
  `runWithRolesAndMonads` takes two separate monad decorations (strategy vs
  counterpart); `Decoration.map` added for natural transformations between
  decorations
- [x] **Phase 2d: Universe polymorphism** — `Spec.{u}`, `BundledMonad.{u,v}`,
  `Decoration.{u,v}`, `Strategy.{u}`, all combinators universe-polymorphic;
  `TwoParty.lean` / `Reduction.lean` work at `u = 0`
- [x] **Phase 2e: N-ary composition** — `replicate`, `Chain` (continuation-
  style), `stateChain` (state-indexed), `iterate`, `stateChainComp`,
  `Transcript.stateChainJoin` / `stateChainUnjoin`, and `stateChainFamily`
  for `Spec`, `Decoration`, `Strategy`, `Transcript`; round-trip lemmas
  (`split_append`, `append_split`, `stateChainSplit_stateChainAppend`,
  `stateChainUnjoin_join`, `stateChainJoin_unjoin`); role-aware wrappers for
  `RoleDecoration`, `Counterpart`, `Strategy.withRoles`
- [x] **Phase 2f: Decoration.Refine** — displayed decoration combinator
  (cf. displayed algebras, ornaments). `Refine F spec d` carries `F X l` at
  each node with label `l : L X` from decoration `d`. Composition:
  `Refine.append`, `.replicate`, `.stateChain`, `.map`. `SenderDecoration` in
  `TwoParty.lean` as a specialization to `RoleDecoration`.
- [x] **Phase 3: OracleDecoration** — `OracleDecoration` assigns
  `OracleInterface` instances at sender nodes (data, not typeclass).
  `QueryHandle` indexes oracle queries parameterized by a transcript (path-
  dependent oracle access — fundamental to W-type interactions where move types
  depend on prior moves). `toOracleSpec` and `answerQuery` defined by recursion.
- [x] **Phase 3b: Oracle verifier redesign** —
  `OracleCounterpart` models the round-by-round challenger with growing oracle
  access (`accSpec` starts at `[]ₒ`, grows by `oi.toOC.spec` at sender nodes).
  `InteractiveOracleVerifier` is the unified recursive type
  (= `OracleCounterpart` with `OptionT` verification output at `.done`).
  `OracleVerifier` bundles `iov` + `simulate` + `reify` (both transcript-
  dependent). `OracleProver` and `OracleReduction` are defined.

- [x] **Phase 4: Security definitions** — `randomChallenger` (generic sampler
  to `Counterpart ProbComp`), `Reduction.completeness` / `perfectCompleteness`,
  `soundness`, `knowledgeSoundness`, `ClaimTree` / `KnowledgeClaimTree`
  (inductive on `Spec` + `RoleDecoration`), `good`/`Terminal`/`follow`/
  `terminalGood`/`maxPathError`/`IsSound`, `bound_terminalProb`
  (`sorry` proof), `rbrSoundness` / `rbrKnowledgeSoundness`, and the
  current bridge theorems (`sorry` where noted).
- [x] **Phase 4b: Counterpart output + simplified Reduction/Security** —
  `Counterpart` takes explicit `Output : Transcript spec → Type u` parameter
  (`Output ⟨⟩` at `.done`; old no-output = `fun _ => PUnit`).
  `runWithRoles` returns both prover and counterpart outputs.
  `Counterpart.iterate`/`stateChainComp` thread state `β` (mirrors strategy pattern).
  `OracleCounterpart` takes `Output : OracleSpec → Type` at `.done`;
  `InteractiveOracleVerifier` is now an abbrev to `OracleCounterpart`.
  Plain `Reduction` uses monadic prover setup, plain `WitnessIn`, and
  transcript-indexed `StatementOut` / `WitnessOut` as parallel families
  (no `WitnessOut` dependency on `StatementOut`).
  `Verifier` is an `abbrev` for `Counterpart` with caller-chosen leaf output;
  acceptance semantics live in `StatementOut` / `Accepts`.
  Security uses generic `[HasEvalSPMF m]` instead of `ProbComp`.
- [x] **Phase 4c: Role-aware sequential composition** —
  `Strategy.compWithRoles`, `Counterpart.append`, `Reduction.comp`, and the
  chain builders `Reduction.stateChainComp` / `Reduction.stateChainCompUniform`
  are implemented on top of `Spec.append` / `Spec.stateChain`.
  `Reduction.ofChain` provides stateless reduction composition over `Spec.Chain`.
- [x] **Phase 4d: Security composition + extractor cleanup** —
  `Reduction.comp` now factors through transcript-indexed
  `Reduction.Continuation`, with `reduction1` / `reduction2` naming throughout.
  `Reduction.completeness_comp`, `Reduction.perfectCompleteness_comp`, and
  `Reduction.soundness_comp` are proved against that interface.
  Security relations now take statement output before witness output, and
  `knowledgeSoundness` uses a dedicated `Extractor.Straightline` instead of an
  ad-hoc function type. `knowledgeSoundness_implies_soundness` is available
  when accepted terminal statements admit a canonical transcript-indexed
  `WitnessOut`.

## In progress

- [ ] **Verifier-indexed round-by-round security** — after landing the
  composition theorems and straightline-extractor cleanup, the main remaining
  `Security.lean` task is still to rephrase the claim-tree layer in terms of
  the actual `Verifier` object and its outputs instead of
  `randomChallenger`-level transcript predicates (`Accepts`, `relOut`)

## Planned
- [ ] **Phase 5: Sumcheck migration** — interaction-native sumcheck started:
  `CompPoly` types (`CDegreeLE`, `CMvDegreeLE`), single-round spec/prover/verifier,
  `n`-round `stateChain` composition, oracle layer stub. Remaining: fill `sorry`
  obligations, connect to old `Sumcheck.Spec` proofs, oracle verifier body
- [ ] **Phase 6: Protocol migration** — FRI, Binius, Whir, Stir, Components,
  CommitmentScheme
- [ ] **Fiat-Shamir** — abstract FS transform on Spec + RoleDecoration
- [ ] **DuplexSponge FS** — concrete instantiation (deferred)
- [ ] **BCS transformation** — IOR + commitment → IR (deferred)

## Open questions / issues

- **OracleInterface integration** (RESOLVED): Oracle access is modeled via
  `OracleDecoration` — a per-sender-node attachment of `OracleInterface`
  instances as data (not typeclass). The oracle spec for querying messages is
  path-dependent (parameterized by the transcript), reflecting the W-type
  structure where move types depend on prior moves. This differs fundamentally
  from the old flat `ProtocolSpec n` approach.

- **Execution of OracleReduction**: `OracleReduction.execute` has not yet been
  reintroduced. It will need `simulateQ` to resolve transcript-dependent oracle
  queries, with types involving `OracleComp (oSpec + od.toOracleSpec tr)` for
  the executed transcript `tr`.

- **Growing oracle access**: Both `OracleCounterpart` and
  `InteractiveOracleVerifier` use an `accSpec` parameter that grows at each
  sender node. This faithfully models verifier gaining oracle access round by
  round, supporting non-public-coin protocols. The accumulation is:
  `accSpec₀ = []ₒ`, then `accSpecᵢ₊₁ = accSpecᵢ + oiᵢ.toOC.spec`.
  The `OracleVerifier.iov` field starts with `accSpec = []ₒ`.

- **`simulate` and `reify` are transcript-dependent**: Unlike the flat
  `ProtocolSpec n` model where message types are static, in the W-type model
  the oracle spec depends on the transcript (path through the tree). Both
  `simulate` and `reify` must take a `Transcript` argument.

- **Witness typing** (RESOLVED): `WitnessIn` is now a plain type, not
  dependent on the input statement. `WitnessOut` remains parallel to
  `StatementOut` (both indexed by `(s, tr)`), so prover input/output are plain
  products and statement/witness compatibility is expressed in security
  relations rather than in the types.

- **Sequential security composition** (RESOLVED): `Reduction.comp` now consumes
  the second stage as a transcript-indexed `Reduction.Continuation`, so the
  completeness / perfect-completeness / soundness composition theorems can
  quantify directly over first-phase transcripts without encoding the second
  reduction awkwardly inside the theorem statement.

- **Knowledge soundness implies soundness** (PARTIALLY RESOLVED): the bridge
  theorem is now proved, but it needs an explicit transcript-indexed
  `acceptWitness` selector. Without that extra datum, the current API does not
  provide a way to reconstruct a `WitnessOut` merely from acceptance of a
  terminal `StatementOut`.

- **Verifier-indexed RBR semantics**: `ClaimTree` / `rbrSoundness` currently
  talk about transcript predicates and `randomChallenger`, not the full
  statement-indexed `Verifier` object. This is the main remaining design gap in
  `Security.lean`.

- **Where Interaction goes long-term**: planned to move to VCVio once stable.
  Keep it import-free from ArkLib (except `Oracle.lean` which bridges VCVio).

## Related work

Our framework independently converges with several lines of work:

- **Escardo–Oliva (2023)** "Higher-order Games with Dependent Types" (TCS 974):
  type trees `𝑻` (= `Spec`), paths (= `Transcript`), `structure S`
  (= `Decoration S`), strategies, `Overline` (= `Decoration.map`).
  Multiple independent decorations; our `Refine` generalizes to dependent ones.
- **Hancock–Setzer (2000)**: structural recursion on interaction interface.
- **Interaction Trees** (Xia et al., POPL 2020): coinductive free monad analog.
- **Displayed algebras / Ornaments** (McBride 2010): `Decoration.Refine`.
- **Session types**: `Spec + RoleDecoration` as dependent session types.

## Old core (to be replaced)

| Area | Files | Status |
|------|-------|--------|
| `OracleReduction/ProtocolSpec/` | 3 files | Replaced by `Interaction/Basic/` modules |
| `OracleReduction/Basic.lean` | 1 file | Replaced by `Interaction/Reduction.lean` |
| `OracleReduction/` (rest) | ~32 files | Untouched, will break |
| `ProofSystem/` | ~50 files | Untouched, will break |
| `CommitmentScheme/` | ~6 files | Untouched, will break |
| `OracleReduction/OracleInterface.lean` | 1 file | Stable, to be reused |

Breakage is expected and intentional. We fix downstream incrementally.
