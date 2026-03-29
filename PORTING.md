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
                           MonadDecoration, append/replicate/chain, comp
                           — universe-polymorphic throughout
  TwoParty.lean            Role, RoleDecoration (= Decoration on Spec),
                           Strategy.withRoles, Counterpart (with Output param),
                           runWithRoles (returns both outputs),
                           SenderDecoration (= Refine over RoleDecoration),
                           per-node monad variants, composition combinators
  Multiparty.lean          PartyDecoration, PartyDecoration.toRoles (via
                           Decoration.map), ThreeParty examples
  Reduction.lean           Prover (monadic, full dependency chain, dependent
                           WitnessOut), Verifier (= Counterpart with OptionT
                           output), Reduction, Proof, execute, Verifier.run
  Security.lean            randomChallenger, completeness (HasEvalSPMF,
                           statement-indexed), soundness (HasEvalSPMF, Accepts
                           set), ClaimTree (inductive on Spec + RoleDecoration),
                           good/Terminal/follow/terminalGood/maxPathError/IsSound,
                           bound_terminalProb, rbrSoundness (with Accepts),
                           soundness_of_claimTree
  Oracle.lean              OracleDecoration (OracleInterface at sender nodes),
                           QueryHandle, toOracleSpec, answerQuery,
                           OracleCounterpart (with Output param, growing oracle
                           access), InteractiveOracleVerifier (= OracleCounterpart
                           with verify output), OracleCounterpart.mapOutput,
                           OracleVerifier (batch: iov + simulate + reify),
                           OracleProver (full dependency chain), OracleReduction

OracleReduction/         ← ArkLib-specific (old core, to be replaced)
  OracleInterface.lean     Stable, reused by Interaction/Oracle.lean
  (TODO) Security/         Completeness, soundness, knowledge soundness, RBR

ProofSystem/             ← concrete protocols on top of the above
  (TODO) Sumcheck/         Multi-round sumcheck
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
- [x] **Phase 2e: N-ary composition** — `replicate`, `chain`, `iterate`,
  `chainComp` for `Spec`, `Decoration`, `Strategy`, `Transcript`; round-trip
  lemmas (`split_join`, `chainSplit_chainJoin`); role-aware wrappers for
  `RoleDecoration`, `Counterpart`, `Strategy.withRoles`
- [x] **Phase 2f: Decoration.Refine** — displayed decoration combinator
  (cf. displayed algebras, ornaments). `Refine F spec d` carries `F X l` at
  each node with label `l : L X` from decoration `d`. Composition:
  `Refine.append`, `.replicate`, `.chain`, `.map`. `SenderDecoration` in
  `TwoParty.lean` as a specialization to `RoleDecoration`.
- [x] **Phase 3: OracleDecoration** — `OracleDecoration` assigns
  `OracleInterface` instances at sender nodes (data, not typeclass).
  `QueryHandle` indexes oracle queries parameterized by a transcript (path-
  dependent oracle access — fundamental to W-type interactions where move types
  depend on prior moves). `toOracleSpec` and `answerQuery` defined by recursion.
- [x] **Phase 3b: Oracle verifier redesign** — `Verifier` updated with
  `StmtOut` output type and `verify : StmtIn → Transcript → OptionT m StmtOut`
  (was `decide : StmtIn → Transcript → m Bool`).
  `OracleCounterpart` models round-by-round challenger with growing oracle
  access (`accSpec` starts at `[]ₒ`, grows by `oi.toOC.spec` at sender nodes).
  `InteractiveOracleVerifier` unifies challenger + verification into one
  recursive type (= `OracleCounterpart` at internal nodes, verification
  function at `.done`). `toOracleCounterpart` extracts the challenger.
  `OracleVerifier` bundles `iov` + `simulate` + `reify` (both transcript-
  dependent). `OracleProver`, `OracleReduction`, `OracleProof` defined.

- [x] **Phase 4: Security definitions** — `randomChallenger` (generic sampler
  to `Counterpart ProbComp`), `Reduction.completeness` / `perfectCompleteness`,
  `soundness` (quantifies over all malicious provers, uses `Accepts` set),
  `ClaimTree` (inductive on `Spec` + `RoleDecoration`),
  `good`/`Terminal`/`follow`/`terminalGood`/`maxPathError`/`IsSound`,
  `bound_terminalProb` (`sorry` proof), `rbrSoundness` (deterministic verify,
  with `Accepts`), `soundness_of_claimTree` (`sorry` bridge).
- [x] **Phase 4b: Generalize Counterpart, Reduction, Security** —
  `Counterpart` takes explicit `Output : Transcript spec → Type u` parameter
  (`Output ⟨⟩` at `.done`; old no-output = `fun _ => PUnit`).
  `runWithRoles` returns both prover and counterpart outputs.
  `Counterpart.iterate`/`chainComp` thread state `β` (mirrors strategy pattern).
  `OracleCounterpart` takes `Output : OracleSpec → Type` at `.done`;
  `InteractiveOracleVerifier` is now an abbrev to `OracleCounterpart`.
  `Prover` is monadic (`run` returns `m (Strategy ...)`), statement-indexed
  with full dependency chain (`Context : Statement → Spec`, `Roles`,
  `StatementOut`, `WitnessOut : ... → StatementOut → Type`).
  `Verifier` is an `abbrev` for `Counterpart` with `OptionT m (VerOutput)`.
  Security uses generic `[HasEvalSPMF m]` instead of `ProbComp`.

## In progress

- [ ] **Sequential composition** — `Strategy.comp`, `Counterpart.comp`, and
  `Reduction.comp` for role-aware specs (infrastructure in place on `Spec`,
  needs role-aware wrappers and `RoleDecoration.append`)

## Planned
- [ ] **Phase 5: Sumcheck migration** — express sumcheck in new types
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

- **Execution of OracleReduction**: `OracleReduction.execute` needs
  `simulateQ` to resolve transcript-dependent oracle queries. The type
  involves `OracleComp (oSpec + od.toOracleSpec tr)` where `tr` is the
  transcript — requires careful monad plumbing. Currently `sorry`.

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

- **Dependent vs non-dependent output** (RESOLVED): `Prover` now uses
  dependent output `(fun tr => (sOut : StatementOut s tr) × WitnessOut s tr sOut)`.
  `Verifier` output is `OptionT m (VerOutput s tr)`. `Counterpart` takes
  explicit `Output : Transcript spec → Type u` parameter.

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
