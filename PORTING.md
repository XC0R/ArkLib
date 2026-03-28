# Core Rebuild: Porting Progress

Tracking the replacement of ArkLib's core IOR layer with one built on
`Interaction.Spec` (W-type game trees) + `RoleDecoration`.
Branch: `quang/core-rebuild`, based on `quang/bump-comppoly`.

Reference branch: `quang/iop-refactor` (old Refactor/ approach, archived).

## Architecture

```
Interaction/             ← generic, standalone (future VCVio)
  Basic.lean               Spec.{u} (W-type), Transcript, Strategy, Decoration,
                           Decoration.map, BundledMonad, MonadDecoration,
                           append, comp — universe-polymorphic throughout
  TwoParty.lean            Role, RoleDecoration (= Decoration on Spec),
                           Strategy.withRoles, Counterpart, runWithRoles,
                           per-node monad variants (withRolesAndMonads,
                           Counterpart.withMonads, runWithRolesAndMonads)
  Multiparty.lean          PartyDecoration, PartyDecoration.toRoles (via
                           Decoration.map), ThreeParty examples
  Reduction.lean           Prover, Verifier, Reduction, Proof, execute

OracleReduction/         ← ArkLib-specific (oracle access layer)
  (TODO) OracleVerifier    Verifier that queries messages via OracleInterface
  (TODO) OracleReduction   OracleProver + OracleVerifier
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

## In progress

- [ ] **Phase 3: OracleVerifier + OracleReduction** — the only ArkLib-specific
  layer; needs `OracleInterface` (currently at `OracleReduction/OracleInterface.lean`)
  to express oracle queries on prover messages. This bridges the generic
  `Interaction` layer (monad `m`) with VCVio's `OracleComp oSpec`.

  Key question: how does `OracleInterface` attach to `Spec` + `RoleDecoration`?
  In the old core, `OracleInterface` is a typeclass on `Message` types, used
  to define `OracleVerifier` (verifier that queries prover messages as oracles).
  In the new core, the message types are the `Moves` at sender nodes. We need
  to either:
  - Decorate sender nodes with `OracleInterface` instances (another `Decoration`)
  - Pass `OracleInterface` instances structurally alongside the spec

- [ ] **Sequential composition** — `Strategy.comp`, `Counterpart.comp`, and
  `Reduction.comp` for role-aware specs (infrastructure in place on `Spec`,
  needs role-aware wrappers and `RoleDecoration.append`)

## Planned

- [ ] **Phase 4: Security definitions** — completeness, soundness, knowledge
  soundness, round-by-round state functions, composition theorems
- [ ] **Phase 5: Sumcheck migration** — express sumcheck in new types
- [ ] **Phase 6: Protocol migration** — FRI, Binius, Whir, Stir, Components,
  CommitmentScheme
- [ ] **Fiat-Shamir** — abstract FS transform on Spec + RoleDecoration
- [ ] **DuplexSponge FS** — concrete instantiation (deferred)
- [ ] **BCS transformation** — IOR + commitment → IR (deferred)

## Open questions / issues

- **OracleInterface integration**: The old `OracleInterface` is a typeclass
  `class OracleInterface (Message : Type) where Query : Type; ...`. In the new
  `Spec`-based world, how should oracle access be parameterized? Options:
  (a) A `Decoration` that assigns `OracleInterface` at each sender node;
  (b) A separate oracle spec parameter alongside the interaction spec;
  (c) Bake oracle access into the monad via `OracleComp`.

- **Composition types**: `Strategy.comp` exists on raw `Spec` but needs
  role-aware wrappers: `RoleDecoration.append` (concatenate role decorations)
  and `Strategy.withRoles` composition that preserves role structure.

- **Dependent vs non-dependent output**: `Prover` currently uses non-dependent
  output `(fun _ => StmtOut × WitOut)`. Dependent output is possible via
  raw `Strategy.withRoles` but no named wrapper exists.

- **Where Interaction goes long-term**: planned to move to VCVio once stable.
  Keep it import-free from ArkLib.

## Old core (to be replaced)

| Area | Files | Status |
|------|-------|--------|
| `OracleReduction/ProtocolSpec/` | 3 files | Replaced by `Interaction/Basic.lean` |
| `OracleReduction/Basic.lean` | 1 file | Replaced by `Interaction/Reduction.lean` |
| `OracleReduction/` (rest) | ~32 files | Untouched, will break |
| `ProofSystem/` | ~50 files | Untouched, will break |
| `CommitmentScheme/` | ~6 files | Untouched, will break |
| `OracleReduction/OracleInterface.lean` | 1 file | Stable, to be reused |

Breakage is expected and intentional. We fix downstream incrementally.
