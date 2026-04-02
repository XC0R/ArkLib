/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.TwoParty.Role
import ArkLib.Interaction.TwoParty.Decoration
import ArkLib.Interaction.TwoParty.Strategy

/-!
# N-Party Sequential Interactions

N-party interactions built on `Spec` + decorations. There is no separate
`Multiparty` inductive type. Instead, an N-party interaction is a `Spec`
paired with a *party decoration* — a `Spec.Decoration (fun _ => Party)` that
labels each node with its acting party.

For any participant `p`, a "resolve" function maps parties to roles:
- `p`'s nodes → `sender` (choose/act)
- Everyone else's nodes → `receiver` (observe/respond)

The projection from N-party to two-party is trivial:
`Decoration.map (fun _ => resolve) partyDeco`, producing a `RoleDecoration`.

All strategy/environment types are inherited from `Spec.Strategy.withRoles`
and `Spec.Counterpart` with zero duplication.

## Main definitions

- `PartyDecoration` — per-node party assignment on a `Spec`
- `PartyDecoration.toRoles` — project party labels to role labels
- `ThreeParty` — example three-party setting (prover, verifier, extractor)
- `ksSpec` / `ksPartyDeco` — knowledge-soundness interaction example
-/

namespace Interaction

/-- A party decoration assigns a party label to each internal node of an
interaction spec. N-party interactions are simply `Spec` + `PartyDecoration`. -/
abbrev PartyDecoration (Party : Type) := Spec.Decoration (fun _ => Party)

/-- Project a party decoration to a role decoration via a resolve function.
This is the analog of MPST local type projection. -/
abbrev PartyDecoration.toRoles {Party : Type} {spec : Spec}
    (resolve : Party → Role) (parties : PartyDecoration Party spec) :
    RoleDecoration spec :=
  Spec.Decoration.map (fun _ => resolve) spec parties

/-- Relabeling party labels then projecting to roles equals projecting after
`Decoration.map` (MPST-style relabeling commutes with local role projection). -/
@[simp]
theorem PartyDecoration.toRoles_comp {Party Party' : Type} {spec : Spec}
    (resolve : Party → Role) (f : Party' → Party) (parties : PartyDecoration Party' spec) :
    PartyDecoration.toRoles (resolve ∘ f) parties =
      PartyDecoration.toRoles resolve (Spec.Decoration.map (fun _ => f) spec parties) := by
  simpa [PartyDecoration.toRoles, Spec.Node.ContextHom.comp] using
    (Spec.Decoration.map_comp (g := fun _ => resolve) (f := fun _ => f) spec parties).symm

/-! ## Three-Party Knowledge Soundness Example

We cast knowledge soundness as a three-party sequential interaction to evaluate
whether this formulation improves on the standard two-party definition.

**Parties**:
- `prover` (P) — generates messages and output witness
- `verifier` (V) — sends challenges and decides accept/reject
- `extractor` (E) — observes the full interaction, outputs extracted witness

**Interaction structure** (for a 1-round protocol):
```
P sends message  →  V sends challenge  →  P outputs witness  →
V decides  →  E extracts  →  done
```

Each party's strategy is determined by their role resolver:
- P sees P-nodes as choices, V/E-nodes as observations
- V sees V-nodes as choices, P/E-nodes as observations
- E sees E-nodes as choices, P/V-nodes as observations
-/

inductive ThreeParty where
  | prover
  | verifier
  | extractor
  deriving DecidableEq

namespace ThreeParty

/-- Role resolver: `me` acts (sender), everyone else observes (receiver). -/
def resolveFor : ThreeParty → ThreeParty → Role
  | .prover, .prover => .sender
  | .prover, .verifier => .receiver
  | .prover, .extractor => .receiver
  | .verifier, .prover => .receiver
  | .verifier, .verifier => .sender
  | .verifier, .extractor => .receiver
  | .extractor, .prover => .receiver
  | .extractor, .verifier => .receiver
  | .extractor, .extractor => .sender

end ThreeParty

section KnowledgeSoundnessInteraction

variable (Msg Chal WitOut : Type)
variable (Decision : Type)
variable (ExtractedWit : Type)

/-- Spec for a one-round knowledge-soundness interaction: message, challenge,
witness output, decision, extraction. -/
private def ksSpec : Spec :=
  Spec.node Msg fun _ => .node Chal fun _ => .node WitOut fun _ =>
  .node Decision fun _ => .node ExtractedWit fun _ => .done

/-- Party labels for the knowledge-soundness interaction. -/
private def ksPartyDeco :
    PartyDecoration ThreeParty (ksSpec Msg Chal WitOut Decision ExtractedWit) :=
  ⟨.prover, fun _ => ⟨.verifier, fun _ => ⟨.prover, fun _ =>
    ⟨.verifier, fun _ => ⟨.extractor, fun _ => ⟨⟩⟩⟩⟩⟩⟩

/-! ### Strategy types for each party

The following examples show what the strategy types compute to for each party.
This makes the MPST projection concrete. -/

variable (m : Type → Type) [Monad m] (α : Type)

/-- **Prover** sees: choose msg, receive chal, choose witOut, receive decision,
receive extraction. -/
example : Spec.Strategy.withRoles m (ksSpec Msg Chal WitOut Decision ExtractedWit)
    ((ksPartyDeco Msg Chal WitOut Decision ExtractedWit).toRoles
      (ThreeParty.resolveFor .prover)) (fun _ => α)
    = m ((_ : Msg) × ((_ : Chal) → m (m ((_ : WitOut) ×
        ((_ : Decision) → m ((_ : ExtractedWit) → m α)))))) := rfl

/-- **Verifier** sees: receive msg, choose chal, receive witOut, choose decision,
receive extraction. -/
example : Spec.Strategy.withRoles m (ksSpec Msg Chal WitOut Decision ExtractedWit)
    ((ksPartyDeco Msg Chal WitOut Decision ExtractedWit).toRoles
      (ThreeParty.resolveFor .verifier)) (fun _ => α)
    = ((_ : Msg) → m (m ((_ : Chal) × ((_ : WitOut) → m
        (m ((_ : Decision) × ((_ : ExtractedWit) → m α))))))) := rfl

/-- **Extractor** sees: receive msg, receive chal, receive witOut, receive decision,
choose extraction. -/
example : Spec.Strategy.withRoles m (ksSpec Msg Chal WitOut Decision ExtractedWit)
    ((ksPartyDeco Msg Chal WitOut Decision ExtractedWit).toRoles
      (ThreeParty.resolveFor .extractor)) (fun _ => α)
    = ((_ : Msg) → m ((_ : Chal) → m ((_ : WitOut) → m
        ((_ : Decision) → m (m ((_ : ExtractedWit) × α)))))) := rfl

/-- **Prover's environment** (verifier + extractor combined): observe msg,
sample chal, observe witOut, sample decision, sample extraction. -/
example : Spec.Counterpart m (ksSpec Msg Chal WitOut Decision ExtractedWit)
    ((ksPartyDeco Msg Chal WitOut Decision ExtractedWit).toRoles
      (ThreeParty.resolveFor .prover)) (fun _ => α)
    = ((_ : Msg) → m ((_ : Chal) × ((_ : WitOut) → m
        ((_ : Decision) × m ((_ : ExtractedWit) × α))))) := rfl

end KnowledgeSoundnessInteraction

/-! ## Evaluation: Three-Party vs Current Formulation

### Current formulation (in `Security/Defs.lean`)

```
∃ extractor : StmtIn → WitOut → Transcript → OptionT (OracleComp oSpec) WitIn,
∀ stmtIn, ∀ prover,
  Pr[verifier_accepts ∧ extractor_fails | run protocol] ≤ ε
```

The verifier is a **function** applied after the protocol. The extractor is a
**function** applied to the transcript and output witness. Neither participates
interactively in the protocol itself.

### Three-party formulation

```
∃ extractorStrategy, ∀ proverStrategy,
  let verifierStrategy := mkVerifier stmtIn sampleChallenges
  Pr[badEvent | run ksInteraction proverStrategy verifierStrategy extractorStrategy] ≤ ε
```

All three parties are unified as "strategies" in the same sequential interaction.

### Verdict

**Straightline extraction**: REGRESSION. The current formulation is simpler —
the extractor is just a function of `(stmtIn, witOut, transcript)`. Modeling it
as an interactive move adds unnecessary structure, since the extractor
doesn't actually interact during the protocol.

**State-restoration extraction**: NEUTRAL to SLIGHT IMPROVEMENT. The SR
extractor *does* interact (it rewinds the prover and re-samples challenges).
The 3-party formulation could model this as additional rounds of interaction
between the extractor and a "rewinding oracle."

**Zero-knowledge simulation**: IMPROVEMENT. The simulator (a third party)
genuinely interacts with the verifier to produce a fake transcript. The 3-party
interaction naturally captures this as a strategy for the simulator party.

**General MPC**: SIGNIFICANT IMPROVEMENT. Multi-party computation with N>2
parties, each with their own role, maps directly to N-party interactions. The
projection to each party's local view is exactly MPST's local type projection.

### Conclusion

The 3-party formulation is *more general* but not uniformly better. For the
specific case of straightline knowledge soundness, the current function-based
formulation is cleaner. The N-party interaction framework shines when parties
genuinely interact (simulation, state-restoration, MPC).
-/

end Interaction
