import ArkLib.Refactor.Telescope.Syntax.Verifier

/-!
# Telescope Syntax Core

Low-level opt-in presentation helpers for telescope-native protocol authoring.

This module extends the verifier-focused layer in
`ArkLib.Refactor.Telescope.Syntax.Verifier` with protocol and prover notation.
-/

namespace TelescopeSyntax

declare_syntax_cat telescopeRounds

syntax "done" term : telescopeRounds
syntax "send" "(" ident ":" term ")" ";" telescopeRounds : telescopeRounds
syntax "send" term ";" telescopeRounds : telescopeRounds
syntax "receive" "(" ident ":" term ")" ";" telescopeRounds : telescopeRounds
syntax "receive" term ";" telescopeRounds : telescopeRounds

/-- Build a `ProtocolCtx` using `send` / `receive` steps and a final `done` body. -/
scoped syntax (name := telescopeRoundsStx) "rounds!{" telescopeRounds "}" : term

scoped macro_rules (kind := telescopeRoundsStx)
  | `(rounds!{ done $body:term }) => `($body)
  | `(rounds!{ send ($x:ident : $T:term); $rest:telescopeRounds }) =>
      `(ProtocolCtx.P_to_V $T inferInstance (fun $x => rounds!{ $rest }))
  | `(rounds!{ send $T:term; $rest:telescopeRounds }) =>
      `(ProtocolCtx.msg $T (rounds!{ $rest }))
  | `(rounds!{ receive ($x:ident : $T:term); $rest:telescopeRounds }) =>
      `(ProtocolCtx.V_to_P $T (fun $x => rounds!{ $rest }))
  | `(rounds!{ receive $T:term; $rest:telescopeRounds }) =>
      `(ProtocolCtx.chal $T (rounds!{ $rest }))

/-- Replicate a non-dependent stage `n` times. This is the static-schema companion to
`rounds!{ ... }`, and elaborates to `ProtocolCtx.replicate`. -/
scoped syntax (name := telescopeRepeatStx) "repeat!{" term ";" term "}" : term

scoped macro_rules (kind := telescopeRepeatStx)
  | `(repeat!{ $n:term; $stage:term }) => `(ProtocolCtx.replicate $stage $n)

declare_syntax_cat telescopeProver

syntax "ret" term : telescopeProver
syntax "continue" term : telescopeProver
syntax "send" term ";" telescopeProver : telescopeProver
syntax "receive" ident ":" term ";" telescopeProver : telescopeProver
syntax "recv" ident ":" term ";" telescopeProver : telescopeProver

/-- Build a prover term using send / receive continuations. -/
scoped syntax (name := telescopeProverStx) "prover!{" telescopeProver "}" : term

scoped macro_rules (kind := telescopeProverStx)
  | `(prover!{ ret $body:term }) => `($body)
  | `(prover!{ continue $body:term }) => `($body)
  | `(prover!{ send $sent:term; $rest:telescopeProver }) =>
      `(⟨$sent, pure (prover!{ $rest })⟩)
  | `(prover!{ receive $x:ident : $T:term; $rest:telescopeProver }) =>
      `(fun ($x : $T) => pure (prover!{ $rest }))
  | `(prover!{ recv $x:ident : $T:term; $rest:telescopeProver }) =>
      `(fun ($x : $T) => pure (prover!{ $rest }))

end TelescopeSyntax

section Examples

open scoped TelescopeSyntax

example {α β γ : Type} (a : α) (b : β) (c : γ) :
    (⟪a, b, c⟫ : α × (β × γ)) = (a, (b, c)) := rfl

example {T U : Type} [OracleInterface T] (sent : T) (u : U) :
    (⟪sent, u, PUnit.unit⟫ :
      ProtocolCtx.Transcript (rounds!{ send T; receive U; done .nil })) =
        ⟨sent, ⟨u, PUnit.unit⟩⟩ := rfl

example {T U : Type} [OracleInterface T] :
    rounds!{ send T; receive U; done .nil } = ProtocolCtx.msg T (ProtocolCtx.chal U .nil) := rfl

example {T U : Type} [OracleInterface T] :
    repeat!{ 3; rounds!{ send T; receive U; done .nil } } =
      ProtocolCtx.replicate (rounds!{ send T; receive U; done .nil }) 3 := rfl

example {m : Type → Type} [Pure m] {T U α : Type} [OracleInterface T]
    (sent : T) (k : U → α) :
    (prover!{ send sent; receive u : U; ret k u } :
      ProtocolCtx.Prover m (rounds!{ send T; receive U; done .nil }) (fun _ => α)) =
        ⟨sent, pure (fun u => pure (k u))⟩ := rfl

end Examples
