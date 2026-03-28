import ArkLib.Refactor.Telescope.Basic

/-!
# Telescope Verifier Syntax

Low-level verifier-focused presentation helpers for telescope-native authoring.

This module depends only on `Basic`, so core verifier files can share `verifier!`
and `⟪...⟫` without importing the prover-specific keyword layer.
-/

namespace TelescopeSyntax

/-- Right-associated nested pair notation. This is useful both for constructing
values and for destructuring transcripts in pattern matches. -/
scoped syntax (name := telescopeTuple) "⟪" withoutPosition(term,*) "⟫" : term

scoped macro_rules (kind := telescopeTuple)
  | `(⟪$x:term⟫) => `($x)
  | `(⟪$x:term, $y:term⟫) => `(⟨$x, $y⟩)
  | `(⟪$x:term, $y:term, $rest:term,*⟫) => `(⟨$x, ⟪$y, $rest,*⟫⟩)

/-- Build a plain or oracle verifier by abstracting the statement/input binders and a
single transcript pattern match. This keeps the verifier surface close to ordinary
`do`-notation while still making transcript destructuring concise. -/
scoped syntax (name := telescopeVerifierStx)
  "verifier!{" ident "," term " => " term "}" : term
scoped syntax (name := telescopeOracleVerifierStx)
  "verifier!{" ident "," ident "," term " => " term "}" : term

scoped macro_rules
  | `(verifier!{ $stmt:ident, $pat:term => $body:term }) =>
      `(fun $stmt tr => match tr with | $pat => $body)
  | `(verifier!{ $stmt:ident, $input:ident, $pat:term => $body:term }) =>
      `(fun $stmt $input tr => match tr with | $pat => $body)

end TelescopeSyntax

section Examples

open scoped TelescopeSyntax

example {α β γ : Type} (a : α) (b : β) (c : γ) :
    (⟪a, b, c⟫ : α × (β × γ)) = (a, (b, c)) := rfl

end Examples
