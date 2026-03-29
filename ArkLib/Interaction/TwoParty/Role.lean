/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Sender / receiver roles

`Interaction.Role` marks which side of a two-party protocol acts at each node. `Action` and `Dual`
package the Σ/Π pattern for strategies vs. environments; `interact` runs one round.
-/

universe u

namespace Interaction

/-- Which side speaks at a protocol node: sender (proposes a move) or receiver (observes). -/
inductive Role where
  | sender
  | receiver

namespace Role

/-- Exchange sender and receiver (duality on the role type). -/
def swap : Role → Role
  | .sender => .receiver
  | .receiver => .sender

/-- Focal party's action type: sender chooses (Σ), receiver responds to any move (Π). -/
def Action (role : Role) (m : Type u → Type u) (X : Type u) (Cont : X → Type u) : Type u :=
  match role with
  | .sender => (x : X) × m (Cont x)
  | .receiver => (x : X) → m (Cont x)

/-- Environment / dual view: sender branch is observation (Π); receiver branch samples (Σ). -/
def Dual (role : Role) (m : Type u → Type u) (X : Type u) (Cont : X → Type u) : Type u :=
  match role with
  | .sender => (x : X) → Cont x
  | .receiver => m ((x : X) × Cont x)

/-- Run one round: pair an `Action` with the matching `Dual` and continue in `k`. -/
def interact {m : Type u → Type u} [Monad m] {X : Type u}
    {ACont DCont : X → Type u} {Result : Type u} :
    (role : Role) → role.Action m X ACont → role.Dual m X DCont →
    ((x : X) → ACont x → DCont x → m Result) → m Result
  | .sender, ⟨x, mCont⟩, dualFn, k => do
      let cont ← mCont
      k x cont (dualFn x)
  | .receiver, recvFn, mDual, k => do
      let ⟨x, dualCont⟩ ← mDual
      let cont ← recvFn x
      k x cont dualCont

end Role
end Interaction
