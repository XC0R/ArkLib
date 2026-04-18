/-
Attempt: prove NeverFail + AllSucceed for FS by
decomposing the support of the FS computation.

Strategy: for any element in FS support, construct a corresponding
element in interactive-default support with the same projected values.
Then use hDefaultSubRandom to get into interactive-random support.
Then use hNoFail/hAllSucceed.

This works INSIDE the proof (not standalone) because:
- We can access `hDefaultSubRandom`
- The instances are already resolved by the `rw` calls
- We work with the goals as-is

Key lemma: runToRoundFS_default_state_eq (already proven)
gives PrvState equality. We need messages too.

Alternative: just show NeverFail directly by showing the computation
structure doesn't produce none.

Actually, the FS computation CAN produce none (if V.verify returns none).
So we need to relate it to the interactive computation.

MINIMUM VIABLE: Prove a single lemma that says:
∀ (s, q) in initial states, ∀ x in FS support,
  (proj x) is in (proj of interactive-default support)

where proj maps Option ((T × SO × WO) × SO') → Option ((SO × WO) × SO').

Since proj preserves none, this gives both NeverFail and AllSucceed.
-/

-- This file intentionally left as design notes.
-- The actual proof work will be in the main file.
-- Key insight: I need a NEW LEMMA that strengthens runToRoundFS_default_state_eq
-- to also track MessagesUpTo, then use it to establish transcript equality,
-- then compose through P.output and V.verify.
