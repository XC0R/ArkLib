/-
  Scratch file to test tactics for the Fin.lastCases goal in _characterize.
  Goal: after Fin.snoc_last, show `default = ofMsgChal (castLE _ (Fin.last _))`
  in the V_to_P case.
-/
import ArkLib.OracleReduction.FiatShamir.Basic

-- Test: can we unfold ofMessagesChallenges and use hDir?
example (n : ℕ) (pSpec : ProtocolSpec n) (i : Fin n)
    [inst : ∀ j, VCVCompatible ((pSpec.take (i.val + 1) (by omega)).«Type» j)]
    (hDir : pSpec.dir i = .V_to_P)
    (messages : pSpec.MessagesUpTo (Fin.last n)) :
    (default : (pSpec.take (i.val + 1) (by omega)).«Type» (Fin.last i.val)) =
    Transcript.ofMessagesChallenges (k := Fin.last n) messages
      (fun (j : pSpec.ChallengeIdx) => (default : pSpec.Challenge j))
      (Fin.castLE (by simp [Fin.val_last]; omega) (Fin.last i.val)) := by
  simp [Transcript.ofMessagesChallenges, hDir]
