import ArkLib.OracleReduction.FiatShamir.Basic

-- Test: can we ascribe h_deriveFS to a type with pSpec instead of pSpec.take?
-- Simulating the situation: a proof uses pSpec.take internally but we want pSpec
open ProtocolSpec in
example (n : Nat) (pSpec : ProtocolSpec n) (StmtIn : Type)
    [inst : ∀ (i : pSpec.ChallengeIdx), VCVCompatible (pSpec.Challenge i)]
    (h : @defaultFSImpl (Fin.val (Fin.last n))
      (pSpec.take (Fin.last n).val (by omega))
      StmtIn (vcvCompatible_take_challenge pSpec (Fin.last n))
    = @defaultFSImpl (Fin.val (Fin.last n))
      (pSpec.take (Fin.last n).val (by omega))
      StmtIn (vcvCompatible_take_challenge pSpec (Fin.last n))) :
    @defaultFSImpl n pSpec StmtIn inst = @defaultFSImpl n pSpec StmtIn inst := h

-- More relevant: can we convert an Eq proof from one type annotation to another?
open ProtocolSpec in
example (n : Nat) (pSpec : ProtocolSpec n) (StmtIn : Type) (α : Type)
    [inst : ∀ (i : pSpec.ChallengeIdx), VCVCompatible (pSpec.Challenge i)]
    (a b : α)
    (h : a = b) :
    a = b := h
-- This trivially works. The question is whether it works when α is a complex type
-- involving pSpec.take vs pSpec.
