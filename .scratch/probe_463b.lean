import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces

-- Check if there's a lemma connecting AffSpanSet and affineSubspaceAtOrigin
#check @Affine.AffSpanSet
#check @AffineSubspace.mk'
#check Affine.mem_affineSubspaceFrom_iff

-- Check what Fin.tail does
example (u : Fin 4 → Nat) : Fin.tail u = fun i => u i.succ := rfl
