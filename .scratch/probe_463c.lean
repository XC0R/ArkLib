import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces

-- Check if AffSpanSet equals affineSubspaceAtOrigin carrier
-- AffSpanSet U = (affineSpan F (univ.image U)).carrier
-- affineSubspaceAtOrigin (U 0) (Fin.tail U) = mk' (U 0) (span F (univ.image (Fin.tail U)))

-- These are the same when affineSpan F (range U) = mk' (U 0) (span F (range (Fin.tail U)))
-- which is exactly what vectorSpan_eq_span_vsub_set_right gives us

-- Check for prob_uniform equality lemmas
#check @PMF.uniformOfFintype
#check @prob_uniform_eq_card_filter_div_card
