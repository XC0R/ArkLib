import ArkLib.OracleReduction.FiatShamir.Basic

-- Check what the two sorry goals look like in fiatShamir_perfectCompleteness
-- by extracting them via #check / set_option

-- The goals after `constructor` in fiatShamir_perfectCompleteness should be:
-- 1. Pr[⊥ | OptionT.mk (do ...)] = 0
-- 2. ∀ x ∈ support (do ...), event x

-- Let's look at what hNoFail / hAllSucceed / hDefaultSubRandomFull types are
-- to understand the relationship between FS and interactive computations.

#check @probFailure
#check @OracleComp.mem_support_bind_iff
