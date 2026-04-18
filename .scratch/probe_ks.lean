import ArkLib
import Clean.Circuit.Foundations

-- Check what the KS goal looks like after unfolding
-- We need to understand the execution structure

open OracleComp OracleSpec ProtocolSpec Circuit Clean.Bridge

-- Check what Reduction.runWithLog unfolds to
#check @Reduction.runWithLog
#check @Extractor.Straightline
