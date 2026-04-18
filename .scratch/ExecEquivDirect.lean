import ArkLib.OracleReduction.FiatShamir.Basic

set_option maxHeartbeats 800000

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
  (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)

-- The NI protocol spec
abbrev niPSpec (pSpec : ProtocolSpec n) :=
  ⟨!v[Direction.P_to_V], !v[∀ i, pSpec.Message i]⟩

-- Try to provide instance manually
instance : ProverFirst (niPSpec pSpec) where
  prover_first' := rfl

instance : ProverOnly (niPSpec pSpec) where
  prover_first' := rfl
