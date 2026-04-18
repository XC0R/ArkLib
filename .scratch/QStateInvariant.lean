/-
Task B: Q-state invariant Pantograph goal extraction

This file captures goal states for the Q-state invariant lemma to guide proof construction.
-/

import ArkLib.OracleReduction.FiatShamir.Basic

open OracleComp OracleSpec ProtocolSpec FiatShamir

variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {pSpec : ProtocolSpec n}
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

-- Type abbreviation for the FS state
abbrev FSState (StmtIn : Type) (pSpec : ProtocolSpec n) (σ : Type) :=
  σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id

/-- The Q-state component is preserved by simulateQ with the FS implementation.
    This is the key invariant: running any OracleComp through the FS simulation
    with `defaultFSImpl` as the initial Q-state preserves that Q-state. -/
private lemma snd_snd_mem_support_simulateQ_addLift_fsChal
    {α : Type}
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α)
    (s : σ)
    (x : α × FSState StmtIn pSpec σ)
    (hx : x ∈ support ((simulateQ (impl.addLift fsChallengeQueryImpl')
      oa : StateT (FSState StmtIn pSpec σ) ProbComp α).run (s, defaultFSImpl))) :
    x.2.2 = defaultFSImpl := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    -- Goal after simp: should be trivial since pure doesn't change state
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    -- hx : x = (a, s, defaultFSImpl)
    simp [hx]
  | query_bind t ob ih =>
    -- This is the interesting case
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, support_bind,
      Set.mem_iUnion] at hx
    obtain ⟨mid, hmid, hcont⟩ := hx
    -- ih : ∀ (u : Range), ∀ (s : σ), ∀ x ∈ support(...), x.2.2 = defaultFSImpl
    -- We need mid.2.2 = defaultFSImpl, then apply ih to hcont
    cases t with
    | inl t_oSpec =>
      -- oSpec query: impl.liftTarget preserves τ-component
      simp only [QueryImpl.addLift] at hmid
      have hmid_snd_snd : mid.2.2 = defaultFSImpl := by
        simp only [QueryImpl.liftTarget_apply, support_map, Set.mem_image] at hmid
        obtain ⟨_, _, rfl⟩ := hmid
        rfl
      -- hcont has mid.2, need to rewrite to (mid.2.1, defaultFSImpl)
      have hcont' : x ∈ support ((simulateQ (impl.addLift fsChallengeQueryImpl')
          (ob mid.1)).run (mid.2.1, defaultFSImpl)) := by
        convert hcont using 2
        ext <;> [rfl; exact hmid_snd_snd.symm]
      exact ih mid.1 mid.2.1 x hcont'
    | inr t_fsChal =>
      -- fsChallengeOracle query: fsChallengeQueryImpl' returns (f query, f)
      simp only [QueryImpl.addLift] at hmid
      have hmid_snd_snd : mid.2.2 = defaultFSImpl := by
        -- hmid states mid is in support of (fsChallengeQueryImpl'.liftTarget t_fsChal).run (s, defaultFSImpl)
        -- fsChallengeQueryImpl' returns pure (f t_fsChal, f)
        -- After liftTarget.run (s, f): result is pure (f t_fsChal, (s, f))
        -- With f = defaultFSImpl, mid = (defaultFSImpl t_fsChal, (s, defaultFSImpl))
        -- So mid.2.2 = defaultFSImpl
        simp only [fsChallengeQueryImpl', support_map, support_pure, Set.mem_image,
          Set.mem_singleton_iff] at hmid
        obtain ⟨_, _, rfl⟩ := hmid
        rfl
      have hcont' : x ∈ support ((simulateQ (impl.addLift fsChallengeQueryImpl')
          (ob mid.1)).run (mid.2.1, defaultFSImpl)) := by
        convert hcont using 2
        ext <;> [rfl; exact hmid_snd_snd.symm]
      exact ih mid.1 mid.2.1 x hcont'

-- Test: check if the lemma compiles
#check @snd_snd_mem_support_simulateQ_addLift_fsChal
