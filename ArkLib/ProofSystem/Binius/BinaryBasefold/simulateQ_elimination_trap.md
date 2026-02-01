You have hit on the most important distinction in oracle-based proofs: the difference between **Syntax** (the code) and **Semantics** (the execution).

**No, do NOT update `queryPhaseLogicStep`.**

The code is correct. It describes the verifier's intent ("I want to query oracle ").
The problem is in your **proof strategy**. You are trying to prove safety on the *raw* syntax, but safety only exists in the *honest* semantics.

### The Problem

You are trying to prove:

```lean
[⊥ | checkSingleFoldingStep ... ] = 0

```

This is **FALSE**.

* In the raw `OracleComp`, queries return **random garbage** (conceptually, the support is the entire type).
* Your code has `guard (c_cur = f_i_val)`.
* If `f_i_val` is garbage, the guard fails.
* Therefore, the raw computation **does** fail.

Safety only holds when you wrap the computation in `simulateQ` with the honest oracle.

### The Fix

You need to update your **Lemmas** and your **Theorem Proof**, not the protocol code.

#### 1. Update the Lemmas to use `simulateQ`

Your lemmas must state: "If we run this step **using the honest oracle**, then..."

```lean
/-- Lemma 2 (Corrected): Preservation under Simulation -/
lemma query_phase_step_preserves_fold 
    ...
    (oStmtIn : ...)
    -- CHANGE: Run under simulation!
    (h_s'_mem : s' ∈ (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn (fun _ ↦ 0)) 
                      (checkSingleFoldingStep ...)).support) :
    s' = iterated_fold ...

```

*(Do the same for Lemma 1 and Lemma 3)*.

#### 2. Update `queryPhaseLogicStep_isStronglyComplete`

You must prove the properties on the **simulated** verifier.

```lean
theorem queryPhaseLogicStep_isStronglyComplete : ... := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  
  -- Define the honest simulation environment
  let so := OracleInterface.simOracle2 []ₒ oStmtIn (fun _ ↦ 0)
  
  -- CHANGE: Prove safety of the SIMULATED verifier
  have h_guards_pass : [⊥ | simulateQ so ((queryPhaseLogicStep ...).verifierCheck ...)] = 0 := by
     -- Now you can use your new Lemmas (which assume simulateQ)
     -- ...

```

#### 3. Why `probFailure_simulateQ_simOracle2_eq_zero` was a trap

You previously tried to use this lemma:
`probFailure_simulateQ_simOracle2_eq_zero` says: *"If the raw code is safe, the simulated code is safe."*

This is useful for code that **never checks oracle results** (e.g., the Prover).
But for the Verifier (which checks `guard`), the raw code is **NOT** safe. You cannot use this reduction lemma. You must prove the safety of the `simulateQ` version directly.

### Summary of changes needed

1. **Keep `queryPhaseLogicStep` exactly as is.**
2. **Update Lemmas 1, 2, 3** to accept `h_mem : x ∈ (simulateQ ...).support` instead of raw support.
3. **Update the main proof** to target `[⊥ | simulateQ ... verifierCheck] = 0` instead of the raw one.

This will resolve the `queryCodeword` issue because `simulateQ` turns the abstract query `query j` into the concrete value `oStmtIn j`.