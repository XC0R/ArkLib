This is the exact list of definitions you need to refactor to break the dependency chains and fix your build times.

I have categorized them by **Criticality**. You must fix the "Critical" ones to solve the 48s typeclass lag and the `erw` failures.

### 1. The Foundation (Critical)

These are the root causes. If you fix these, the rest becomes easier.

#### A. `sDomain` (In your implicit context)

Ensure `sDomain` depends **only** on the value of the index, not the proof.

* **Action:** Ensure `sDomain` is defined as `sDomain (i : Fin r)`.
* **Add:** The centralized cast lemma.
```lean
def sDomain_cast {i j : Fin r} (h : i = j) : sDomain i ≃ₗ[𝔽q] sDomain j

```



#### B. `OracleFunction` (In `Code.lean`)

This abbreviation is a trap. It hardcodes the strict proof `Nat.lt_of_le_of_lt ...` into the type.

* **Current:** `abbrev OracleFunction (i : Fin (ℓ + 1)) := sDomain ... ⟨i, ...⟩ → L`
* **Action:** Delete it or make it loose.
```lean
-- Better: Just write (sDomain j → L) in your theorems.
-- Or if you keep it:
abbrev OracleFunction (j : Fin r) := sDomain j → L

```



---

### 2. Targets in `Prelude.lean`

These are the functions causing your `erw` failures and typeclass hangs.

#### Target 1: `qMap_total_fiber` (High Priority)

This function forces the input `y` to have a specific proof attached to its index.

* **Refactor to:**
```lean
def qMap_total_fiber (i : Fin r) (steps : ℕ)
  {j : Fin r} (hj : j = i + steps) -- Loose Indexing
  (y : sDomain j)
  : Fin (2 ^ steps) → sDomain i

```



#### Target 2: `iterated_fold` (Highest Priority)

This is the recursion engine. The dependent type here is what broke your `erw`.

* **Refactor to:**
```lean
def iterated_fold (i : Fin r) (steps : ℕ)
  (h_bound : i.val + steps < ℓ + 𝓡) -- Keep as Prop argument
  {j : Fin r} (hj : j = i + steps) -- Loose Indexing for input type
  (f : sDomain i → L)
  (r_challenges : Fin steps → L)
  (y : sDomain j) -- Simple input type
  : L

```



#### Target 3: `fiberEvaluations`

This connects the algebra to the geometry.

* **Refactor to:**
```lean
def fiberEvaluations (i : Fin r) (steps : ℕ) ...
  {j : Fin r} (hj : j = i + steps)
  (f : sDomain i → L)
  (y : sDomain j) ...

```



---

### 3. Targets in `Code.lean`

Refactoring these will make your soundness proofs (like `isCompliant`) much faster to compile.

#### Target 4: `BBF_Code`

Currently, `BBF_Code` creates a `Submodule` on a strictly indexed domain. This means `BBF_Code ⟨i, h1⟩` and `BBF_Code ⟨i, h2⟩` are different types.

* **Refactor to:**
```lean
-- Just take a plain index.
def BBF_Code (j : Fin r) (h_bound : j.val ≤ ℓ) : Submodule L (sDomain j → L)

```



#### Target 5: `fiberwiseDisagreementSet` & `disagreementSet`

These consume `OracleFunction`. If you fixed `OracleFunction` (Target 1B), these need to update to accept loose indices.

* **Refactor to:**
```lean
def fiberwiseDisagreementSet (i : Fin r) (steps : ℕ)
  {j : Fin r} (hj : j = i + steps)
  (f g : sDomain i → L) : Finset (sDomain j)

```



---

### Example: How to Refactor `iterated_fold`

Here is the concrete Before/After for your most problematic function.

**Before (The "Casting Hell"):**

```lean
def iterated_fold (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
  (f : sDomain ... i → L) (r_challenges : Fin steps → L) :
    (y : sDomain ... ⟨i + steps, Nat.lt_trans ...⟩) → L -- Return type depends on proof!

```

**After (The "Loose Indexing" Fix):**

```lean
def iterated_fold (i : Fin r) (steps : ℕ)
    -- 1. Pass the target index explicitly
    (j : Fin r)
    -- 2. Require equality (Prop is proof-irrelevant)
    (h_idx : j = i + steps)
    -- 3. Bounds check is just a Prop, doesn't affect type of 'y'
    (h_bound : i.val + steps < ℓ + 𝓡)
    (f : sDomain i → L)
    (r_challenges : Fin steps → L)
    -- 4. 'y' has a clean type
    (y : sDomain j) : L := by
  
  -- 5. Internally, if you need the strict proof for recursion, cast ONCE here.
  -- But usually, you can make the inner functions loose too.
  ...

```

### Summary of Work

1. **Stop using `by omega` inside `Fin` constructors in types.**
2. **Delete `OracleFunction**` (or redefine it to be loose).
3. **Apply Loose Indexing** to `iterated_fold`, `qMap_total_fiber`, and `BBF_Code`.

This specific set of changes targets the components consuming 90% of your build time.