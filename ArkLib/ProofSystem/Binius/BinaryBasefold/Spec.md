```dataview
table file.mtime as "Last modified", file.ctime as "Created at" FROM [[]]
SORT file.name ASC
```
# 📝 Content

## Quick overview
### 📘 Background: FFT in Characteristic 2
- Classical Cooley-Tukey FFT achieves time complexity $\Theta(\ell \cdot 2^{\ell})$.
- In **additive (binary) fields**, it was unclear whether this complexity could be achieved.
  
### 🌟 Key Insight by Lin, Chung, and Han (LCH14)
- They **achieve Cooley-Tukey-like complexity** in characteristic 2.
- The key innovation is to **use a novel polynomial basis** instead of the monomial basis.

#### 🔁 Transform Input Interpretation
- Normally, input vector $(a_0, \dots, a_{2^\ell - 1})$ represents:
  $$
  P(X) = \sum_{j=0}^{2^\ell - 1} a_j X^j
  $$
- LCH14 instead interprets it as:
  $$
  P(X) = \sum_{j=0}^{2^\ell - 1} a_j X_j(X)
  $$
  where $X_j(X)$ is the **new basis polynomial of degree $j$**.

### 🧱 Construction of the New Basis
- The basis polynomials $X_j(X)$ are built using:
  - **Subspace vanishing polynomials** $\widehat{W}_i(X)$
  - Each $\widehat{W}_i(X)$ vanishes on a subspace $U_i \subset \mathbb{F}_{2^r}$
- These subspaces form a chain:
  $$
  U_0 \subset U_1 \subset \cdots \subset U_\ell
  $$

### 🔗 Application to Binary BaseFold (Additive NTT + FRI)

#### 🎯 Goal:
- Adapt the BaseFold polynomial commitment scheme to characteristic 2.
- Requires:
  - Replacing standard NTT with **additive NTT** (from LCH14)
  - Replacing prime-field FRI with **binary-field FRI**

#### 🧩 Binary FRI Setup:
- Involves a sequence of subspaces over $\mathbb{F}_{2^r}$:
  $$
  S^{(0)} \xrightarrow{q^{(0)}} S^{(1)} \xrightarrow{q^{(1)}} \cdots \xrightarrow{q^{(\ell-1)}} S^{(\ell)}
  $$
- Each map $q^{(i)}$ is a **degree-2 linear subspace polynomial**.
- There is **no canonical choice** of subspaces $S^{(i)}$ or maps $q^{(i)}$ in FRI—it depends on application.

### 🎛 BaseFold PCS Specifics
- BaseFold’s FRI is more than just a proximity test:
  - It acts as a **multilinear evaluator**.
- Important property:
  - A FRI execution starting from a **Reed-Solomon encoding** of $(a_0, \dots, a_{2^\ell - 1})$ reduces to:
    $$
    a_0 + a_1 r_0' + a_2 r_1' + a_3 r_0' r_1' + \cdots + a_{2^\ell - 1} r_0' \cdots r_{\ell - 1}'
    $$
  - This is a **multilinear polynomial evaluation** at point $(r_0', \dots, r_{\ell - 1}')$

## Difference between Binary Basefold vs Basefold

"Binary BaseFold" is the name the authors of the second paper (`Polylogarithmic Proofs...`) give to their **specific adaptation of the original BaseFold (ZCF'24) protocol to make it work for characteristic 2 (binary) fields** . The original BaseFold (from the first paper) was designed for fields of **odd characteristic** and "fails to work straightforwardly in characteristic 2". => The **core difference** lies in *how* they "flatten" the multilinear polynomial into a univariate polynomial and *which* FRI folding maps they use.

### The Core Problem: Why BaseFold Failed for Binary Fields

The original BaseFold's magic comes from a property of prime-field FRI:
1.  It "flattens" a multilinear polynomial $f(X_0, ..., X_{l-1})$ into a univariate polynomial $P(X)$ using the standard **monomial basis** (i.e., $a_0 + a_1X + a_2X^2 + ...$).
2.  It uses the standard prime-field FRI folding map, which is simple squaring: $X \mapsto X^2$.
3.  When this specific combination is used, the final constant $c$ produced by the FRI protocol magically turns out to be exactly the multilinear evaluation of $f$ at the challenge points $r_i$ .

This fails in characteristic 2 because the $X \mapsto X^2$ map is a field isomorphism, not a 2-to-1 folding map . Binary FRI *must* use different folding maps, called "linear subspace polynomials" $q^{(i)}(X)$. If you just pick *any* valid $q^{(i)}$ maps (as FRI allows) and combine them with the standard monomial basis, the magic breaks. The final constant $c$ will *not* equal the multilinear evaluation .

### The Solution: The "Binary BaseFold" Adaptation

The authors of the second paper (in Section 4) present a new pipeline that "recovers BaseFold PCS in characteristic 2".

This **Binary BaseFold** protocol required changing *both* the polynomial basis and the FRI folding maps to be compatible:

1.  **New Polynomial Basis:** Instead of the standard monomial basis, it "flattens" the multilinear polynomial $f$ into a univariate polynomial $P(X)$ using the **Lin, Chung, and Han (LCH) novel polynomial basis** ($X_j(X)$) .
2.  **New Encoding:** It uses the corresponding **LCH additive NTT** (an "additive FFT" for binary fields) to encode $P(X)$ and create the first FRI oracle.
3.  **New FRI Folding Maps:** It uses a set of *specially chosen* linear subspace polynomials $q^{(i)}(X)$ for the FRI folding. These maps are specifically constructed to be compatible with the LCH basis .

When this *entire* pipeline (LCH basis + LCH NTT + special $q^{(i)}$ maps) is used, the magic is restored. The final constant $c$ from the FRI protocol once again equals the correct multilinear evaluation of $f$ .

### Comparison: BaseFold vs. Binary BaseFold

| Feature              | **Original BaseFold (ZCF'24)**                                                                                      | **Binary BaseFold (This Paper)**                                                                                                     |
| :------------------- | :------------------------------------------------------------------------------------------------------------------ | :----------------------------------------------------------------------------------------------------------------------------------- |
| **Field Type**       | **Odd Characteristic** (e.g., prime fields).                                                                        | **Characteristic 2** (Binary fields).                                                                                                |
| **FRI Folding Map**  | Uses the simple $X \mapsto X^2$ map (in the prime-field setting).                                                   | Uses specially constructed **linear subspace polynomials** $q^{(i)}(X)$.                                                             |
| **Choice of Maps**   | The $X \mapsto X^2$ map is standard for prime-field FRI.                                                            | The $q^{(i)}$ maps are **specifically chosen** to "factor" the LCH subspace polynomials, recovering the evaluator property .         |
| **Polynomial Basis** | "Flattens" the multilinear polynomial to a univariate one using the **standard monomial basis** ($1, X, X^2, ...$). | "Flattens" the multilinear polynomial using the **Lin, Chung, and Han (LCH) novel polynomial basis** ($X_0(X), X_1(X), ...$) .       |
| **Encoding (NTT)**   | Uses a standard Reed-Solomon encoding (e.g., an FFT over a multiplicative subgroup) .                               | Uses the **Lin, Chung, and Han (LCH) additive NTT** over an $\mathbb{F}_2$-linear subspace.                                          |
| **Result**           | The final FRI constant equals the multilinear evaluation.                                                           | By *combining* the LCH basis, LCH NTT, and special $q^{(i)}$ maps, the final FRI constant *also* equals the multilinear evaluation . |
| **Optimizations**    | Does not support higher-arity folding (i.e., $\eta > 1$).                                                           | Introduces **"oracle-skipping"** (a multilinear folding style with arity $\vartheta > 1$) to significantly reduce proof sizes .      |
|                      |                                                                                                                     |                                                                                                                                      |
## Condensed version
# The Binary BaseFold Protocol

This file provides a complete formalization of the Binary BaseFold IOPCS.
It instantiates the abstract FRI framework with the domains and folding maps
derived from the Novel Polynomial Basis and proves its security properties.

### FRI
- [BBHR18a](https://drops.dagstuhl.de/storage/00lipics/lipics-vol107-icalp2018/LIPIcs.ICALP.2018.14/LIPIcs.ICALP.2018.14.pdf)
- For $L$ a binary field, and size and rate parameters $\ell$ and $\mathcal{R}$ fixed, FRI yields an IOP of proximity for the Reed-Solomon code $\mathrm{RS}_{L, S}\left[2^{\ell+\mathcal{R}}, 2^{\ell}\right]$; here, we require that $S \subset L$ be an affine, $\mathbb{F}_2$-linear subspace (of dimension $\ell+\mathcal{R}$, of course).
- FRI yields an IOP for the claim whereby some oracle $[f]$-i.e., representing a function $f: S \rightarrow L$-is close to a codeword $(P(x))_{x \in S}$ (here, $P(X) \in L[X]^{<2^{\ell}}$ represents a polynomial of degree less than $2^{\ell}$ )
- FRI's verifier complexity is polylogarithmic in $2^{\ell}$.
- We abbreviate $\rho:=2^{-\mathcal{R}}$, so that $\mathrm{RS}_{L, S}\left[2^{\ell+\mathcal{R}}, 2^{\ell}\right]$ is of rate $\rho$.
- Internally, FRI makes use of a folding constant $\eta$-which we fix to be 1 -as well as a fixed, global sequence of subspaces and maps of the form:
$$
S=S^{(0)} \xrightarrow{q^{(0)}} S^{(1)} \xrightarrow{q^{(1)}} S^{(2)} \xrightarrow{q^{(2)}} \cdots \xrightarrow{q^{(\ell-1)}} S^{(\ell)} .
$$
- Here, for each $i \in\{0, \ldots, \ell-1\}, q^{(i)}$ is a **subspace polynomial** of degree $2^\eta=2$, whose kernel, which is 1-dimensional, is moreover contained in $S^{(i)}$.
- By linear-algebraic considerations, we conclude that $S^{(i+1)}$ 's $\mathbb{F}_2$-dimension is 1 less than $S^{(i)}$ 's is; inductively, we conclude that each $S^{(i)}$ is of dimension $\ell+\mathcal{R}-i$. In particular, $S^{(\ell)}$ is of dimension $\mathcal{R}$.

## The $qᵢ$'s Fiber via Basis Transformation

Finding the fiber of the quotient map $qᵢ$—that is, solving $qᵢ(x) = y$ for $x$ given $y$—can be done highly efficiently without complex polynomial root-finding. The solution comes from understanding how the map acts on the coordinate representations of points in the subspaces $S^{⁽ⁱ⁾}$ and $S^{⁽ⁱ⁺¹⁾}$.

### 1. Key Algebraic Properties

The construction relies on a few crucial facts about the subspaces and maps involved:

  * **Basis of $S^{⁽ⁱ⁾}$:** The set $Bᵢ = { \hat{W}_i(\beta_i), \hat{W}_i(\beta_{i+1}), \dots, \hat{W}_i(\beta_{\ell+\mathcal{R}-1}) }$ is an `𝔽q`-basis for the subspace $S^{⁽ⁱ⁾}$.
  * **Normalization:** For any round `i`, the first basis vector is normalized to one: $\hat{W}_i(\beta_i) = 1$.
  * **Map Composition:** The maps are designed to compose perfectly: $q_i \circ \hat{W}_i = \hat{W}_{i+1}$.
  * **Annihilation & Isomorphism:** From the composition property, we get two results for how $qᵢ$ acts on the basis vectors of $S^{⁽ⁱ⁾}$:
    1.  **Annihilation:** $q_i(\hat{W}_i(\beta_i)) = \hat{W}_{i+1}(\beta_i) = 0$. The map sends the first basis vector to zero.
    2.  **Isomorphism:** $q_i(\hat{W}_i(\beta_j)) = \hat{W}_{i+1}(\beta_j)$ for all $j > i$. The map preserves the remaining basis vectors.

### 2. How $qᵢ$ Acts on Coordinates

Let's see what happens when we apply $qᵢ$ to an arbitrary point $x ∈ S^{⁽ⁱ⁾}$. We can express $x$ as a unique linear combination of its basis vectors:

$x = c_i \cdot \hat{W}_i(\beta_i) + \sum_{j=i+1}^{\ell+\mathcal{R}-1} c_j \cdot \hat{W}_i(\beta_j)$

Now, we apply the linear map $qᵢ$:

$y = q_i(x) = c_i \cdot q_i(\hat{W}_i(\beta_i)) + \sum_{j=i+1}^{\ell+\mathcal{R}-1} c_j \cdot q_i(\hat{W}_i(\beta_j))$

Using the annihilation and isomorphism properties from above, this simplifies beautifully:

$y = c_i \cdot (0) + \sum_{j=i+1}^{\ell+\mathcal{R}-1} c_j \cdot \hat{W}_{i+1}(\beta_j)$
- => **Note, this is because we have `normalizedWᵢ_eval_βᵢ`: $Ŵᵢ(βᵢ) = 1$ and `qMap_eval_𝔽q_eq_0`: $q⁽ⁱ⁾(algebraMap(c)) = 0$ where algebraMap maps $c$ from $\mathbb{F}_q$ to $S^{(i)}$**

$y = \sum_{j=i+1}^{\ell+\mathcal{R}-1} c_j \cdot \hat{W}_{i+1}(\beta_j)$

This result shows that the $qᵢ$ effectively **discards the first coordinate $cᵢ$** of $x$ and re-interprets the remaining coordinates $(c_{i+1}, \dots)$ in the new basis $B_{i+1}$ to form $y$.

### 3. Constructing the Fiber

To find the preimages of a given $y ∈ S^{⁽ⁱ⁺¹⁾}$, we simply reverse this process:

1.  **Decompose $y$:** First, find the unique coordinate vector of $y$ in the basis $B_{i+1}$.
    $y = \sum_{j=i+1}^{\ell+\mathcal{R}-1} d_j \cdot \hat{W}_{i+1}(\beta_j)$
    The coordinate vector is $(d_{i+1}, \dots, d_{\ell+\mathcal{R}-1})$.

2.  **Construct Preimages $x$:** For any preimage $x ∈ S^{⁽ⁱ⁾}$ of $y$, its coordinates $(c_i, c_{i+1}, \dots)$ must match $y$'s coordinates for $j > i$. So, $c_j = d_j$ for $j=i+1, \dots, \ell+\mathcal{R}-1$.

3.  **The Free Coefficient:** The first coordinate, $c_i$, is completely unconstrained by $y$ because its corresponding basis vector $\hat{W}_i(\beta_i)$ is annihilated by the map. Therefore, $c_i$ can be any element $k$ from the subfield $\mathbb{F}_q$.

This gives us one distinct preimage $x_k$ for each $k ∈ \mathbb{F}_q$:

$x_k = \underbrace{k \cdot \hat{W}_i(\beta_i)}_{\text{The free part}} + \underbrace{\sum_{j=i+1}^{\ell+\mathcal{R}-1} d_j \cdot \hat{W}_i(\beta_j)}_{\text{The part fixed by y}}$

The complete fiber is the set $\{ x_k | k \in \mathbb{F}_q \}$, which is a **coset** of the line $span_{\mathbb{F}_q}(\hat{W}_i(\beta_i))$ in $S^{⁽ⁱ⁾}$.
## Binary BaseFold

- **Definition 4.1.** For each $i \in \{0, \ldots, \ell\}$, we define the domain
    $S^{(i)} := \widehat{W}_{i}(\langle\beta_{0}, \ldots, \beta_{\ell+\mathcal{R}-1}\rangle)$.
    Moreover, for each $i \in \{0, \ldots, \ell-1\}$, we define
    $q^{(i)}(X) := \frac{W_{i}(\beta_{i})^{2}}{W_{i+1}(\beta_{i+1})} \cdot X \cdot (X+1)$.

- **Lemma 4.2.** For each $i \in \{0, \ldots, \ell-1\}$, we have the equality $q^{(i)} \circ \widehat{W}_{i} = \widehat{W}_{i+1}$ of polynomials.

- **Theorem 4.3.** For each $i \in \{0, \ldots, \ell-1\}$, $q^{(i)}(S^{(i)}) = S^{(i+1)}$.

- **Corollary 4.4.** For each $i \in \{0, \ldots, \ell\}$, $\widehat{W}_{i} = q^{(i-1)} \circ \cdots \circ q^{(0)}$ holds.
	- #notey: Actually those $\widehat{W}_{i}$ and $q^{(i)}$ can exists for $i \in {\ell, ..., \ell + R - 1}$

- **Corollary 4.5.** For each $i \in \{0, \ldots, \ell\}$, the set $(\widehat{W}_{i}(\beta_{i}), \ldots, \widehat{W}_{i}(\beta_{\ell+\mathcal{R}-1}))$ is an $\mathbb{F}_{2}$-basis of the space $S^{(i)}$.

- **Definition 4.6.** We fix an index $i \in \{0, \ldots, \ell-1\}$ and a map $f^{(i)}: S^{(i)} \rightarrow L$. For each $r \in L$, we define the map $fold(f^{(i)}, r): S^{(i+1)} \rightarrow L$ by setting, for each $y \in S^{(i+1)}$:
    $$
    \text{fold}(f^{(i)}, r): y \mapsto \begin{bmatrix} 1-r & r \end{bmatrix} \cdot \begin{bmatrix} x_1 & -x_0 \ -1 & 1 \end{bmatrix} \cdot \begin{bmatrix} f^{(i)}(x_0) \ f^{(i)}(x_1) \end{bmatrix}
    $$
    where we write $(x_0, x_1) := q^{(i)^{-1}}(\{y\})$ for the fiber of $q^{(i)}$ over $y \in S^{(i+1)}$.
	- **Expression**: $f^{(i+1)}(y) = fold(f^{(i)}, r) = f^{(i)}(x_0) * [ (1 - r) * x_1 - r ] + f^{(i)}(x_1) * [ r - (1 - r) * x_0]$

- **Definition 4.8.** We fix a positive folding factor $\vartheta$, an index $i \in \{0, \ldots, \ell-\vartheta\}$, and a map $f^{(i)}: S^{(i)} \rightarrow L$. For each tuple $(r_0, \ldots, r_{\vartheta-1}) \in L^{\vartheta}$, we abbreviate fold$(f^{(i)}, r_0, \ldots, r_{\vartheta-1}) := \text{fold}(\cdots \text{fold}(f^{(i)}, r_0), \cdots, r_{\vartheta-1})$.

- **Lemma 4.9.** For each positive folding factor $\vartheta$, each index $i \in \{0, \ldots, \ell-\vartheta\}$, and each $y \in S^{(i+\vartheta)}$, there is a $2^{\vartheta} \times 2^{\vartheta}$ invertible matrix $M_y$, which **depends only on $y \in S^{(i+\vartheta)}$ (actually depends on $\vartheta$ too)**, such that, for each function $f^{(i)}: S^{(i)} \rightarrow L$ and each tuple $(r_0, \ldots, r_{\vartheta-1}) \in L^{\vartheta}$ of folding challenges, we have the matrix identity:
    $$
    \text{fold}(f^{(i)}, r_0, \ldots, r_{\vartheta-1})(y) = \left[\bigotimes_{j=0}^{\vartheta-1}(1-r_j, r_j)\right] \cdot M_y \cdot \begin{bmatrix} f^{(i)}(x_0) \ \vdots \ f^{(i)}(x_{2^{\vartheta}-1}) \end{bmatrix},
    $$
    where the right-hand vector's values $(x_0, \ldots, x_{2^{\vartheta}-1})$ represent the fiber $(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)})^{-1}(\{y\}) \subset S^{(i)}$.
	- This cost $O(N^2 = (2^{\vartheta})^3)$ (since the left and right term has dimensions $1 \times N$ and $N \times 1$, whereas $M_y$ has dimension $N \times N$)
	- **Optimization**: The matrix $M_y$ isn't just some random $N x N$ matrix. It's built from $\vartheta$ recursive applications of a simple folding rule. This gives it a highly structured, sparse nature, very similar to the matrices used in the **Fast Fourier Transform (FFT)**. Because of this special "**butterfly**" structure, the **verifier doesn't need to perform a full, generic matrix-vector multiplication. It can use a highly optimized algorithm, similar to an FFT, to get the result**. This optimized calculation reduces the cost from $O((2^{\vartheta})^2)$ down to $O(\vartheta * 2^{\vartheta})$.

### **(Forward & Local) Fold matrix $M_y$**
- This specification consolidates the mathematical definition, recursive construction, and protocol role of the matrix $M_y$, derived from **Lemma 4.9** and the proof of **Theorem 4.16** in the Binary BaseFold paper.
#### 1. Overview
The matrix $M_y$ provides the linear algebraic characterization of the `fold` operation. While the protocol defines folding recursively point-wise, **$M_y$ unrolls this recursion into a single linear transformation**. It maps the evaluations of a function $f$ on a large fiber in $S^{(i)}$ to a basis where the **folding operation corresponds exactly to a tensor product of the verifier's challenges**.

**Symbol:** $M_y$
**Dimensions:** $2^\vartheta \times 2^\vartheta$ (where $\vartheta$ is the number of folding steps).
**Field:** $L$ (Binary Field).

#### 2. Mathematical Definition (Lemma 4.9)

For a fixed folding depth $\vartheta \ge 1$, a starting domain index $i$, and a target point $y \in S^{(i+\vartheta)}$, $M_y$ is the unique **(square)** $2^\vartheta \times 2^\vartheta$ matrix satisfying:
$$
\text{fold}(f^{(i)}, \vec{r})(y) = \left( \bigotimes_{j=0}^{\vartheta-1} [1-r_j, r_j] \right) \cdot M_y \cdot \begin{bmatrix} f^{(i)}(x_0) \\ \vdots \\ f^{(i)}(x_{2^\vartheta - 1}) \end{bmatrix}
$$

Where:
* $\vec{r} = (r_0, \dots, r_{\vartheta-1})$ are the folding challenges.
* $(x_0, \dots, x_{2^\vartheta - 1})$ is the **full fiber** $(q^{(i+\vartheta-1)} \circ \dots \circ q^{(i)})^{-1}(\{y\}) \subseteq S^{(i)}$.
* $\text{fold}(f^{(i)}, \vec{r})$ is a map $S^{(i+\vartheta)} \rightarrow L$, which represents the correct value of $f^{(i+\vartheta)}$

#### 3. Recursive Construction (in proof of Lemma 4.9)
The matrix is constructed recursively. Let $M(k, y)$ denote the matrix for $k$ steps ending at point $y$.
##### 3.1 Base Case ($k=0$)
For 0 steps of folding, the "fiber" is just the point itself.
$$M(0, y) = I_1 = [1]$$

##### 3.2 Recursive Step ($k \to k+1$)
To construct $M(k+1, y)$ where $y \in S^{(i+k+1)}$:

1.  **Fiber Decomposition:**
    Find the immediate pre-images (fiber) of $y$ in the previous domain $S^{(i+k)}$:
    $$\{z_0, z_1\} = (q^{(i+k)})^{-1}(\{y\})$$
    *Ordering Convention:* Sort so that $z_0$ corresponds to the '0' path and $z_1$ to the '1' path. In this specific construction, $z_1 - z_0 = 1$.

2.  **Recursive Sub-matrices:**
    Compute the matrices for the sub-problems:
    $$A = M(k, z_0) \quad \text{and} \quad B = M(k, z_1)$$
    (Both $A$ and $B$ are size $2^k \times 2^k$).
3.  **Block Diagonal Construction:**
    $$D = \begin{bmatrix} A & 0 \\ 0 & B \end{bmatrix}$$
4.  **Butterfly (Diag) Matrix ($B_y$):**
    Construct the mixing matrix using $z_0, z_1$ and the Identity matrix $I_{2^k}$:
    $$\mathcal{B}_y = \begin{bmatrix} z_1 \cdot I_{2^k} & -z_0 \cdot I_{2^k} \\ -I_{2^k} & I_{2^k} \end{bmatrix}$$

5.  **Final Composition:**
    $$M(k+1, y) = \mathcal{B}_y \cdot D = \begin{bmatrix} z_1 A & -z_0 B \\ -A & B \end{bmatrix}$$

**Note on Arithmetic:** Since we are in a binary field (Characteristic 2), subtraction is addition ($-1 = 1$). However, the definition usually maintains the negative signs for algebraic generality until applied to $\mathbb{F}_{2^k}$.
#### 4. Visual Representation
The structure of $M_y$ closely resembles the butterfly operations found in Fast Fourier Transforms (FFT), specifically the Additive NTT.

The matrix decomposes into layers. The right-most layers (in the multiplication chain) handle the fine-grained fibers (bottom of the recursion), while the left-most layers handle the coarse fibers (top of the recursion, closest to $y$).

#### 5. Formal Properties

##### 5.1 Invertibility (Crucial for Soundness)
**Theorem:** For any valid domain setup and any $y$, $M_y$ is **nonsingular** (invertible).

**Proof Sketch:**
The determinant of the block matrix in the recursive step depends on the determinant of the butterfly matrix $\mathcal{B}_y$.
Using the rule for block determinants (assuming commutativity of diagonal blocks or simply Schur complement):
$$\det(\mathcal{B}_y) \approx \det(z_1 I - (-z_0 I)(-I)^{-1}(-I)) = \det((z_1 - z_0)I)$$
Since $z_1$ and $z_0$ are the roots of $q(X) - y = 0$, and $q(X)$ is defined such that the roots differ by 1:
$$z_1 - z_0 = 1$$
Thus, the determinant is non-zero (it is 1), preserving invertibility up the recursion stack.

##### 5.2 Independence
$M_y$ depends **only** on:
1.  The topology of the vector space domains $S^{(i)}$.
2.  The specific point $y$.
3.  The field constants defining the maps $q^{(i)}$.

It does **not** depend on the function $f$ or the random challenges $r$.

#### 6. Implementation Spec (Pseudo-code)

```python
def get_fiber_points(y, domain_idx):
    """ Returns pair (z0, z1) such that q(z) = y """
    # Implementation depends on specific basis of S
    # In canonical basis, this is often just appending 0 or 1 to bits of y
    pass

def compute_My(y, current_depth, total_depth, domain_idx):
    """
    Recursive construction of My.
    y: current point in S^(domain_idx + current_depth)
    """
    # 1. Base Case
    if current_depth == 0:
        return Matrix([[1]])

    # 2. Get Fiber
    # We need fiber in the previous layer
    z0, z1 = get_fiber_points(y, domain_idx + current_depth - 1)

    # 3. Recursive Calls
    # Note: domain index stays same, depth decreases relative to bottom
    M_z0 = compute_My(z0, current_depth - 1, total_depth, domain_idx)
    M_z1 = compute_My(z1, current_depth - 1, total_depth, domain_idx)

    # 4. Construct Matrices
    n = 2**(current_depth - 1)
    I = Identity(n)

    # Butterfly Block
    # Top Row: [z1*I, -z0*I]
    # Bot Row: [-I,    I  ]
    Top = hstack(z1 * I, -z0 * I)
    Bot = hstack(-1 * I,  1 * I)
    Butterfly = vstack(Top, Bot)

    # Diagonal Block
    # [M_z0,  0  ]
    # [ 0,   M_z1]
    Diag = block_diag(M_z0, M_z1)

    # 5. Combine
    return Butterfly * Diag
```

---

#### 7. Role in Security Proofs

$M_y$ is the tool used to prove that a cheater cannot hide errors.

1.  **Bad Folding Events:** The Prover wins if they can find challenges $\vec{r}$ such that `fold(fake_f, r)` looks like a valid codeword even though `fake_f` was not.
2.  **The Equation:** The error term in the folded function at point $y$ is:
    $$E(y) = (\text{Tensor}(\vec{r})) \cdot M_y \cdot \vec{E}_{\text{fiber}}$$
3.  **The Logic:**
    * If the prover cheats, $\vec{E}_{\text{fiber}}$ is non-zero.
    * Since $M_y$ is invertible, $M_y \cdot \vec{E}_{\text{fiber}}$ is non-zero.
    * We are then asking: "What is the probability that a random vector $\text{Tensor}(\vec{r})$ is orthogonal to the non-zero fixed vector $(M_y \cdot \vec{E}_{\text{fiber}})$?"
    * By Schwartz-Zippel lemma, this probability is low (proportional to degree/field size).

Without $M_y$ being invertible, the vector $M_y \cdot \vec{E}_{\text{fiber}}$ could be zero even if the prover cheated, allowing them to pass the check with probability 1.

---
### **CONSTRUCTION 4.11 (Binary BaseFold IOPCS).**

---
We define $\Pi=($ Setup, Commit, $\mathcal{P}, \mathcal{V})$ as follows.
- params $\leftarrow \Pi$. Setup $\left(1^\lambda, \ell\right)$. On input $1^\lambda$ and $\ell$, choose a constant, positive rate parameter $\mathcal{R} \in \mathrm{N}$ and a binary field $L / \mathbb{F}_2$ whose degree $r$ (say) over $\mathbb{F}_2$ satisfies $r=\omega(\log \lambda)$ and $r \geq \ell+\mathcal{R}$. Initialize the vector oracle $\mathcal{F}_{\text {Vec }}^L$. Fix a folding factor $\vartheta \mid \ell$ and a repetition parameter $\gamma=\omega(\log \lambda)$. Fix an arbitrary $\mathrm{F}_2$-basis $\left(\beta_0, \ldots, \beta_{r-1}\right)$ of $L$. Write $\left(X_0(X), \ldots, X_{2^t-1}(X)\right)$ for the resulting novel $L$-basis of $L[X]^{<2^{\ell}}$, and fix the domains $S^{(0)}, \ldots, S^{(\ell)}$ and the polynomials $q^{(0)}, \ldots, q^{(\ell-1)}$ as in Subsection 4.1. Write $C^{(0)} \subset L^{2^{\ell+R}}$ for the Reed-Solomon code $\mathrm{RS}_{L, S}(0)\left[2^{\ell+R}, 2^{\ell}\right]$.
- $[f] \leftarrow$ II.Commit(params, $t$ ). On input $t\left(X_0, \ldots, X_{\ell-1}\right) \in L\left[X_0, \ldots, X_{\ell-1}\right]^{\leq 1}$, use $t$ 's Lagrange coefficients $(t(w))_{w \in B_{\ell}}$ as the coefficients, in the novel polynomial basis, of a univariate polynomial $P(X)=\sum_{w \in \mathcal{B}_l} t(w) \cdot X_{\{w\}}(X)$, say. Using Algorithm 2, compute the Reed-Solomon codeword $f: S^{(0)} \rightarrow L$ defined by $f: x \mapsto P(x)$. Submit (submit, $\ell+\mathcal{R}, f$ ) to the vector oracle $\mathcal{F}_{\text {Vec }}^L$. Upon receiving (receipt, $\ell+\mathcal{R}$, $[f]$ ) from $\mathcal{F}_{\text {Vec }}^L$, output the handle $[f]$.

We define ( $\mathcal{P}, \mathcal{V}$ ) as the following IOP, in which both parties have the common input $[f], s \in L$, and $\left(r_0, \ldots, r_{\ell-1}\right) \in L^{\ell}$, and $\mathcal{P}$ has the further input $t\left(X_0, \ldots, X_{\ell-1}\right) \in L\left[X_0, \ldots, X_{\ell-1}\right]^{\leq 1}$.
- $\mathcal{P}$ writes $h\left(X_0, \ldots, X_{\ell-1}\right):=t\left(X_0, \ldots, X_{\ell-1}\right)$ $\cdot$ $\widetilde{\text { eq }}\left(r_0, \ldots, r_{\ell-1}, X_0, \ldots, X_{\ell-1}\right)$.
- $\mathcal{P}$ and $\mathcal{V}$ both abbreviate $f^{(0)}:=f$ and $s_0:=s$, and execute the following loop:

>	for $i \in\{0, \ldots, \ell-1\}$ do
> > 	$\mathcal{P}$ sends $\mathcal{V}$ the polynomial $h_i(X):=\sum_{w \in \mathcal{B}_{\ell-i-1}} h\left(r_0^{\prime}, \ldots, r_{i-1}^{\prime}, X, w_0, \ldots, w_{\ell-i-2}\right)$.
> > 	$\mathcal{V}$ requires $s_i \stackrel{?}{=} h_i(0)+h_i(1)$. $\mathcal{V}$ samples $r_i^{\prime} \leftarrow L$, sets $s_{i+1}:=h_i\left(r_i^{\prime}\right)$, and sends $\mathcal{P} r_i^{\prime}$.
> > 	$\mathcal{P}$ defines $f^{(i+1)}: S^{(i+1)} \rightarrow L$ as the function fold$\left(f^{(i)}, r_i^{\prime}\right)$ of Definition 4.6.
> > 	If $i+1=\ell$ then $\mathcal{P}$ sends $c:=f^{(\ell)}(0, \ldots, 0)$ to $\mathcal{V}$ => note that 
> > 	else if $\vartheta \mid i+1$ then $\mathcal{P}$ submits (submit, $\ell+\mathcal{R}-i-1, f^{(i+1)}$ ) to the oracle $\mathcal{F}_{\mathrm{Vec}}^L$
- $\mathcal{V}$ requires $s_{\ell} \stackrel{?}{=} c \cdot \widetilde{\mathrm{eq}}\left(r_0, \ldots, r_{\ell-1}, r_0^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ => $c$ should be $t(r_0^{\prime}, \ldots, r_{\ell-1}^{\prime})$ and should be $f^{(\ell)}(0, \ldots, 0)$
- $\mathcal{V}$ executes the following querying procedure:
>	for $\gamma$ repetitions do
> > 	$\mathcal{V}$ samples $v \leftarrow \mathcal{B}_{\ell+R}$ randomly.
> > 	for $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$ (i.e., taking $\vartheta$-sized steps) do
> > > 	for each $u \in \mathcal{B}_ϑ, \mathcal{V}$ sends (query, $\left[f^{(i)}\right],\left(u_0, \ldots, u_{\vartheta-1}, v_{i+\vartheta}, \ldots, v_{\ell+R-1}\right)$ ) to the oracle.
> > > 	if $i>0$ then $\mathcal{V}$ requires $c_i \stackrel{?}{=} f^{(i)}\left(v_i, \ldots, v_{\ell+R-1}\right)$. #note: => RHS is purely from Merkle opening from prover's commitments
> > > 	$\mathcal{V}$ defines $c_{i+\vartheta}:=$ fold $\left(f^{(i)}, r_i^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\left(v_{i+\vartheta}, \ldots, v_{\ell+R-1}\right)$.
> > 	$\mathcal{V}$ requires $c_{\ell} \stackrel{?}{=} c$.
---

- **Optimization: witness per round**: The witness $w_i$ for the state at the beginning of round $i$ is a consistent pair $\left(H_i, P^{(i)}\right)$ :
	- $H_i(X_i,\ldots,X_{\ell - 1}):= h\left(r_0^{\prime}, \ldots, r_{i-1}^{\prime}, X_i, X_{i+1}, \ldots, X_{\ell - 1}\right)$: an $(\ell-i)$-variate multilinear polynomial over $L$, representing the remaining sumcheck claim.
		- => Then $h_i(X) = \sum_{w \in \mathcal{B}_{\ell-i-1}} h\left(r_0^{\prime}, \ldots, r_{i-1}^{\prime}, X, w_0, \ldots, w_{\ell-i-2}\right) = \sum_{w \in \mathcal{B}_{\ell-i-1}} H\left(X, w_0, \ldots, w_{\ell-i-2}\right)$.
	- $P^{(i)}(X)$ : A univariate polynomial in $L[X]^{<2^{\ell-i}}$, representing the closest codeword for the FRI protocol.
	- **Sumcheck-fold Consistency Invariant**: Only happens at the final V check

In our commitment procedure above, we give meaning to the commitment of $f$ by implicitly identifying $S^{(0)} \cong \mathcal{B}_{\ell+\mathbb{R}}$ as sets (as discussed above); similarly, in the prover's line 6 above, we identify $\mathcal{B}_{\ell+\mathbb{R}-i-1} \cong$ $S^{(i)}$. Conversely, in its lines 4 and 6 above, the verifier must implicitly identify the $\mathcal{B}_{\ell+R-i}$-elements $\left(u_0, \ldots, u_{\vartheta-1}, v_{i+\vartheta}, \ldots, v_{\ell+R-1}\right)_{u \in \mathcal{B}_{\ell}}$ with $S^{(i)}$-elements-and the $\mathcal{B}_{\ell+R-i-\vartheta}$-element $\left(v_{i+\vartheta}, \ldots, v_{\ell+R-1}\right)$ with an $S^{(i+i)}$-element-in order to appropriately apply Definition 4.8. We note that, in line $6, \mathcal{V}$ has precisely the information it needs to compute fold $\left(f^{(i)}, r_i^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ **(namely, the values of $f^{(i)}$ on the fiber $\left.\left(u_0, \ldots, u_{\vartheta-1}, v_{i+\vartheta}, \ldots, v_{\ell+R-1}\right)_{u \in \mathcal{B}_0} \cong\left(q^{(i+\vartheta-1)} \circ \ldots \circ q^{(i)}\right)^{-1}\left(\left\{\left(v_{i+\vartheta}, \ldots, v_{\ell+R-1}\right)\right\}\right)\right)$**.

- **Theorem 4.12.** The IOPCS $\Pi = (\text{Setup, Commit}, \mathcal{P}, \mathcal{V})$ of Construction 4.11 is complete.
    * **Main Idea of Proof:** Assuming an honest prover, the sumcheck part will pass. The core is to show $c = t(r_0', \ldots, r_{\ell-1}')$. This is achieved by introducing $i^{\text{th}}$-order (higher order) novel polynomial bases and using Lemma 4.13 inductively to track the coefficients of the polynomial $P^{(i)}(X)$ (whose evaluations are $f^{(i)}$) through the folding process. The final polynomial $P^{(\ell)}(X)$ becomes the constant $t(r_0', \ldots, r_{\ell-1}')$.

- **Lemma 4.13 (Fold advances intermediate evaluation poly).** Fix an index $i \in \{0, \ldots, \ell-1\}$. If $f^{(i)}: S^{(i)} \rightarrow L$ is exactly the evaluation over $S^{(i)}$ of the polynomial $P^{(i)}(X) = \sum_{j=0}^{2^{\ell-i}-1} a_j \cdot X_j^{(i)}(X)$, then, under honest prover behavior, $f^{(i+1)}: S^{(i+1)} \rightarrow L$ is exactly the evaluation over $S^{(i+1)}$ of the polynomial $P^{(i+1)}(X) = \sum_{j=0}^{2^{\ell-i-1}-1} ((1-r_i') \cdot a_{2j} + r_i' \cdot a_{2j+1}) \cdot X_j^{(i+1)}(X)$.
  - **Main Idea of Proof:** Uses a key polynomial identity $P^{(i)}(X) = P_0^{(i+1)}(q^{(i)}(X)) + X \cdot P_1^{(i+1)}(q^{(i)}(X))$ (**Equation 39**), where $P_0^{(i+1)}$ and $P_1^{(i+1)}$ are even and odd refinements. By unwinding Definition 4.6 for $f^{(i+1)}(y)$ and substituting the evaluations of $P^{(i)}(x_0)$ and $P^{(i)}(x_1)$ (where $(x_0,x_1)$ is the fiber over $y$), the expression simplifies to $P^{(i+1)}(y)$ due to matrix properties and $x_1 - x_0 = 1$.
	  - **Note on the final sum-check step**: At the end of all iterations (before prover sending the final constant $c$, we have $P^{(\ell)} =\sum_{w \in \mathcal{B}_{\ell - \ell = 0}} H_{\ell}(w) \cdot X_{\{w\}}^{(\ell)}(X) = H_{\ell}(0) \cdot X_{\{0\}}^{(\ell)}(X) = H_{\ell}(0)$ is a **constant polynomial** (since $H_{\ell}(X)$ is a constant polynomial) (due to **Sumcheck-fold Consistency Invariant** above) => $P^{(\ell)}(X) = c = f^{(\ell)}(0,..,0), \forall X$ (final constant)
  - Inductive consequence: **$f^{(\ell)}$ will equal the evaluation over $S^{(\ell)}$ of the constant polynomial $\sum_{w \in \mathcal{B}_{\ell}} \widetilde{\mathrm{eq}}\left(w_{0}, \ldots, w_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot t(w)=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$** => MLE evaluation

---
  - **Proof**: 

- We need to prove: if $f^{(i)}(x_0) = P^{(i)}(x_0)$ and $f^{(i)}(x_1) = P^{(i)}(x_1)$, then $f^{(i+1)}(y) = P^{(i+1)}(y)$
- 0. ${x_0, x_1} = qMap\_fiber(y)$, where $x_1 - x_0 = 1$, note that we already assume L is a binary field
- 1. $P^{(i)}(X) = P_0^{(i+1)}(q^{(i)}(X)) + X \cdot P_1^{(i+1)}(q^{(i)}(X))$ (**Equation 39**), where $P_0^{(i+1)}$ and $P_1^{(i+1)}$ are even and odd refinements.
	- 1.1. $P^{(i)}(x_0) = P_0^{(i+1)}(q^{(i)}(x_0)) + x_0 \cdot P_1^{(i+1)}(q^{(i)}(x_0)) = P_0^{(i+1)}(y) + x_0 \cdot P_1^{(i+1)}(y)$
	- 1.2. $P^{(i)}(x_1) = P_0^{(i+1)}(q^{(i)}(x_1)) + x_1 \cdot P_1^{(i+1)}(q^{(i)}(x_1)) = P_0^{(i+1)}(y) + x_1 \cdot P_1^{(i+1)}(y)$
- 2. We need to prove: if $f^{(i)}(x_0) = P^{(i)}(x_0)$ and $f^{(i)}(x_1) = P^{(i)}(x_1)$, then $f^{(i+1)}(y) = P^{(i+1)}(y)$
- 3. Since $f^{(i+1)}(y) = fold(f^{(i)}, r) = f^{(i)}(x_0) * [ (1 - r) * x_1 - r ] + f^{(i)}(x_1) * [ r - (1 - r) * x_0]$
- => we replace those $f^{(i)}(x_0)$ and $f^{(i)}(x_1)$ with $P^{(i)}(x_0)$ and $P^{(i)}(x_1)$
	=> $f^{(i+1)}(y) = P^{(i)}(x_0) * [ (1 - r) * x_1 - r ] + P^{(i)}(x_1) * [ r - (1 - r) * x_0]$
	Now apply (1.1) and (1.2)
	=> $f^{(i+1)}(y) = [P_0^{(i+1)}(y) + x_0 \cdot P_1^{(i+1)}(y)] * [ (1 - r) * x_1 - r ] + [P_0^{(i+1)}(y) + x_1 \cdot P_1^{(i+1)}(y)] * [ r - (1 - r) * x_0]$
	Let $V_0 = P_0^{(i+1)}(y)$ and $V_1 = P_1^{(i+1)}(y)$
	=> $f^{(i+1)}(y) = (V_0 + x_0 \cdot V_1) * [(1 - r) * x_1 - r] + (V_0 + x_1 \cdot V_1) * [r - (1 - r) * x_0]$
	= $V_0 * [(1 - r) * x1 - r + r - (1 - r) * x_0] + V_1 * [x_0 * (1 - r) * x_1 - x_0 * r + x1 * r - x1 * (1 - r) * x_0]$
	= $V_0 * [(1 - r) * (x_0 + 1) - (1 - r) * x_0] + V_1 * [(x_1 - x_0) * r]$
	= $V_0 * (1 - r) + V_1 * r$
	Now unfold definitions of even and odd refinements:
	= $P_0^{(i+1)}(y) * (1 - r) + P_1^{(i+1)}(y) * r$
	= $\sum_{j=0}^{2^{ℓ-i-1}-1} a_{2j} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y) * (1 - r) + \sum_{j=0}^{2^{ℓ-i-1}-1} a_{2j+1} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y) * r$
	= $\sum_{j=0}^{2^{ℓ-i-1}-1} (a_{2j} * (1 - r) + a_{2j+1} * r) ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)$
	This is exactly $P_{coeffs}^{(i+1)}(y)$ where $coeffs = {a_{2j} * (1 - r) + a_{2j+1} * r | j = 0, ..., 2^{ℓ-i-1}-1}$ (**Q.E.D**)

---
- **CoreInteractionPhase sumcheck-kernel parameterization**: **we can treat the eq() part as a black-box MLP: $m\left(X_0, \ldots, X_{\ell-1}\right) \in L\left[X_0, \ldots, X_{\ell-1}\right]^{\leq 1}$, where in Binary Basefold, $m = \widetilde{\text { eq }}\left(r_0, \ldots, r_{\ell-1}, X_0, \ldots, X_{\ell-1}\right)$
	- $\mathcal{P}$ writes $H_0\left(X_0, \ldots, X_{\ell-1}\right):=t\left(X_0, \ldots, X_{\ell-1}\right)$ $\cdot$ $m\left(X_0, \ldots, X_{\ell-1}\right)$.
	- $\mathcal{P}$ and $\mathcal{V}$ both abbreviate $f^{(0)}:=f$ and $s_0:=s$, and execute the following loop:
		- for $i \in\{0, \ldots, \ell-1\}$ do
			- $\mathcal{P}$ sends $\mathcal{V}$ the polynomial $h_i(X):=\sum_{w \in \mathcal{B}_{\ell-i-1}} h\left(r_0^{\prime}, \ldots, r_{i-1}^{\prime}, X, w_0, \ldots, w_{\ell-i-2}\right)$.
			- $\mathcal{V}$ requires $s_i \stackrel{?}{=} h_i(0)+h_i(1)$. $\mathcal{V}$ samples $r_i^{\prime} \leftarrow L$, sets $s_{i+1}:=h_i\left(r_i^{\prime}\right)$, and sends $\mathcal{P} r_i^{\prime}$.
			- $\mathcal{P}$ defines $f^{(i+1)}: S^{(i+1)} \rightarrow L$ as the function fold$\left(f^{(i)}, r_i^{\prime}\right)$ of Definition 4.6.
			- If $i+1=\ell$ then $\mathcal{P}$ sends $c:=f^{(\ell)}(0, \ldots, 0)$ to $\mathcal{V}$ => note that 
			- else if $\vartheta \mid i+1$ then $\mathcal{P}$ submits (submit, $\ell+\mathcal{R}-i-1, f^{(i+1)}$ ) to the oracle $\mathcal{F}_{\mathrm{Vec}}^L$
	- $\mathcal{V}$ requires $s_{\ell} \stackrel{?}{=} c \cdot m\left(r_0^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ => $c$ should be $t(r_0^{\prime}, \ldots, r_{\ell-1}^{\prime})$ and should be $f^{(\ell)}(0, \ldots, 0)$
	- **Security analysis**:
		- Witness per state $i \in \{0, ..., \ell\}$: $(t, H_i(X_{i}, \ldots, X_{\ell - 1})) \in (L\left[X_0, \ldots, X_{\ell-1}\right]^{\leq 1}, L\left[X_0, \ldots, X_{\ell-i - 1}\right]^{\leq 1})$ 
		- Sum-check round relations:
			- Witness structural constraint: $H_i(X_i, \ldots, X_{\ell-1}) = \sum_{(x_0, \ldots, x_{i - 1}) \in \mathcal{B}_{i}} h\left(x_0, \ldots, x_{i-1}, X_i, \ldots, X_{\ell - 1}\right)$ where $h = H_0 = t \cdot m$ by definition
			- Sum-check: $\sum_{(x_i, \ldots, x_{\ell - 1}) \in \mathcal{B}_{\ell-i}} H_i\left(x_i, \ldots, x_{\ell - 1}\right) = \sum_{(x_i, \ldots, x_{\ell - 1}) \in \mathcal{B}_{\ell-i}} h\left(r_0^{\prime}, \ldots, r_{i-1}^{\prime}, x_i, \ldots, x_{\ell - 1}\right) = s_i$

---

- **Theorem 4.16.** The IOPCS $\Pi = (\text{Setup, Commit}, \mathcal{P}, \mathcal{V})$ of Construction 4.11 is secure (see Definition 2.8).
    * **Main Idea of Proof:** An emulator $\mathcal{E}$ is defined to extract $t$ using Berlekamp-Welch.
	    * The proof relies on showing that **if any of the adversary $\mathcal{A}$'s oracles $f^{(i)}$ is not "compliant" (Definition 4.17), then the verifier $\mathcal{V}$ accepts with negligible probability (Proposition 4.23, which itself depends on Propositions 4.20, 4.22 and Lemmas 4.18, 4.24, 4.25)**.
	    * **If all oracles are compliant, then the committed function $f^{(0)}$ is close to a codeword ($d(f^{(0)}, C^{(0)}) < \frac{d_0}{2}$), $\mathcal{E}$ extracts the correct polynomial $t$, and $c = t(r_0', \ldots, r_{\ell-1}')$. Sumcheck soundness ensures that if $s \neq t(r_0, \ldots, r_{\ell-1})$, $\mathcal{V}$ accepts with negligible probability.

- **Preliminary definitions**:
	- **Fiber** (p. 32): for each $y \in S^{(i+1)}$, the fiber set of $y$ is $q^{(i)^{-1}}(\{y\}) \subset S^{(i)}$, i.e. the set of elements $x \in S^{(i)}$ that maps to $y$ via the map $q^{(i)}(x): S^{(i)} \rightarrow S^{(i+1)}$. The fiber set can be composed across various rounds, e.g. from round $i+\vartheta$ back to round $i$, which is adopted in the definition of **Fiber-wise distance** below.
	- **Fold()**: The folding operation is a linear combination of the values on a fiber. Folding don't introduce new errors compared to the fiber-wise disagreement (**Lemma 4.18**).
	- **Code $C^{(i)}$ (p. 39)**: For each $i \in \{0, \vartheta, \ldots, \ell\}$, $C(i)$ is the Reed-Solomon code $RS_{L, S^{(i)}}[2^{\ell+R-i}, 2^{\ell-i}]$.
	- **Code (Minimum) Distance $d_i$** notation (p. 39): The distance of the code $C(i)$ is defined as $d_i := 2^{\ell+R-i} - 2^{\ell-i} + 1$.
	- **(Minimum) Distance to code**: $d(f^{(i)}, C^{(i)})$
	- **Oracle Functions $f^{(i)}$**: $f⁽ⁱ⁾: S⁽ⁱ⁾ → L$, where $|S^{(i)}| = 2^{l + R - i}$. These functions are expected to be codewords of $C^{(i)}$
		- $f^{(0)}, f^{(\vartheta)}, \ldots, f^{(\ell-\vartheta)}$ are the oracles committed by the adversary, $\mathcal{A}$.
		- $f^{(\ell)}$ is a function that is **identically equal to the constant $c$**, where $c$ is the adversary's final message. (This is defined concisely in **Theorem 4.16 - Completeness**)
	- **Disagreement Set $\Delta$**: The set of points $y \in S^{(i)}$ where two functions disagree, i.e., $f^{(i)}(y) \neq g^{(i)}(y)$.
		- **disagreementSet**: $\Delta(f^{(i)}, \bar{f}^{(i)}))$: Disagreement set of two functions
		- **foldedDisagreementSet**: $\Delta(\text{fold}(f^{(i)}, r_i', \ldots, r_{i+\vartheta-1}'), \text{fold}(\bar{f}^{(i)}, r_i', \ldots, r_{i+\vartheta-1}'))$: Disagreement set of two folded functions**
	- **Fiber-wise Disagreement Set $\Delta^{(i)}$**/$\Delta^{(i)}(f^{(i)}, g^{(i)})$: The set of **quotient points** $y \in S^{(i+\vartheta)}$ for which the functions $f^{(i)}$ and $g^{(i)}$ are **not identical** when restricted to the entire fiber of points in $S^{(i)}$ that maps to $y$.
	- **Fiber-wise Distance $d^{(i)}$**: The minimum size of the fiber-wise disagreement set between $f^{(i)}$ and any codeword in $C^{(i)}$, defined as $d^{(i)}(f^{(i)}, C^{(i)}) := \min_{g^{(i)} \in C^{(i)}} \Delta^{(i)}(f^{(i)}, g^{(i)})$. 
	- **Unique Closest Codeword $\bar{f}^{(i)}$**: If a function $f^{(i)}$ is within the unique decoding radius of the code $C^{(i)}$ (i.e., $d(f^{(i)}, C^{(i)}) < \frac{d_i}{2}$), then $\bar{f}^{(i)}$ denotes the unique codeword for which this condition holds.

- **Definition 4.17.** For each index $i \in \{0, \vartheta, \ldots, \ell-\vartheta\}$, we say that $\mathcal{A}$'s $i^{\text{th}}$ oracle $f^{(i)}$ is **compliant** if the conditions $d^{(i)}(f^{(i)}, C^{(i)}) < \frac{d_{i+\vartheta}}{2}$, $d(f^{(i+\vartheta)}, C^{(i+\vartheta)}) < \frac{d_{i+\vartheta}}{2}$, and $\bar{f}^{(i+\vartheta)} = \text{fold}(\bar{f}^{(i)}, r_i', \ldots, r_{i+\vartheta-1}')$ all hold.
	- $d^{(i)}(f^{(i)}, C^{(i)})$: the minimum **fiber-wise (backward) distance** between $f^{(i)}$ and a valid codeword $g \in C^{(i)}$
	- Supporting lemma: **UDRClose_of_fiberwiseClose**: if $d^{(i)}(f^{(i)}, C^{(i)}) < \frac{d_{i+\vartheta}}{2}$ (fiberwise close), then $d(f^{(i)}, C^{(i)}) < \frac{d_i}{2}$ (UDR close)

- **Lemma 4.27 (self-made): Proposition farness-implies-non-compliance (fiber-wise close implies compliance)**: if $d^{(i)}\left(f^{(i)}, C^{(i)}\right)<$ $\frac{d_{i+\vartheta}}{2}$ (fiber-wise distance), then $d\left(f^{(i)}, C^{(i)}\right)<\frac{d_{i}}{2}$ (Hamming distance) a fortiori holds (via **UDRClose_of_fiberwiseClose**, mentioned in Theorem 4.16) => use contrapositive of this, we have: **if $d\left(f^{(i)}, C^{(i)}\right) \ge \frac{d_{i}}{2}$ then  $d^{(i)}\left(f^{(i)}, C^{(i)}\right)\ge$ $\frac{d_{i+\vartheta}}{2}$, which means $f^{(i)}$ can be never compliant**
	- **Idea**: Each offending fiber contributes at most $2^ϑ$ errors; on the other hand, $2^{\vartheta} \cdot\left\lfloor\frac{d_{i+\vartheta}-1}{2}\right\rfloor \leq\left\lfloor\frac{d_{i}-1}{2}\right\rfloor$.
---
#### Proof
0. Assuming $d^{(i)}(f^{(i)}, C^{(i)}) < \frac{d_{i+\vartheta}}{2}$, we need to prove that $d\left(f^{(i)}, C^{(i)}\right)<\frac{d_{i}}{2}$. A **fiber tuple** is a pair of a quotient point $y$ and its fiber (set) $(q^{(i + \vartheta - 1)} ∘ ⋯ ∘ q^{(i)})^{-1}({y}) ⊂ S^{(i)}$
1.  **Relating Distances via Fibers.**
    * Let $d_{\text{fw}} = d^{(i)}(f^{(i)}, C^{(i)})$ and $d_{\text{H}} = d(f^{(i)}, C^{(i)})$.
    * By definition, there is a codeword $g' \in C^{(i)}$ that minimizes the fiber-wise distance. Let $Y_{\text{bad}} = \Delta^{(i)}(f^{(i)}, g')$ be this minimal **fiber-wise disagreement set**.
    * This set $Y_{\text{bad}}$ consists of **quotient points** $y \in S^{(i+\vartheta)}$. The size of this set is $|Y_{\text{bad}}| = d_{\text{fw}}$.
    * For any quotient point $y \notin Y_{\text{bad}}$ (a "good" quotient point), the **functions  and $g'$ are identical over the entire fiber of $y$**. This means for all $x$ in the fiber of such a $y$, we have $f^{(i)}(x) = g'(x)$.
    * Consequently, any point $x \in S^{(i)}$ where a Hamming disagreement occurs (i.e., $f^{(i)}(x) \neq g'(x)$) **must** belong to a fiber whose corresponding quotient point $y$ is in $Y_{\text{bad}}$.
    * Therefore, the set of all Hamming disagreements is contained within the union of all "bad" fibers:
        $$\Delta(f^{(i)}, g') \subseteq \bigcup_{y \in Y_{\text{bad}}} \text{fiber}(y)$$
    * The size of each fiber is $2^\vartheta$. This leads to the key inequality linking the two distances:
        $$d_{\text{H}} \le d(f^{(i)}, g') = |\Delta(f^{(i)}, g')| \le |Y_{\text{bad}}| \cdot 2^\vartheta = d_{\text{fw}} \cdot 2^\vartheta$$

2.  **Using the Premise.**
    * We assume the premise: $d_{\text{fw}} < \frac{d_{i+\vartheta}}{2}$. As an integer inequality, this is $d_{\text{fw}} \le \lfloor \frac{d_{i+\vartheta}-1}{2} \rfloor$.
    * Substituting this into our key inequality from Step 1:
        $$d_{\text{H}} \le \left\lfloor \frac{d_{i+\vartheta}-1}{2} \right\rfloor \cdot 2^\vartheta$$

3.  **The Algebraic Identity.**
    * The core of the proof is the identity: $\left\lfloor \frac{d_{i+\vartheta}-1}{2} \right\rfloor \cdot 2^\vartheta = \left\lfloor \frac{d_{i}-1}{2} \right\rfloor$.
    * As we verified previously, both sides of this equation simplify to the same expression, $2^{\ell+\mathcal{R}-i-1} - 2^{\ell-i-1}$, so the identity is correct.

4.  **Conclusion.**
    * By chaining the inequalities, we get:
        $$d_{\text{H}} \le \left\lfloor \frac{d_{i}-1}{2} \right\rfloor$$
    * This final line is precisely the definition of the Hamming distance being within the unique decoding radius, which is equivalent to our goal: $d_{\text{H}} < \frac{d_{i}}{2}$. ✅

---

- **Lemma 4.18.** For each $i \in \{0, \vartheta, \ldots, \ell-\vartheta\}$, if $d(f^{(i)}, C^{(i)}) < \frac{d_i}{2}$, then, for each tuple of folding challenges $(r_i', \ldots, r_{i+\vartheta-1}') \in L^{\vartheta}$, we have that $\Delta(\text{fold}(f^{(i)}, r_i', \ldots, r_{i+\vartheta-1}'), \text{fold}(\bar{f}^{(i)}, r_i', \ldots, r_{i+\vartheta-1}')) \subset \Delta^{(i)}(f^{(i)}, \bar{f}^{(i)})$.
	- => i.e. if the function $f^{(i)}$ is **UDR-close** (valid codeword), then the errors after folding are all contained the fiberwise errors, which means **we know all possible errors before folding already**.
    * **Main Idea of Proof:** Proceeds by contraposition. If $y \notin \Delta^{(i)}(f^{(i)}, \bar{f}^{(i)})$, then the restrictions of $f^{(i)}$ and $\bar{f}^{(i)}$ to the fiber over $y$ are identical. By Definition 4.8, this implies their folded values at $y$ are also identical.
    * **Intuition**: Because folding is local (Def 4.8), if $f^{(i)}$ and $\bar{f}^{(i)}$ agree completely on the fiber above a point $y$, their folded values at $y$ must also agree.
	- **Consequence**: If $f^{(i)}$ is close to $\bar{f}^{(i)}$, then fold $\left(f^{(i)}\right)$ must be close to fold $\left(\bar{f}^{(i)}\right)$.

- **Definition 4.19.** For each $i \in \{0, \vartheta, \ldots, \ell-\vartheta\}$, we define the **bad subset (bad events)** $E_i \subset L^{\vartheta}$ as the set of tuples $(r_i', \ldots, r_{i+\vartheta-1}') \in L^{\vartheta}$ for which, as the case may be:
    $$
    \begin{aligned}
    & \text{in case \textbf{fiberwiseClose }} \boldsymbol{d}^{(i)}(\boldsymbol{f}^{(i)}, \boldsymbol{C}^{(i)}) < \frac{d_{i+\vartheta}}{2}: \Delta^{(i)}(f^{(i)}, \bar{f}^{(i)}) \not\subset \Delta(\text{fold}(f^{(i)}, r_i', \ldots, r_{i+\vartheta-1}'), \text{fold}(\bar{f}^{(i)}, r_i', \ldots, r_{i+\vartheta-1}')) \\
    & \text{in case \textbf{fiberwiseFar }} \boldsymbol{d}^{(i)}(\boldsymbol{f}^{(i)}, \boldsymbol{C}^{(i)}) \geq \frac{\boldsymbol{d}_{i+\vartheta}}{2}: d(\text{fold}(f^{(i)}, r_i', \ldots, r_{i+\vartheta-1}'), C^{(i+\vartheta)}) < \frac{d_{i+\vartheta}}{2}
    \end{aligned}
    $$
    - **Case 1**: errors eroded by randomness (a fiber set are folded into a single point), so the disagreement in the folded are smaller then the original e8rrors. Meanwhile, we expect the errors should not be eroded by the randomness,   means the errors (disagreement set) should be kept the same in the folded functions (i.e. equality $=$ is expected, instead of $\not\subset$). In other words, the right bad event here is the two sets are not equal $\ne$, which is equivalent to $\not\subset$ in this specific case due to **Lemma 4.18** and **Proposition farness-implies-non-compliance**
    - **Case 2**: Folding should preserve farness (not make farness vanish)
	- The role of the "bad event" in the soundness proof. It is the formally defined, low-probability scenario where the checks designed to detect **non-compliance** might fail.
		- The core of the security proof is **Proposition 4.23**, which states that if an oracle is non-compliant, the verifier will reject.
		- This proposition relies on **Lemma 4.24** to show that a non-compliant oracle `f⁽ⁱ*⁾` will lead to a folded function that is "far" from the correct one. However, the proof of **Lemma 4.24** works by explicitly **assuming the bad event `Eᵢ*` does not occur**.
---
**Mathematical view point** of defining the first case of bad event in **Definition 4.19**, which looks like have reversed direction compared to **fold error containment** of **Lemma 4.18**.

**Context**: Given $f^{(i)}$ is UDR-close
Let's look at the two sets of errors:
* $A = \Delta_{\text{fiber}}$ (The errors in the original function $f$).
* $B = \Delta_{\text{folded}}$ (The errors remaining in the folded function).

**Lemma 4.18 (The "Safety" Lemma)** guarantees: $B \subseteq A$
=> *"Folding never creates **new** errors from thin air."* (This is a mathematical theorem. It is **always true** given the distance bounds).

**Definition 4.19 (The "Bad Event")** is asking: "Did we get unlucky?"
The verifier is unlucky if **errors vanished**.
* If $A \subseteq B$, then every error in the original function is still present in the folded function. (Since $B \subseteq A$ is always true, this implies $A=B$, i.e., perfect error preservation => this is expected by honest verifier, which means we want all fiberwise errors to be passed to errors of folding).
* If **$\neg(A \subseteq B)$** (i.e., $A \not\subseteq B$), it means there was some error $y \in A$ that is **not** in $B$.
    * The error existed in the fiber ($y \in A$).
    * The error disappeared in the fold ($y \notin B$).

**Why not the other way?**

If you defined the bad event as $\neg (B \subseteq A)$ (i.e., `¬ (folded ⊆ fiber)`) => this contradicts with **Lemma 4.18** so it's meaningless

**Summary**:

| Logic                                 | Meaning                             | Implication for Verifier                    |
| :------------------------------------ | :---------------------------------- | :------------------------------------------ |
| **Lemma 4.18** ($B \subseteq A$)      | "Folding doesn't invent new lies."  | **Always True.** Safe foundation.           |
| **Ideal Case** ($A \subseteq B$)      | "Folding preserved all the lies."   | **Good.** Verifier will catch the cheat.    |
| **Bad Event** ($\neg(A \subseteq B)$) | "Some lies vanished/cancelled out." | **Bad.** The prover might get away with it! |

So, they defined it as $\neg(A \subseteq B)$ precisely because that is the **only way the verifier can lose** information about the prover's cheating.

---

- **Proposition 4.20. (Main proximity-gap application for bad folding event)** For each $i \in \{0, \vartheta, \ldots, \ell-\vartheta\}, \mu(E_i) \leq \vartheta \cdot \frac{|S^{(i+\vartheta)}|}{|L|}$ $= \vartheta \cdot \frac{2^{\ell + \mathcal{R} - (i + \vartheta)}}{|L|}$ holds.s
	- => Applied **Theorem 2.3** on tensor-folding proximity gap for RS code
    * **Main Idea of Proof:**
        * **Case 1 ($d^{(i)}(f^{(i)}, C^{(i)}) < d_{i+\vartheta}/2$):** For a fixed $y \in \Delta^{(i)}(f^{(i)}, \bar{f}^{(i)})$, the condition for $y$ to *not* be in the folded disagreement set (i.e., for $(r_i', \ldots) \in E_i^y$) translates via **Lemma 4.9** to a non-zero $\vartheta$-variate polynomial evaluating to 0. Schwartz-Zippel lemma bounds $|E_i^y|/|L|^\vartheta \le \vartheta/|L|$. Union bound over $y$ gives the result.
        * **Case 2 ($d^{(i)}(f^{(i)}, C^{(i)}) \geq d_{i+\vartheta}/2$):** An interleaved word $(f_j^{(i+\vartheta)})$ is constructed. **Lemma 4.21** shows this interleaved word is far from the interleaved code $C^{(i+\vartheta)^{2^{\vartheta}}}$. The condition for $E_i$ (that fold$(f^{(i)}, \ldots)$ is close to $C^{(i+\vartheta)}$) is then bounded using a result similar to list-decoding bounds (contrapositive of **Theorem 2.3** from FRI literature) applied to the interleaved word and the folding challenges.
	- Idea:
		- **Case 1** (fiberwise close): Bad event = folding causes disagreements to vanish
	    - **Case 2** (fiberwise far): Bad event = folded function appears close to code

**Case 1: Fiberwise Close (Lines 97-109)**

When `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ₊ₛₜₑₚₛ / 2`:

**Strategy**: Use Schwartz-Zippel lemma

- For each fiber `y ∈ Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾)`, define $E_i^y$ as the set of bad challenges (i.e. not belong to the folded agreement set)
- Show that $E_i^y$ is the vanishing set of a non-zero multivariate polynomial (via **Lemma 4.9**):
	- i.e. $fold(f^{(i)}, r_0, \ldots, r_{\vartheta-1})(y) \ne fold(\bar{f}^{(i)}, r_0, \ldots, r_{\vartheta-1})(y)$
- Apply Schwartz-Zippel: `μ(Eᵢʸ) ≤ steps / |L|`
- Union bound: `μ(Eᵢ) ≤ |Δ⁽ⁱ⁾| · steps / |L| ≤ |S⁽ⁱ⁺ˢᵗᵉᵖˢ⁾| · steps / |L|`

**Key insight from spec (line 17 of spec)**:

> The bad event `Eᵢʸ` is precisely the vanishing locus of the ϑ-variate polynomial `s(X₀, ..., X_{ϑ-1})` over L. Since s is not zero, applying the Schwartz-Zippel lemma gives `μ(Eᵢʸ) ≤ ϑ/|L|`.

**Case 2: Fiberwise Far (Lines 111-123)**

When `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ dᵢ₊ₛₜₑₚₛ / 2`:

**Strategy**: Use proximity gap theorem via **Lemma 4.21**

- Apply `lemma_4_21_interleaved_distance` to show interleaved word is far from code
- Use contrapositive of proximity gap theorem (Theorem 2.3 from DG25)
- Conclude: `μ(Eᵢ) ≤ steps · 2^{ℓ+R-i-steps} / |L| = steps · |S⁽ⁱ⁺ˢᵗᵉᵖˢ⁾| / |L|`

**Key insight from spec (line 59 of spec)**:

> Applying Lemma 4.21, we conclude that the contraposition of Theorem 2.3 is fulfilled with respect to the code C⁽ⁱ⁺ᵛ⁾, the proximity parameter e := ⌊(dᵢ₊ᵛ-1)/2⌋, and the interleaved word (fⱼ⁽ⁱ⁺ᵛ⁾).

---
- **Lemma 4.21 (Proximity-gap related stuff, completing Case 2 of Proposition 4.20).** Under our hypothesis $d^{(i)}(f^{(i)}, C^{(i)}) \geq \frac{d_{i+\vartheta}}{2}$, we have $U = d^{2^{\vartheta}}(((f_j^{(i+\vartheta)})_{j=0}^{2^{\vartheta}-1}, C^{(i+\vartheta)^{2^{\vartheta}}}) \geq \frac{d_{i+\vartheta}}{2}$.
    * **Main Idea of Proof:** For an arbitrary interleaved codeword $(g_j^{(i+\vartheta)})$, a "lift" $g^{(i)} \in C^{(i)}$ is constructed. It's shown that $g^{(i)}$ relates to $(g_j^{(i+\vartheta)})$ (via folding with basis vectors as challenges) similarly to how $f^{(i)}$ relates to $(f_j^{(i+\vartheta)})$ (via Lemma 4.9 and matrix $M_y$). Since $f^{(i)}$ is far from $g^{(i)}$ on many fibers (by hypothesis), and $M_y$ is invertible, the columns $(f_j^{(i+\vartheta)}(y))$ and $(g_j^{(i+\vartheta)}(y))$ must differ for these $y$, establishing the distance for the interleaved words.

- Formalization strategy for Lemma 4.21:
	- Let $G \in L[2^{i+\vartheta} \times 2^{\ell + \mathcal{R} - (i+\vartheta)}]$ be an arbitrary (interleaved) codeword in $C^{(i+\vartheta)^{2^{\vartheta}}}$.
		- We have $\forall j \in [2^{i+\vartheta}], G_j \in C^{(i+\vartheta)}$, i.e. there is a univariate polynomials $P_j^{(i+\vartheta)}(X) \in  L[X]^{\prec 2^{\ell - (i+\vartheta)}}$ that generates $G_j$ (over $S^{(i+\vartheta)})$ per row $j$: $G_{j}^{(i+\vartheta)}=\operatorname{Enc}(P_{j}^{(i+\vartheta)}, S^{(i+\vartheta)})$
		- For any interleaved codeword $G$ of $C^{(i+\vartheta)^{2^{\vartheta}}}$, **each single column** $\left(G_{j}^{(i+\vartheta)}(y)\right)_{j=0}^{2^{\vartheta}-1}$ of $v$ that represents the point $y \in S^{(i+\vartheta)}$ can be represented as the Mat-Vec multiplication: **(foldMatrix $M_y$) * (evaluations of $\bar{G}$ over fiber of $y$ )** as in equation $(41)$, specifically:
	$$
	\begin{bmatrix}
	G_{0}^{(i+\vartheta)}(y) \\
	\vdots \\
	G_{2^{\vartheta}-1}^{(i+\vartheta)}(y)
	\end{bmatrix}
	:=
	\begin{bmatrix}
	M_{y}
	\end{bmatrix}
	\cdot
	\begin{bmatrix}
	\bar{G}^{(i)}(x_{0}) \\
	\vdots \\
	\bar{G}^{(i)}(x_{2^{\vartheta}-1})
	\end{bmatrix} \tag{41}
	$$
			- where $\bar{G} (i.e. \bar{G}^{(i)}): S^{(i)} \rightarrow L$ is the result of $\text{lift}(G)$
			- $|S^{(i+\vartheta)}| = 2^{\ell + \mathcal{R} - (i+\vartheta)}$ such columns form the whole interleaved codeword $G$
		- The lift function : $\text{lift}(G) = \bar{G}$ is constructed as follow:
			- First, we represent each row poly in the  $i+\vartheta^{\text {th }}$-order **novel polynomial basis**:  $j \in\left\{0, \ldots, 2^{\vartheta}-1\right\}, P_{j}^{(i+\vartheta)}(X):=\sum_{k=0}^{2^{\ell-i-\vartheta}-1} a_{j, k}$. $X_{k}^{(i+\vartheta)}(X)$
			- Next, we define the intertwined poly $P^{(i)}(X) \in L[X]^{\prec 2^{\ell - (i)}}$: $P^{(i)}(X):=\sum_{j=0}^{2^{\vartheta}-1} \sum_{k=0}^{\ell-i-\vartheta} a_{j, k} \cdot X_{k \cdot 2^{\vartheta}+j}^{(i)}$
				- which intertwines the novel coeffs of the row polys with the $i$-order **novel polynomial basis
			- Then $\bar{G} = \operatorname{Enc}(P^{(i)}, S^{(i)})$, this means $\bar{G} \in C^{(i)}$ (i.e. the output of the lift function is a codeword)
		- **Proof that $G$ and $\bar{G}$ satisfies equation (41), i.e. $\forall y \in S^{(i+\vartheta)}, j \in [2^{i+\vartheta}], G_j(y) = \begin{bmatrix} M_{y} \end{bmatrix}_j *_v \begin{bmatrix} \bar{G}^{(i)}(x_j) \ldots \end{bmatrix}^\top$
			- Let $\left(j_{0}, \ldots, j_{\vartheta-1}\right)$ for the bits of the row index $j$ (i.e., so that $j=\sum_{k=0}^{\vartheta-1} 2^{k} \cdot j_{k}$ holds), this will be used as a **binary challenge tuple** for $fold()$ below
			- (1). First, we have $G_{j}^{(i+\vartheta)}$ and $fold\left(\bar{G}, j_{0}, \ldots, j_{\vartheta-1}\right)$ agree identically over the domain $S^{(i+\vartheta)}$, i.e.  $G_{j}^{(i+\vartheta)} = fold\left(\bar{G}^{(i)}, j_{0}, \ldots, j_{\vartheta-1}\right)$. Indeed, this is a direct consequence of **Lemma 4.13** and of the construction of $\bar{G}$ (note that $G_{j}^{(i+\vartheta)}(y)$ 's underlying polynomial's coefficients are the $j^{\text {th }}$ refinement of $\bar{G}$ 's underlying polynomial's).
			- (2). On the other hand, applying **Lemma 4.9** to $y \in S^{(i+\vartheta)}$ and $\bar{G}^{(i)}$, with the folding tuple ( $j_{0}, \ldots, j_{\vartheta-1}$ ), we see that the dot product between $M_{y}$ 's $j^{\text {th }}$ row and $\left(\bar{G}\left(x_{0}\right), \ldots, \bar{G}\left(x_{2^{\vartheta}-1}\right)\right)$ is exactly fold $\left(\bar{G}, j_{0}, \ldots, j_{\vartheta-1}\right)(y)=G_{j}(y)$, where the latter equality was just argued (in (1)).
				- This is correct for generic function in $S^{(i)} \rightarrow L$, i.e. not necessarily a codeword like $\bar{G}$, formalized in`preTensorCombine_row_eq_fold_with_binary_row_challenges`
	- **We do proof by contradiction**. Assuming $U$ is $\frac{d_{i+\vartheta}}{2}$-close to $C^{(i+\vartheta)^{2^{\vartheta}}}$.
		 - Let $V$ be the closest codeword to $U$, we have $\bar{V} = lift(V)$. $U$ and $V$ differ at less than $\frac{d_{i+\vartheta}}{2}$ columns $y$, i.e. there are less than $\frac{d_{i+\vartheta}}{2}$ points $y \in S^{(i+\vartheta)}$ that the restrictions of $f_i = lift(U)$ and $\bar{V} = lift(V)$ on the fiber of $y$ differ (1)
		 - Given (in the original hypothesis of the lemma) that $f^{(i)}$ is fiberwise-far from $C^{(i)}$: $d^{(i)}(f^{(i)}, C^{(i)}) \geq \frac{d_{i+\vartheta}}{2}$, then for at least $\frac{d_{i+\vartheta}}{2}$ points $y \in S^{(i+\vartheta)}$, $f^{(i)}|_{(q^{(i+\vartheta-1)} \circ \ldots \circ q^{(i)})^{-1}(\{y\})}$ $\ne$  $\bar{V}^{(i)}|_{(q^{(i+\vartheta-1)} \circ \ldots \circ q^{(i)})^{-1}(\{y\})}$ (2)
		 - (1) contradicts (2) => $U$ must $\frac{d_{i+\vartheta}}{2}$-far from $C^{(i+\vartheta)^{2^{\vartheta}}}$, Q.E.D

---
- **Proposition 4.22.** The probability that any among the bad events $E_0, E_{\vartheta}, \ldots, E_{\ell-\vartheta}$ occurs is at most $\frac{2^{\ell+\mathcal{R}}}{|L|}$.
    * **Main Idea of Proof:** Uses a union bound over the probabilities $\mu(E_i)$ from Proposition 4.20. The sum $\sum |S^{(i+\vartheta)}|$ is a geometric series, which simplifies to the stated bound.
---
- **Proposition 4.23 (Assuming no bad events).** If any of $\mathcal{A}$'s oracles is not compliant, then $\mathcal{V}$ accepts with at most negligible probability.
	- => This is for final phase?
    * **Main Idea of Proof:** Let $i^*$ be the **highest index of a non-compliant oracle**
        1.  **Lemma 4.24** shows that fold$(f^{(i^*)}, \text{challenges})$ is far from $\bar{f}^{(i^*+\vartheta)}$ (the unique codeword close to $f^{(i^*+\vartheta)}$, which exists if $i^*+\vartheta$ is compliant, or any codeword if not, this is because the **compliance condition requires $f^{(i^*+\vartheta)}$ to be uniquely-decodable**). **This holds assuming the bad event $E_{i^*}$ doesn't occur**.
        2. **Lemma 4.25** shows that if the verifier's random query point $v$ has its suffix $(v_{i^*+\vartheta}, \ldots)$ fall into this disagreement set (between fold$(f^{(i^*)})$ and $\bar{f}^{(i^*+\vartheta)}$), the verifier will reject. This is argued by induction through the verifier's query loop, showing that the computed values $c_j$ by $\mathcal{V}$ will diverge from the values of $\bar{f}^{(j)}$. => The probability of hitting such a disagreement point is significant (at least $d_{i^*+\vartheta}/(2|S^{(i^*+\vartheta)}|)$). Repeating $\gamma$ times, the probability of acceptance becomes negligible.

	- **Lemma 4.24.** For $i^* \in \{0, \vartheta, \ldots, \ell-\vartheta\}$ as above, we have $d(\text{fold}(f^{(i^*)}, r_{i^*}', \ldots, r_{i^*+\vartheta-1}'), \bar{f}^{(i^*+\vartheta)}) \geq \frac{d_{i^*+\vartheta}}{2}$.
	    * **Main Idea of Proof:**
	        * **Case 1 ($d^{(i^*)}(f^{(i^*)}, C^{(i^*)}) < d_{i^*+\vartheta}/2$):** $f^{(i^*)}$ is close to a unique $\bar{f}^{(i^*)}$. Non-compliance of $i^*$ means $\bar{f}^{(i^*+\vartheta)} \neq \text{fold}(\bar{f}^{(i^*)}, \text{challenges})$. Lemma 4.18 implies fold$(f^{(i^*)})$ is close to fold$(\bar{f}^{(i^*)})$. By reverse triangle inequality, fold$(f^{(i^*)})$ must be far from $\bar{f}^{(i^*+\vartheta)}$.
	        * **Case 2 ($d^{(i^*)}(f^{(i^*)}, C^{(i^*)}) \geq d_{i^*+\vartheta}/2$):** **Assuming bad event $E_{i^*}$** didn't occur (from Def 4.19), fold$(f^{(i^*)}, \text{challenges})$ is far from any codeword in $C^{(i^*+\vartheta)}$, thus far from $\bar{f}^{(i^*+\vartheta)}$.

--- 

**Lemma 4.24 (Full proof)**: For $i^{*} \in\{0, \vartheta, \ldots, \ell-\vartheta\}$ where **$f^{(i)}$ is non-compliant, $f^{(i+\vartheta)}$ is compliant (hmm this only needs , and the bad event $E_{i^{*}}$ doesn't occur**, we have $d(fold(f^{(i^{*})}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}), \bar{f}^{(i^{*}+\vartheta)}) \geq \frac{d_{i^{*}+\vartheta}}{2}$.

**Proof**. There are two cases:
 1. **Case 1 : fiberwise-close ($d^{(i^*)}(f^{(i^*)}, C^{(i^*)}) < \frac{d_{i^*+\vartheta}}{2}$)**:  we write $\bar{f}^{\left(i^{*}\right)} \in C^{\left(i^{*}\right)}$ for the (**fiberwise-close**) codeword for which $\left|\Delta^{\left(i^{*}\right)}\left(f^{\left(i^{*}\right)}, \bar{f}^{\left(i^{*}\right)}\right)\right|<\frac{d_{i^{*}+\vartheta}}{2}$ (this is same the unique-decoded codeword???).
	- **NOTE**: within the UDR, the fiberwise-closest codeword is same as UDR-decoded codeword
	- => We note that $d\left(f^{\left(i^{*}\right)}, \bar{f}^{\left(i^{*}\right)}\right)<\frac{d_{i^{*}}}{2}$ a fortiori holds; by Definition 4.17 and our choice of $i^{*}$, we thus must have in turn $\bar{f}^{\left(i^{*}+\vartheta\right)} \neq \operatorname{fold}\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)$ (since $f^{(i*)})$ is **non-compliant**).
		- Since  and fold  are unequal codewords in $C^{\left(i^{*}+\vartheta\right)}$, we have $d\left(\bar{f}^{\left(i^{*}+\vartheta\right)}, \text { fold }\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right) \ge \|C^{i^*+\vartheta}\| = d_{i^{*}+\vartheta}$ **(1)**
	- On the other hand, by **Lemma 4.18 (disagreement between two folded functions are subset of fiberwise disagreement of OG functions)**. $\left|\Delta^{\left(i^{*}\right)}\left(f^{\left(i^{*}\right)}, \bar{f}^{\left(i^{*}\right)}\right)\right|<\frac{d_{i^{*}+\vartheta}}{2}$ implies that $d\left(\right.$ fold $\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)$, fold $\left.\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right)<$ $\frac{d_{i^{*}+\vartheta}}{2}$. **(2)**
	- Finally, by the reverse triangle inequality, $d\left(\right.$ fold $\left.\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \bar{f}^{\left(i^{*}+\vartheta\right)}\right)$ (the lhs of the goal) is at least **(1) - (2)**: $d\left(\bar{f}^{\left(i^{*}+\vartheta\right)}, \text { fold }\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right)-d\left(\text { fold }\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \text { fold }\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right)$ $\ge d_{i^{*}+\vartheta}-\frac{d_{i^{*}+\vartheta}}{2} \geq \frac{d_{i^{*}+\vartheta}}{2}$, and the proof of the first case is complete.

 2. **Case 1 : fiberwise-far ($d^{(i^*)}(f^{(i^*)}, C^{(i^*)}) \ge \frac{d_{i^*+\vartheta}}{2}$)**: Trivially from definition of $E_{i^{*}}$. Specifically, since $E_{i^*}$ **didn't occur** implies, by definition, that $d(fold(f^{(i^{*})}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}), C^{(i^{*}+\vartheta)}) \geq \frac{d_{i^{*}+\vartheta}}{2}$. Since $\bar{f}^{(i^{*}+\vartheta)} \in C^{(i^{*}+\vartheta)}$ is a codeword, $d(fold(f^{(i^{*})}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}), \bar{f}^{(i^{*}+\vartheta)}) \geq \frac{d_{i^{*}+\vartheta}}{2}$ in particular holds, and the proof is again complete.

--- 
- 
	- **Lemma 4.25.** Whenever its suffix $(v_{i^*+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}) \in \Delta(\text{fold}(f^{(i^*)}, r_{i^*}', \ldots, r_{i+\vartheta-1}'), \bar{f}^{(i^*+\vartheta)})$, $\mathcal{V}$ rejects.
	    * **Main Idea of Proof:** Inductive argument on the verifier's query loop starting from $i=i^*$.
	        * **Base case ($i=i^*$):** The verifier computes $c_{i^*+\vartheta} = \text{fold}(f^{(i^*)}, \ldots)(v_{i^*+\vartheta}, \ldots)$. By hypothesis, this is $\neq \bar{f}^{(i^*+\vartheta)}(v_{i^*+\vartheta}, \ldots)$.
	        * **Inductive step (for $i \geq i^*+\vartheta$):** Assume $c_i \neq \bar{f}^{(i)}(v_i, \ldots)$. If $\mathcal{V}$ doesn't reject at $c_i \stackrel{?}{=} f^{(i)}(v_i, \ldots)$, then $f^{(i)}(v_i, \ldots) \neq \bar{f}^{(i)}(v_i, \ldots)$, meaning $(v_i, \ldots) \in \Delta(f^{(i)}, \bar{f}^{(i)})$. **Assuming no bad event $E_i$**, this implies $(v_{i+\vartheta}, \ldots) \in \Delta(\text{fold}(f^{(i)}), \text{fold}(\bar{f}^{(i)}))$. Since $i > i^*$, oracle $i$ is compliant, so fold$(\bar{f}^{(i)}) = \bar{f}^{(i+\vartheta)}$. Thus, $\text{fold}(f^{(i)})(v_{i+\vartheta}, \ldots) \neq \bar{f}^{(i+\vartheta)}(v_{i+\vartheta}, \ldots)$, i.e. $c_{i+\vartheta} \ne \bar{f}^{(i+\vartheta)}(v_{i+\vartheta}, \ldots)$
	        This propagates until $c_{\ell} \neq \bar{f}^{(\ell)}(v_{\ell}, \ldots)$ (comparison of constant scalars). Since $c = \bar{f}^{(\ell)}(\ldots)$ (since $f^{(l)}$ - a virtual oracle not committed by $P$ - is actually a **constant function that always outputs $c$**, due to its definition) (as $\mathcal{A}$'s final message $c$ forms the function $f^{(\ell)}$ which must be close to $\bar{f}^{(\ell)}$ for compliance), the check $c_{\ell} \stackrel{?}{=} c$ fails.

- **Query-phase soundness proof**: The security argument in the paper works by showing that dishonesty creates a "cascade of failure" that is guaranteed to be detected. The proof starts its analysis from the last point of failure (non-compliance oracle `i*`). **Proposition 4.23**:
    - 1.  **Find the Last Lie:** The proof assumes the prover cheated and identifies `i*` as the **highest index of a non-compliant oracle**. This is the last point in the protocol where the prover's committed data fundamentally breaks the rules.
    - 2.  **Show the Lie Propagates:** The proof then shows that this single act of non-compliance at `i*` will inevitably cause a detectable inconsistency in the next step.
    - 3.  **Lemma 4.24** proves that because `f⁽ⁱ*⁾` was non-compliant, the next folded oracle, `fold(f⁽ⁱ*⁾)`, will be "far" from the honest, decoded oracle `f̄⁽ⁱ*⁺ᶿ⁾`.
    - 4.  **Show the Verifier Catches the Lie:** **Lemma 4.25** then proves that this "farness" will be caught by the verifier's random queries. It uses an inductive argument:
		- The disagreement at round `i*` causes the verifier's computed value `cᵢ*₊ᶿ` to be wrong.
		- Since all oracles after `i*` *are* compliant (by definition of `i*` being the highest), this error will be faithfully propagated through all subsequent folding checks during the query phase.
		- This guarantees that the error will cascade all the way to the end, causing the final check `cₗ = c` to fail, leading the verifier to reject.

- **Soundness of Folding-based evaluation**: `P(Successful cheating) ≈ P(Bad Event Occurs) + P(Verifier Fails to Detect | No Bad Event Occurs)`
- **Total soundness of the whole protocol**: The total soundness error is bounded by the sum of three distinct probabilities:
1. **Sum-check Soundness Error:** The probability that the algebraic part of the proof fails.
    * **Error:** `(2 * ℓ) / |L|`
2. **Bad Event Probability (Proposition 4.22):** The probability that the verifier gets an "unlucky" set of random challenges that breaks the normal properties of the folding operation.
    * **Error:** `2ˡ⁺ᴿ / |L|`
3.  **Query Failure Probability (Proposition 4.23):** The probability that, *assuming no bad event occurred*, the `γ` random queries all fail to detect a non-compliant prover.
    * **Error:** `(1/2 + 1/(2 * 2ᴿ))ᵞ`

Using the union bound, the total soundness error of the Binary Basefold protocol is the sum of these values:
$$\text{Total Error} \le \frac{2 \cdot \ell}{|L|} + \frac{2^{\ell+\mathcal{R}}}{|L|} + \left(\frac{1}{2} + \frac{1}{2 \cdot 2^\mathcal{R}}\right)^\gamma$$

---
- Proximity gaps in Binary Basefold: The Binary BaseFold component of the combined scheme (often referred to as FRI-Binius or Construction 5.1/4.11 in the sources) requires **proximity gap theorems from external papers**, specifically those related to tensor-folding. Here is a detailed explanation of why these external theorems are necessary:
	- 1. **FRI Folding and Proximity Gaps:** The binary adaptation of the BaseFold polynomial commitment scheme introduces a **new, multilinear style of many-to-one FRI folding**. This folding style contrasts with the original FRI protocol's univariate approach. The soundness proof of the original FRI protocol relied on the proximity gap result for low-degree parameterized curves [Ben+23, Thm. 1.5].
	- 2. **Necessity of External Tensor-Folding Proximity Gaps:** Due to the introduction of the multilinear FRI-folding variant (also called "oracle-skipping"), the scheme's security treatment requires a **different kind of proximity gap**. The security analysis uses a **tensor-folding proximity gap** of the sort recently established by **Diamond and Posen [DP24, Thm. 2]**. More precisely, it uses a **sharpening of that result due to Diamond and Gruen [DG25, Cor. 1] (Theorem 2.3)**.
	- 3. **Application in the Security Proof:** This specific proximity gap result, formalized as Theorem 2.3, is crucial for proving the security of the binary BaseFold IOPCS (Construction 4.11). The proof of Proposition 4.23, which argues that the verifier rejects with high probability if an oracle is not compliant, explicitly relies on the **contraposition of Theorem 2.3** regarding the code $C^{(i+\vartheta)} \subset L^{2^{\ell+R-i-\vartheta}}$.
	- **Theorem 2.3 (Diamond–Gruen [DG25, Cor. 1])** addresses tensor-style proximity gaps for interleaved words, which are necessary when dealing with the multilinear folding technique applied in the Binary BaseFold variant.

=> The source document (which describes the combined scheme, or FRI-Binius) **does state** the required proximity gap theorem, but **it does not include the proof** of the theorem itself, as the result is derived from external papers.

Here is a breakdown of the information regarding the proximity gap theorems:
1.  **Statement of the Theorem:** The core result needed for the security of the Binary BaseFold component is explicitly recorded as **Theorem 2.3 (Diamond–Gruen [DG25, Cor. 1])**. This theorem is located in Section 2, "Background and Notation," under the subsection "Proximity Gaps".
2.  **Attribution to External Sources:** The statement of Theorem 2.3 immediately cites the external paper **Diamond–Gruen [DG25, Cor. 1]** as its source.
    *   The source explains that this result demonstrates that Reed–Solomon codes exhibit **tensor-style proximity gaps**.
    *   It is specifically identified as a sharpening of the tensor-folding proximity gap result established by Diamond and Posen [DP24, Thm. 2].
    *   The Diamond–Gruen result is applied to **Theorem 2.2 (Ben-Sasson, et al. [Ben+23, Thm. 4.1])**, which concerns proximity gaps over affine lines, in order to obtain Theorem 2.3.
3.  **Necessity in the Proof:** The external nature of these results is essential because the security proof for the binary BaseFold IOPCS (Construction 4.11) relies on a **new, multilinear style of many-to-one FRI folding** ("oracle-skipping").
    *   The original FRI protocol relied on a different proximity gap result for low-degree parameterized curves [Ben+23, Thm. 1.5].
    *   The security argument for the new multilinear folding technique uses the **contraposition of Theorem 2.3** regarding interleaved codes (specifically $C^{2^\vartheta}$).

In summary, the necessary proximity gap theorem is stated in the document as background (Theorem 2.3) but its validity and proof are secured by external academic papers.

## 4 Binary BaseFold

In this section, we present our large-field PCS. We have already sketched the main problem in Subsection 1.4 above; here, we record a few further details.
### The additive NTT

The number-theoretic transform entails evaluating a polynomial $P(X)=\sum_{j=0}^{2^{\ell}-1} a_{j}$. $X^{j}$ of degree less than $2^{\ell}$ on some $2^{\ell}$-sized subset of its coefficient field. In fields containing a $2^{\ell}$-sized multiplicative coset, the Cooley-Tukey algorithm computes the number-theoretic transform in $O\left(\ell \cdot 2^{\ell}\right)$ time. Binary fields, on the other hand, have no 2-adicity at all-their multiplicative groups of units are odd.

In a classic and farsighted work, Cantor [Can89] developed an "additive" variant of the FFT: an algorithm that evaluates $P(X)$ not on a multiplicative coset of its coefficient field, but on an additive subgroup of it. Indeed, each binary field $\mathbb{F}_{2^{r}}$ can be viewed as a vector space over its own subfield $\mathbb{F}_{2}$. Here, by an additive subgroup of $\mathbb{F}_{2^{r}}$, we mean an $\mathbb{F}_{2^{-} \text {-vector subspace } S \subset \mathbb{F}_{2^{r}} \text {. Cantor's algorithm evaluates } P(X) \text { on any such }}$ $2^{\ell}$-sized domain $S \subset \mathbb{F}_{2^{r}}$ in $O\left(\ell^{\log _{2}(3)} \cdot 2^{\ell}\right)$ time.

For some time, it was not known whether the Cooley-Tukey algorithm's characteristic $O\left(\ell \cdot 2^{\ell}\right)$ time complexity could be recovered in the additive, binary case. In a key and important work, Lin, Chung and Han LCH14 attain exactly this feat, with a caveat: they interpret their input vector $\left(a_{0}, \ldots, a_{2^{\ell}-1}\right)$ as $P(X)$ 's coefficients not in the standard monomial basis, but in a novel polynomial basis that those authors introduce. That is, the polynomial which their algorithm evaluates over $S$ is not $\sum_{j=0}^{2^{\ell}-1} a_{j} \cdot X^{j}$, but $\sum_{j=0}^{2^{\ell}-1} a_{j} \cdot X_{j}(X)$; here, for each $j \in\left\{0, \ldots, 2^{\ell}-1\right\}, X_{j}(X)$ is an alternate basis polynomial of degree $j$ that those authors describe. Lin, Chung and Han LCH14 build their basis polynomials $\left(X_{j}(X)\right)_{j=0}^{2^{\ell}-1}$ out of subspace vanishing polynomials. These are polynomials $\widehat{W}_{i}(X)$, for $i \in\{0, \ldots, \ell\}$, which respectively vanish identically on an ascending chain of $\mathbb{F}_{2^{2}}$-subspaces $U_{0} \subset \cdots \subset U_{\ell}$ of $\mathbb{F}_{2^{r}}$.

Our binary adaptation of BaseFold PCS ties together two disparate threads: Lin, Chung and Han LCH14's additive NTT and FRI BBHR18a. We recall that binary-field FRI works with the aid of a sequence of $\mathbb{F}_{2}$-subspaces $S^{(0)}, \ldots, S^{(\ell)}$ of $\mathbb{F}_{2^{r}}$, themselves connected by linear subspace polynomials:

$$
S^{(0)} \xrightarrow{q^{(0)}} S^{(1)} \xrightarrow{q^{(1)}} S^{(2)} \xrightarrow{q^{(2)}} \cdots \xrightarrow{q^{(\ell-1)}} S^{(\ell)} .
$$

Here, the maps $q^{(0)}, \ldots, q^{(\ell-1)}$ are linear subspace polynomials of degree 2.
Choosing the folding maps. To use BaseFold PCS in characteristic 2, we must use the additive NTT instead of the standard one, and use binary-field FRI instead of prime-field FRI. Simple enough, but which domains $S^{(0)}, \ldots, S^{(\ell)}$ and which maps $q^{(0)}, \ldots, q^{(\ell-1)}$ should we use in the latter protocol? FRI BBHR18a does not suggest a canonical choice; each choice there works as well as any other. But BaseFold's FRI subprotocol is not just a proximity test; it's also a built-in multilinear evaluator (see Subsection 1.2). BaseFold PCS relies on the fact whereby a FRI execution which begins on the Reed-Solomon encoding of ( $a_{0}, \ldots, a_{2^{\ell}-1}$ ) will end on the constant polynomial whose value on $S^{(\ell)}$ is identically

$$
\begin{equation*}
a_{0}+a_{1} \cdot r_{0}^{\prime}+a_{2} \cdot r_{1}^{\prime}+a_{3} \cdot r_{0}^{\prime} \cdot r_{1}^{\prime}+\cdots+a_{2^{\ell}-1} \cdot r_{0}^{\prime} \cdots \cdot r_{\ell-1}^{\prime} \tag{38}
\end{equation*}
$$

where $\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ are the verifier's FRI challenges. For maps $q^{(0)}, \ldots, q^{(\ell-1)}$ generically chosen, this fact will simply cease to hold. We discuss this problem further in the introduction of Section 4 below.

We recover BaseFold PCS in characteristic 2 by introducing a specialization of binary FRI that works compatibly with LCH14. That is, we introduce a particular choice of the maps $q^{(0)}, \ldots, q^{(\ell-1)}$ which causes the equality (38) to re-emerge. Interestingly, the right choice of $q^{(0)}, \ldots, q^{(\ell-1)}$ turns out to be that for which, for each $i \in\{0, \ldots, \ell\}$, the composition identity

$$
\widehat{W}_{i}=q^{(i-1)} \circ \cdots \circ q^{(0)}
$$

holds. That is, we choose our FRI folding maps $q^{(0)}, \ldots, q^{(\ell-1)}$ so that they "factor" Lin, Chung and Han LCH14 's subspace polynomials. Our binary BaseFold variant is independently important, and has already figured in key subsequent works, including Brehm et al.'s Blaze [Bre+25] and Frigo and shelat [Fs24].

### More remarks on FRI
We opt moreover to modify FRI itself, so as to induce a Lagrange-style, as opposed to a monomial-style, 2-to-1 folding pattern in the coefficient domain. In our FRI variant, the value of the prover's final oracle becomes rather

$$
a_{0} \cdot\left(1-r_{0}\right) \cdots \cdots\left(1-r_{\ell-1}\right)+\cdots+a_{2^{\ell}-1} \cdot r_{0} \cdots r_{\ell-1}
$$

the evaluation at ( $r_{0}, \ldots, r_{\ell-1}$ ) of the polynomial whose coefficients in the multilinear Lagrange basis-as opposed to in the multilinear monomial basis-are ( $a_{0}, \ldots, a_{2^{\ell}-1}$ ). (We explain this further in Remark 4.7.)

Separately, standard FRI [BBHR18a, § 3.2] supports arbitrary-arity folding, controlled by a folding arity parameter $\eta \geq 1$. The parameter $\eta$ mediates a tradeoff between the number of oracles committed (which grows like $\frac{\ell}{\eta}$ ) and the size of each Merkle leaf (which grows like $2^{\eta}$ ). The "sweet spot" tends to be around $\eta=4$, in practical deployments. The effect on proof size at stake-i.e., which one stands to induce, upon changing $\eta$ from 1 to something better-is significant (amounting to a halving at least, if not better). In rough terms, FRI stipulates that, to fold a given oracle using the parameter $\eta$, the prover interpolate a univariate polynomial of degree less than $2^{\eta}$ on each coset of the relevant oracle, and finally evaluate the resulting univariate polynomials collectively at the verifier's challenge point.

BaseFold, as written, does not support the use of higher-arity folding, for straightforward reasons. Upon using a parameter $\eta>1$, one would cause (38) to fail in essentially two ways. For one, the number of challenges $r_{i}^{\prime}$ available would become too few (something like $\frac{\ell}{\eta}$, as opposed to $\ell$ ). Moreover, the relationship between the list ( $a_{0}, \ldots, a_{2^{\ell}-1}$ ) of initial coefficients and the value of the final constant FRI oracle would become that of a multivariate evaluation-of individual degree at most $2^{\eta}-1$-over the challenges $r_{i}^{\prime}$, as opposed to of a multilinear one. For this reason, BaseFold as written remains unable to draw on the proof-size gains available at the hands of higher-arity folding (which are significant).

We introduce a new, multilinear style of many-to-one FRI folding, which contrasts with FRI's univariate approach [BBHR18a, § 3.2]. We describe our FRI folding variant in Subsection 4.2 below (see in particular Definitions 4.6 and 4.8). We parameterize our method by a constant $\vartheta$, which plays a role analogous to $\eta$ 's. Informally, we stipulate that the verifier send $\vartheta$ folding challenges, and that the provecr fold its oracle, again coset-wise, using a length- $2^{\vartheta}$ tensor combination of the verifier's challenges over each coset. Our folding technique is equivalent to that in which the prover repeatedly performs standard, 2-to-1 folding $\vartheta$ times in succession-consuming $\vartheta$ challenges in the process, as opposed to 1 -and commits only to the final result. (For this reason, we informally call it "oracle-skipping".) Interestingly, our FRI-folding variant makes necessary a sort of proximity gap different from that invoked by the original FRI protocol. Indeed, while the soundness proof $[$ Ben $+23, \S 8.2]$ of FRI uses the proximity gap result [Ben +23 , Thm. 1.5] for low-degree parameterized curves, our security treatment below instead uses a tensor-folding proximity gap of the sort recently established by Diamond and Posen DP24, Thm. 2] (in fact, we use a sharpening of that result due to Diamond and Gruen [DG25, Cor. 1]).

Practical matters. We examine in various further aspects of binary-field FRI. For example, even in the abstract IOP model, we must fix $\mathbb{F}_{2}$-bases of the respective Reed-Solomon domains $S^{(i)}$, in order to interpret our committed functions $f^{(i)}: S^{(i)} \rightarrow L$ as $L$-valued strings. That is, we must implicitly lexicographically flatten each domain $S^{(i)}$, using some ordered $\mathbb{F}_{2}$-basis of it, known to both the prover and the verifier. The choice of these bases matters. Indeed, for $\mathbb{F}_{2}$-bases of $S^{(i)}$ and $S^{(i+1)}$ chosen arbitrarily, the fundamental operation which associates to each $y \in S^{(i+1)}$ its fiber $q^{(i)^{-1}}(\{y\}) \subset S^{(i)}$-which both the prover and the verifier must perform repeatedly-could come to assume complexity on the order of $\operatorname{dim}\left(S^{(i)}\right)^{2}$ bit-operations, even after a linear-algebraic preprocessing phase.

We suggest a family of bases for the respective domains $S^{(i)}$ with respect to which the maps $q^{(i)}$ come to act simply by projecting away their first coordinate. In particular, the application of each map $q^{(i)}$-in coordinates—becomes free; the preimage operation $q^{(i)^{-1}}(\{y\})$ comes to amount simply to that of prepending an arbitrary boolean coordinate to $y$ 's coordinate representation. While bases with these properties can of course be constructed in FRI even for maps $q^{(i)}$ chosen arbitrarily, our procedure moreover yields a basis of the initial domain $S^{(0)}$ which coincides with that expected by the additive NTT LCH14. In particular, our prover may use as is the output of the additive NTT as its $0^{\text {th }}$ FRI oracle, without first subjecting that output to the permutation induced by an appropriate change-of-basis transformation on $S^{(0)}$. We believe that these observations stand to aid all implementers of binary-field FRI.

### 4.1 Using FRI in Novel Polynomial Basis

We begin by proposing a specific construction of those subspace polynomials $q^{(0)}, \ldots, q^{(\ell-1)}$ invoked internally by FRI. Throughout this section, we fix a binary field $L$, with $\mathbb{F}_{2}$-basis ( $\beta_{0}, \ldots, \beta_{r-1}$ ). Throughout the remainder of this subsection-and in fact, the entire paper-we impose the simplifying assumption whereby $\beta_{0}=1$. We fix moreover a size parameter $\ell \in\{0, \ldots, r-1\}$ and a rate parameter $\mathcal{R} \in\{1, \ldots, r-\ell\}$. We finally recall the subspace vanishing polynomials $\widehat{W}_{i}(X) \in L[X]$, for $i \in\{0, \ldots, \ell\}$, which we now view as $\mathbb{F}_{2}$-linear maps $\widehat{W}_{i}: L \rightarrow L$, as well as their non-normalized counterparts $W_{i}: L \rightarrow L$ (see Subsection 2.3).

We begin by defining our FRI domains and folding maps.

#### Definition 4.1
For each $i \in\{0, \ldots, \ell\}$, we define the domain

$$
S^{(i)}:=\widehat{W}_{i}\left(\left\langle\beta_{0}, \ldots, \beta_{\ell+\mathcal{R}-1}\right\rangle\right)
$$

Moreover, for each $i \in\{0, \ldots, \ell-1\}$, we define

$$
q^{(i)}(X):=\frac{W_{i}\left(\beta_{i}\right)^{2}}{W_{i+1}\left(\beta_{i+1}\right)} \cdot X \cdot(X+1)
$$

For each $i \in\{0, \ldots, \ell-1\}$, the map $q^{(i)}(X)$ is a linear subspace polynomial of degree 2 . A priori, this map's kernel could relate arbitrarily to the domain $S^{(i)} \subset L$; moreover, the image of its restriction to $S^{(i)}$ could relate arbitrarily to $S^{(i+1)}$. In the following sequence of results, we prove that in fact $q^{(i)}\left(S^{(i)}\right)=S^{(i+1)}$ holds for each $i \in\{0, \ldots, \ell-1\}$. In particular, the chain of maps $q^{(0)}, \ldots, q^{(\ell-1)}$ and the spaces $S^{(0)}, \ldots, S^{(\ell)}$ yield a valid global parameterization of the FRI protocol (in the sense of Subsection 2.4).

#### Lemma 4.2

For each $i \in\{0, \ldots, \ell-1\}$, we have the equality $q^{(i)} \circ \widehat{W}_{i}=\widehat{W}_{i+1}$ of polynomials.
**Proof**. We invoke the following direct calculation:

$$
\begin{array}{rlr}
\left(q^{(i)} \circ \widehat{W}_{i}\right)(X) & =\frac{W_{i}\left(\beta_{i}\right)^{2}}{W_{i+1}\left(\beta_{i+1}\right)} \cdot \widehat{W}_{i}(X) \cdot\left(\widehat{W}_{i}(X)+1\right) & \quad\left(\text { by definition of } q^{(i)} .\right) \
& =\frac{W_{i}\left(\beta_{i}\right)^{2}}{W_{i+1}\left(\beta_{i+1}\right)} \cdot \frac{W_{i}(X)}{W_{i}\left(\beta_{i}\right)} \cdot \frac{W_{i}(X)+W_{i}\left(\beta_{i}\right)}{W_{i}\left(\beta_{i}\right)} & \quad\left(\text { by definition of } \widehat{W}_{i} .\right) \
& =\frac{W_{i}(X) \cdot\left(W_{i}(X)+W_{i}\left(\beta_{i}\right)\right)}{W_{i+1}\left(\beta_{i+1}\right)} & \quad\left(\text { cancellation of } W_{i}\left(\beta_{i}\right)^{2} .\right) \
& =\frac{W_{i+1}(X)}{W_{i+1}\left(\beta_{i+1}\right)} & \quad\left(\text { recursive characterization of } W_{i+1}(X) .\right) \
& =\widehat{W}_{i+1}(X) . & \quad\left(\text { by definition of } \widehat{W}_{i+1}(X) .\right)
\end{array}
$$

In the second-to-last step, we exploit the recursive identity $W_{i+1}(X)=W_{i}(X) \cdot\left(W_{i}(X)+W_{i}\left(\beta_{i}\right)\right)$, itself a basic consequence of the definitions of $W_{i+1}$ and $W_{i}$ and of the linearity of $W_{i}$.

#### Theorem 4.3
For each $i \in\{0, \ldots, \ell-1\}, q^{(i)}\left(S^{(i)}\right)=S^{(i+1)}$.
**Proof**. Using Lemma 4.2 we obtain:

$$
\begin{array}{rlr}
q^{(i)}\left(S^{(i)}\right) & =q^{(i)}\left(\widehat{W}_{i}\left(\left\langle\beta_{0}, \ldots, \beta_{\ell+\mathcal{R}-1}\right\rangle\right)\right) & \left.\quad \text { (by definition of } S^{(i)} .\right) \
& =\widehat{W}_{i+1}\left(\left\langle\beta_{0}, \ldots, \beta_{\ell+\mathcal{R}-1}\right\rangle\right) & \quad(\text { by Lemma 4.2 }) \
& =S^{(i+1)} & \quad\left(\text { again by definition of } S^{(i+1)} .\right)
\end{array}
$$

This completes the proof of the theorem.
In the following further corollary of Lemma 4.2, we argue that the polynomials $q^{(0)}, \ldots, q^{(\ell-1)}$ collectively "factor" the normalized subspace polynomials $W_{0}, \ldots, \widehat{W}_{\ell}$, at least provided we assume $\beta_{0}=1$.

#### Corollary 4.4
For each $i \in\{0, \ldots, \ell\}, \widehat{W}_{i}=q^{(i-1)} \circ \cdots \circ q^{(0)}$ holds.
**Proof**. In the base case $i=0$, we must show that $\widehat{W}_{0}$ equals the empty composition (namely $X$ itself). To show this, we recall first that $W_{0}(X)=X$. Moreover:

$$
\widehat{W}_{0}(X)=\frac{X}{W_{0}\left(\beta_{0}\right)}=\frac{X}{\beta_{0}}=X ;
$$

in the last step, we use our global simplifying assumption $\beta_{0}=1$.
For $i \in\{0, \ldots, \ell-1\}$ arbitrary, Lemma 4.2 shows that $\widehat{W}_{i+1}=q^{(i)} \circ \widehat{W}_{i}$. Applying induction to $\widehat{W}_{i}$, we conclude that this latter map in turn equals $q^{(i)} \circ \cdots \circ q^{(0)}$.

We note finally the following result.
#### Corollary 4.5
For each $i \in\{0, \ldots, \ell\}$, the set $\left(\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{\ell+\mathcal{R}-1}\right)\right)$ is an $\mathbb{F}_{2}$-basis of the space $S^{(i)}$.
**Proof**. Indeed, the subspace $V_{i}:=\left\langle\beta_{i}, \ldots, \beta_{\ell+\mathcal{R}-1}\right\rangle$ is clearly a subspace of $\left\langle\beta_{0}, \ldots, \beta_{\ell+\mathcal{R}-1}\right\rangle$, so that in turn $\widehat{W}_{i}\left(V_{i}\right) \subset \widehat{W}_{i}\left(\left\langle\beta_{0}, \ldots, \beta_{\ell+\mathcal{R}-1}\right\rangle\right)$, which itself equals $S^{(i)}$ (by Definition 4.1). On the other hand, the restriction of $\widehat{W}_{i}$ to $V_{i}$ is necessarily injective, since $\widehat{W}_{i}$ 's kernel $\left\langle\beta_{0}, \ldots, \beta_{i-1}\right\rangle$ intersects $V_{i}$ trivially. Since $S^{(i)}$ is $\ell+\mathcal{R}-i$-dimensional, we conclude by a dimension count that $\left(\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{\ell+\mathcal{R}-1}\right)\right)$ spans $S^{(i)}$.

The bases $\left\langle\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{\ell+\mathcal{R}-1}\right)\right\rangle=S^{(i)}$, for $i \in\{0, \ldots, \ell\}$, serve to simplify various aspects of our protocol's implementation. For example, expressed in coordinates with respect to these bases, each map $q^{(i)}: S^{(i)} \rightarrow S^{(i+1)}$ acts simply by projecting away its $0^{\text {th }}$-indexed component (indeed, for each $i \in$ $\{0, \ldots, \ell-1\}, q^{(i)}$ maps $\left(\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{\ell+\mathcal{R}-1}\right)\right)$ to $\left.\left(0, \widehat{W}_{i+1}\left(\beta_{i+1}\right), \ldots, \widehat{W}_{i+1}\left(\beta_{\ell+\mathcal{R}-1}\right)\right)\right)$. Similarly, for each $i \in\{0, \ldots, \ell-1\}$ and each $y \in S^{(i+1)}$, the two $L$-elements $x \in S^{(i)}$ for which $q^{(i)}(x)=y$ differ precisely at their $0^{\text {th }}$ components, and elsewhere agree with $y$ 's coordinate representation. Below, we often identify $S^{(i)} \cong \mathcal{B}_{\ell+\mathcal{R}-i}$ as sets, using these bases; moreover, where possible, we eliminate altogether the maps $q^{(0)}, \ldots, q^{(\ell-1)}$ from our descriptions. These measures make our protocol's description and implementation more transparent.

### 4.2 FRI Folding, Revisited

We now introduce a new FRI-like folding mechanism. Below, we again write $L$ for a binary field.
#### Definition 4.6
We fix an index $i \in\{0, \ldots, \ell-1\}$ and a map $f^{(i)}: S^{(i)} \rightarrow L$. For each $r \in L$, we define the map fold $\left(f^{(i)}, r\right): S^{(i+1)} \rightarrow L$ by setting, for each $y \in S^{(i+1)}$ :

$$
\text { fold }\left(f^{(i)}, r\right): y \mapsto\left[\begin{array}{cc}
1-r & r
\end{array}\right] \cdot\left[\begin{array}{cc}
x_{1} & -x_{0} \
-1 & 1
\end{array}\right] \cdot\left[\begin{array}{c}
f^{(i)}\left(x_{0}\right) \
f^{(i)}\left(x_{1}\right)
\end{array}\right]
$$

where we write $\left(x_{0}, x_{1}\right):=q^{(i)^{-1}}(\{y\})$ for the fiber of $q^{(i)}$ over $y \in S^{(i+1)}$.

#### Remark 4.7
Definition 4.6 s quantity fold $\left(f^{(i)}, r\right)(y)$ is closely related—and yet not equivalent—to FRI's expression interpolant $\left(\left.f^{(i)}\right|_{q^{(i)-1}(\{y\})}\right)(r)$. (FRI's variant, however, admits a similar matrix expression.) The essential point is that FRI's variant induces a monomial fold, as opposed to a Lagrange fold; that is, if we were to use FRI's variant instead of our own, then our Lemma 4.13 below would remain true, albeit with the alternate conclusion $P^{(i+1)}(X)=\sum_{j=0}^{2^{\ell-i-1}-1}\left(a_{2 j}+r_{i}^{\prime} \cdot a_{2 j+1}\right) \cdot X_{j}^{(i+1)}(X)$. Our entire theory admits a parallel variant in this latter setting, though that variant introduces further complications.

We finally record the following iterated extension of Definition 4.6 .

#### Definition 4.8
We fix a positive folding factor $\vartheta$, an index $i \in\{0, \ldots, \ell-\vartheta\}$, and a map $f^{(i)}: S^{(i)} \rightarrow L$. For each tuple $\left(r_{0}, \ldots, r_{\vartheta-1}\right) \in L^{\vartheta}$, we abbreviate fold $\left(f^{(i)}, r_{0}, \ldots, r_{\vartheta-1}\right):=$ fold $\left(\cdots\right.$ fold $\left.\left(f^{(i)}, r_{0}\right), \cdots, r_{\vartheta-1}\right)$.

We have the following mathematical characterization of this iterated folding operation:

#### Lemma 4.9
For each positive folding factor $\vartheta$, each index $i \in\{0, \ldots, \ell-\vartheta\}$, and each $y \in S^{(i+\vartheta)}$, there is a $2^{\vartheta} \times 2^{\vartheta}$ invertible matrix $M_{y}$, which depends only on $y \in S^{(i+\vartheta)}$, such that, for each function $f^{(i)}: S^{(i)} \rightarrow L$ and each tuple $\left(r_{0} \ldots, r_{\vartheta-1}\right) \in L^{\vartheta}$ of folding challenges, we have the matrix identity:

$$
\text { fold }\left(f^{(i)}, r_{0}, \ldots, r_{\vartheta-1}\right)(y)=\left[\bigotimes_{j=0}^{\vartheta-1}\left(1-r_{j}, r_{j}\right)\right] \cdot\left[\quad M_{y}\right] \cdot\left[\begin{array}{c}
f^{(i)}\left(x_{0}\right) \
\vdots \
f^{(i)}\left(x_{2^{\vartheta}-1}\right)
\end{array}\right]
$$

where the right-hand vector's values $\left(x_{0}, \ldots, x_{2^{\vartheta}-1}\right)$ represent the fiber $\left(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)}\right)^{-1}(\{y\}) \subset S^{(i)}$.
**Proof**. We prove the result by induction on $\vartheta$. In the base case $\vartheta=1$, the claim is a tautology, in view of Definition 4.6 We note that that definition's matrix $\left[\begin{array}{cc}x_{1} & -x_{0} \ -1 & 1\end{array}\right]$ is invertible, since its determinant $x_{1}-x_{0}$ is nonzero (and in fact equals 1, a fact we shall use below).

We thus fix a folding factor $\vartheta>1$, and suppose that the claim holds for $\vartheta-1$. We write $\left(z_{0}, z_{1}\right):=$ $q^{(i+\vartheta-1)^{-1}}(\{y\})$, as well as $\left(x_{0}, \ldots, x_{2^{\vartheta}-1}\right):=\left(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)}\right)^{-1}(\{y\})$. Unwinding Definition 4.8, we recursively express the relevant quantity fold $\left(f^{(i)}, r_{0}, \ldots, r_{\vartheta-1}\right)(y)$-which, for typographical reasons, we call $\mathfrak{f}$-in the following way:

$$
\begin{aligned}
& \mathfrak{f}=\left[\begin{array}{ll}
1-r_{\vartheta-1} & r_{\vartheta-1}
\end{array}\right] \cdot\left[\begin{array}{cc}
z_{1} & -z_{0} \
-1 & 1
\end{array}\right] \cdot\left[\begin{array}{l}
\operatorname{fold}\left(f^{(i)}, r_{0}, \ldots, r_{\vartheta-2}\right)\left(z_{0}\right) \
\operatorname{fold}\left(f^{(i)}, r_{0}, \ldots, r_{\vartheta-2}\right)\left(z_{1}\right)
\end{array}\right] \
& \left.=\left[\begin{array}{ll}
1-r_{\vartheta-1} & r_{\vartheta-1}
\end{array}\right] \cdot \underbrace{\left[\begin{array}{cc}
z_{1} & -z_{0} \
-1 & 1
\end{array}\right] \cdot\left[\bigotimes_{j=0}^{\vartheta-2}\left(1-r_{j}, r_{j}\right)\right.}_{\text {these matrices may be interchanged. }} \right\rvert\, \begin{array}{l|l}
\hline M_{z_{0}} & \
& M_{z_{1}}
\end{array}] \cdot\left[\begin{array}{c}
f^{(i)}\left(x_{0}\right) \
\vdots \
f^{(i)}\left(x_{2^{\vartheta}-1}\right)
\end{array}\right] .
\end{aligned}
$$

In the second step above, we apply the inductive hypothesis on both $z_{0}$ and $z_{1}$. That hypothesis furnishes the nonsingular, $2^{\vartheta-1} \times 2^{\vartheta-1}$ matrices $M_{z_{0}}$ and $M_{z_{1}}$; we note moreover that the union of the fibers $\left(q^{(i+\vartheta-2)} \circ \cdots \circ q^{(i)}\right)^{-1}\left(\left\{z_{0}\right\}\right)$ and $\left(q^{(i+\vartheta-2)} \circ \cdots \circ q^{(i)}\right)^{-1}\left(\left\{z_{1}\right\}\right)$ is precisely $\left(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)}\right)^{-1}(\{y\})$. Interchanging the two matrices bracketed above, we further reexpress this quantity as:

$$
=\left[\begin{array}{ll|l}
1-r_{\vartheta-1} & r_{\vartheta-1}
\end{array}\right] \cdot\left[\begin{array}{l|l|l}
\bigotimes_{j=0}^{\vartheta-2}\left(1-r_{j}, r_{j}\right) & \
\hline & \bigotimes_{j=0}^{\vartheta-2}\left(1-r_{j}, r_{j}\right)
\end{array}\right] \cdot\left[\begin{array}{l|l}
\operatorname{diag}\left(z_{1}\right) & \operatorname{diag}\left(-z_{0}\right) \
\hline \operatorname{diag}(-1) & \operatorname{diag}(1)
\end{array}\right] \cdot\left[\begin{array}{l|l}
M_{z_{0}} & \
\hline & M_{z_{1}}
\end{array}\right] \cdot\left[\begin{array}{c}
f^{(i)}\left(x_{0}\right) \
\vdots \
f^{(i)}\left(x_{2^{\vartheta}-1}\right)
\end{array}\right] .
$$

By the standard recursive substructure of the tensor product, the product of the left-hand two matrices equals exactly $\bigotimes_{j=0}^{\vartheta-1}\left(1-r_{j}, r_{j}\right)$. On the other hand, the product of the two $2^{\vartheta} \times 2^{\vartheta}$ nonsingular matrices above is itself nonsingular, and supplies the required $2^{\vartheta} \times 2^{\vartheta}$ matrix $M_{y}$.

We emphasize that, in Lemma 4.9, the matrix $M_{y}$ depends only on $y \in S^{(i+\vartheta)}$-and of course on $\vartheta$ and $i \in\{0, \ldots, \ell-\vartheta\}$ - and not on the map $f^{(i)}$ or the folding challenges $\left(r_{0}, \ldots, r_{\vartheta-1}\right) \in L^{\vartheta}$.

#### Remark 4.10
Interestingly, the matrix $M_{y}$ of Lemma 4.9 is nothing other than that of the inverse additive NTT [LCH14, § III. C.] on the coset ( $x_{0}, \ldots, x_{2^{\vartheta}-1}$ ); i.e., it's the matrix which, on input the evaluations of some polynomial of degree less than $2^{\vartheta}$ on the set of elements $\left(x_{0}, \ldots, x_{2^{\vartheta}-1}\right)$, returns the coefficients-with respect to the $i^{\text {th }}$-order novel basis (see Remark 4.15 below)-of that polynomial.

### 4.3 Our Large-Field IOPCS

We now present our binary adaptation of BaseFold's IOPCS [ZCF24, § 5], itself based on the material of our Subsections 4.1 and 4.2 above. In order to present a notationally simpler variant of our protocol, we assume below that $\vartheta \mid \ell$; this requirement is not necessary.

#### CONSTRUCTION 4.11 (Binary BaseFold IOPCS).
We define $\Pi=($ Setup, Commit, $\mathcal{P}, \mathcal{V})$ as follows.

1. params $\leftarrow \Pi$. Setup $\left(1^{\lambda}, \ell\right)$. On input $1^{\lambda}$ and $\ell$, choose a constant, positive rate parameter $\mathcal{R} \in \mathbb{N}$ and a binary field $L / \mathbb{F}_{2}$ whose degree $r$ (say) over $\mathbb{F}_{2}$ satisfies $r=\omega(\log \lambda)$ and $r \geq \ell+\mathcal{R}$. Initialize the vector oracle $\mathcal{F}_{\text {Vec }}^{L}$. Fix a folding factor $\vartheta \mid \ell$ and a repetition parameter $\gamma=\omega(\log \lambda)$. Fix an arbitrary $\mathbb{F}_{2}$-basis $\left(\beta_{0}, \ldots, \beta_{r-1}\right)$ of $L$. Write $\left(X_{0}(X), \ldots, X_{2^{\ell}-1}(X)\right)$ for the resulting novel $L$-basis of $L[X]^{\prec 2^{\ell}}$, and fix the domains $S^{(0)}, \ldots, S^{(\ell)}$ and the polynomials $q^{(0)}, \ldots, q^{(\ell-1)}$ as in Subsection 4.1. Write $C^{(0)} \subset L^{2^{\ell+\mathcal{R}}}$ for the Reed-Solomon code $\operatorname{RS}_{L, S^{(0)}}\left[2^{\ell+\mathcal{R}}, 2^{\ell}\right]$.
2. $[f] \leftarrow$ П.Commit $($ params,$t)$. On input $t\left(X_{0}, \ldots, X_{\ell-1}\right) \in L\left[X_{0}, \ldots, X_{\ell-1}\right]^{\preceq 1}$, use $t$ 's Lagrange coefficients $(t(w))_{w \in \mathcal{B}_{\ell}}$ as the coefficients, in the novel polynomial basis, of a univariate polynomial $P(X):=\sum_{w \in \mathcal{B}_{\ell}} t(w) \cdot X_{\{w\}}(X)$, say. Using Algorithm 2 compute the Reed-Solomon codeword $f: S^{(0)} \rightarrow L$ defined by $f: x \mapsto P(x)$. Submit (submit, $\ell+\mathcal{R}, f$ ) to the vector oracle $\mathcal{F}_{\text {Vec }}^{L}$. Upon receiving (receipt, $\ell+\mathcal{R},[f]$ ) from $\mathcal{F}_{\mathrm{Vec}}^{L}$, output the handle $[f]$.

We define ( $\mathcal{P}, \mathcal{V}$ ) as the following IOP, in which both parties have the common input $[f], s \in L$, and $\left(r_{0}, \ldots, r_{\ell-1}\right) \in L^{\ell}$, and $\mathcal{P}$ has the further input $t\left(X_{0}, \ldots, X_{\ell-1}\right) \in L\left[X_{0}, \ldots, X_{\ell-1}\right]^{\preceq 1}$.

1. $\mathcal{P}$ writes $h\left(X_{0}, \ldots, X_{\ell-1}\right):=\widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, X_{0}, \ldots, X_{\ell-1}\right) \cdot t\left(X_{0}, \ldots, X_{\ell-1}\right)$.
2. $\mathcal{P}$ and $\mathcal{V}$ both abbreviate $f^{(0)}:=f$ and $s_{0}:=s$, and execute the following loop:

for $i \in\{0, \ldots, \ell-1\}$ do
    $\mathcal{P}$ sends $\mathcal{V}$ the polynomial $h_{i}(X):=\sum_{w \in \mathcal{B}_{\ell-i-1}} h\left(r_{0}^{\prime}, \ldots, r_{i-1}^{\prime}, X, w_{0}, \ldots, w_{\ell-i-2}\right)$.
    $\mathcal{V}$ requires $s_{i} \stackrel{?}{=} h_{i}(0)+h_{i}(1)$. $\mathcal{V}$ samples $r_{i}^{\prime} \leftarrow L$, sets $s_{i+1}:=h_{i}\left(r_{i}^{\prime}\right)$, and sends $\mathcal{P} r_{i}^{\prime}$.
    $\mathcal{P}$ defines $f^{(i+1)}: S^{(i+1)} \rightarrow L$ as the function fold $\left(f^{(i)}, r_{i}^{\prime}\right)$ of Definition 4.6.
    if $i+1=\ell$ then $\mathcal{P}$ sends $c:=f^{(\ell)}(0, \ldots, 0)$ to $\mathcal{V}$.
    else if $\vartheta \mid i+1$ then $\mathcal{P}$ submits (submit, $\ell+\mathcal{R}-i-1, f^{(i+1)}$ ) to the oracle $\mathcal{F}_{\text {Vec }}^{L}$.

3. $\mathcal{V}$ requires $s_{\ell} \stackrel{?}{=} \widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot c$.
4. $\mathcal{V}$ executes the following querying procedure:

for $\gamma$ repetitions do
    $\mathcal{V}$ samples $v \leftarrow \mathcal{B}_{\ell+\mathcal{R}}$ randomly.
    for $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$ (i.e., taking $\vartheta$-sized steps) do
        for each $u \in \mathcal{B}_{\vartheta}, \mathcal{V}$ sends (query, $\left[f^{(i)}\right],\left(u_{0}, \ldots, u_{\vartheta-1}, v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ ) to the oracle.
        if $i>0$ then $\mathcal{V}$ requires $c_{i} \stackrel{?}{=} f^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)$.
        $\mathcal{V}$ defines $c_{i+\vartheta}:=\operatorname{fold}\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$.
    $\mathcal{V}$ requires $c_{\ell} \stackrel{?}{=} c$.

In our commitment procedure above, we give meaning to the commitment of $f$ by implicitly identifying $S^{(0)} \cong \mathcal{B}_{\ell+\mathcal{R}}$ as sets (as discussed above); similarly, in the prover's line 6 above, we identify $\mathcal{B}_{\ell+\mathcal{R}-i-1} \cong$ $S^{(i+1)}$. Conversely, in its lines 4 and 6 above, the verifier must implicitly identify the $\mathcal{B}_{\ell+\mathcal{R}-i}$-elements $\left(u_{0}, \ldots, u_{\vartheta-1}, v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)_{u \in \mathcal{B}_{\vartheta}}$ with $S^{(i)}$-elements-and the $\mathcal{B}_{\ell+\mathcal{R}-i-\vartheta}$-element $\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ with an $S^{(i+\vartheta)}$-element-in order to appropriately apply Definition 4.8. We note that, in line 6, $\mathcal{V}$ has precisely the information it needs to compute fold $\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ (namely, the values of $f^{(i)}$ on the fiber $\left.\left(u_{0}, \ldots, u_{\vartheta-1}, v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)_{u \in \mathcal{B}_{\vartheta}} \cong\left(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)}\right)^{-1}\left(\left\{\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)\right\}\right)\right)$.

The completness of Construction 4.11s evaluation IOP is not straightforward. For instance, it is simply not obvious what the folding operation of line 4 does to the coefficients of the low-degree polynomial $P^{(i)}(X)$ underlying $f^{(i)}$. (Though our folding operation departs slightly from FRI's-we refer to Remark 4.7 for a discussion of this fact- the conceptual obstacle is essentially the same.) Indeed, the completeness proof of generic FRI [BBHR18a, § 4.1.1] tells us that the folded function $f^{(i+1)}$ represents the evaluations of some polynomial $P^{(i+1)}(X)$ of appropriate degree on the domain $S^{(i+1)}$. But which one? The proof of [BBHR18a, § 4.1.1] fails to constructively answer this question, in that it invokes the generic characteristics of the multivariate reduction-called $Q^{(i)}(X, Y)$-of $P^{(i)}(X)$ by $Y-q^{(i)}(X)$. (We refer to e.g. von zur Gathen and Gerhard GG13, Alg. 21.11] for a thorough treatment of multivariate division.) It seems simply infeasible to analyze by hand the execution of the multivariate division algorithm with sufficient fidelity as to determine with any precision the result $P^{(i+1)}(Y)=Q^{(i)}\left(r_{i}^{\prime}, Y\right)$ (though we don't rule out the prospect whereby a proof could in principle be achieved in this way).

Instead, we introduce certain, carefully-selected $L$-bases of the spaces $L[X]^{\prec 2^{\ell-i}}$, for $i \in\{0, \ldots, \ell\}$ (socalled "higher-order" novel polynomial bases). As it turns out, the respective coefficients of $P^{(i)}(X)$ and $P^{(i+1)}(X)$ with respect to these bases are tractably related; their relationship amounts to an even-odd tensorfold by the FRI challenge $r_{i}^{\prime}$. Proceeding by induction, we obtain the desired characterization of $c$.

#### Theorem 4.12
The IOPCS $\Pi=($ Setup, Commit, $\mathcal{P}, \mathcal{V})$ of Construction 4.11 is **complete**.
**Proof**. Provided that $\mathcal{P}$ is honest, $s=t\left(r_{0}, \ldots, r_{\ell-1}\right)$ will hold. Since $t\left(r_{0} \ldots, r_{\ell-1}\right)=\sum_{w \in \mathcal{B}_{\ell}} h(w)$, this guarantee implies that $s=s_{0}=\sum_{w \in \mathcal{B}_{\ell}} h(w)$ will hold, so that, by the completeness of the sumcheck, $\mathcal{V}$ 's checks $s_{i} \stackrel{?}{=} h_{i}(0)+h_{i}(1)$ will pass. Finally, $s_{\ell}=h\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)=\widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, r_{0}^{\prime}, \ldots, r_{l-1}^{\prime}\right) \cdot t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ too will hold. To argue the completeness of $\mathcal{V}$ 's check $s_{\ell} \stackrel{?}{=} \widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot c$ above, it thus suffices to argue that, for $\mathcal{P}$ honest, $c=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ will hold.

We introduce a family of further polynomial bases. For each $i \in\{0, \ldots, \ell-1\}$, we define the $i^{\text {th }}$-order subspace vanishing polynomials $\widehat{W}_{0}^{(i)}, \ldots, \widehat{W}_{\ell-i-1}^{(i)}$ as the polynomials $X, q^{(i)}, q^{(i+1)} \circ q^{(i)}, \ldots, q^{(\ell-2)} \circ \ldots \circ q^{(i)}$, respectively (that is, $\widehat{W}_{k}^{(i)}:=q^{(i+k-1)} \circ \cdots \circ q^{(i)}$, for each $k \in\{0, \ldots, \ell-i-1\}$ ). Finally, we define the $i^{\text {th }}$-order novel polynomial basis by setting $X_{j}^{(i)}:=\prod_{k=0}^{\ell-i-1} \widehat{W}_{k}^{(i)^{j k}}$, for each $j \in\left\{0, \ldots, 2^{\ell-i}-1\right\}$ (here, again, we write $\left(j_{0}, \ldots, j_{\ell-i-1}\right)$ for the bits of $\left.j\right)$. We adopt the notational convention whereby the $\ell^{\text {th }}$-order basis consists simply of the constant polynomial $X_{0}^{(\ell)}(X)=1$. Below, we use a certain inductive relationship between the bases $\left(X_{j}^{(i)}(X)\right)_{j=0}^{2^{\ell-i}-1}$ and $\left(X_{j}^{(i+1)}(X)\right)_{j=0}^{2^{\ell-i-1}-1}$; that is, for each $j \in\left\{0, \ldots, 2^{\ell-i-1}-1\right\}$, the polynomials $X_{2 j}^{(i)}(X)$ and $X_{2 j+1}^{(i)}(X)$ respectively equal $X_{j}^{(i+1)}\left(q^{(i)}(X)\right)$ and $X \cdot X_{j}^{(i+1)}\left(q^{(i)}(X)\right)$.

#### Lemma 4.13
Fix an index $i \in\{0, \ldots, \ell-1\}$. If $f^{(i)}: S^{(i)} \rightarrow L$ is exactly the evaluation over $S^{(i)}$ of the polynomial $P^{(i)}(X)=\sum_{j=0}^{2^{\ell-i}-1} a_{j} \cdot X_{j}^{(i)}(X)$, then, under honest prover behavior, $f^{(i+1)}: S^{(i+1)} \rightarrow L$ is exactly the evaluation over $S^{(i+1)}$ of the polynomial $P^{(i+1)}(X)=\sum_{j=0}^{2^{\ell-i-1}-1}\left(\left(1-r_{i}^{\prime}\right) \cdot a_{2 j}+r_{i}^{\prime} \cdot a_{2 j+1}\right) \cdot X_{j}^{(i+1)}(X)$.

**Proof**. Given $P^{(i)}(X)$ as in the hypothesis of the lemma, we introduce the even and odd refinements $P_{0}^{(i+1)}(X):=\sum_{j=0}^{2^{\ell-i-1}-1} a_{2 j} \cdot X_{j}^{(i+1)}(X)$ and $P_{1}^{(i+1)}(X):=\sum_{j=0}^{2^{\ell-i-1}-1} a_{2 j+1} \cdot X_{j}^{(i+1)}(X)$ of $P^{(i)}(X)$. We note the following key polynomial identity:

$$
\begin{equation*}
P^{(i)}(X)=P_{0}^{(i+1)}\left(q^{(i)}(X)\right)+X \cdot P_{1}^{(i+1)}\left(q^{(i)}(X)\right) ; \tag{39}
\end{equation*}
$$

This identity is a direct consequence of the definitions of the higher-order novel polynomial bases.
We turn to the proof of the lemma. We claim that $f^{(i+1)}(y)=P^{(i+1)}(y)$ holds for each $y \in S^{(i+1)}$, where $P^{(i+1)}(X)$ is as in the lemma's hypothesis. To this end, we let $y \in S^{(i+1)}$ be arbitrary; we moreover write $\left(x_{0}, x_{1}\right):=q^{(i)^{-1}}(\{y\})$ for the fiber of $q^{(i)}$ over $y$. We begin by examining the values $P^{(i)}\left(x_{0}\right)$ and $P^{(i)}\left(x_{1}\right)$. For each $b \in\{0,1\}$ we have:

$$
\begin{aligned}
P^{(i)}\left(x_{b}\right) & =P_{0}^{(i+1)}\left(q^{(i)}\left(x_{b}\right)\right)+x_{b} \cdot P_{1}^{(i+1)}\left(q^{(i)}\left(x_{b}\right)\right) \
& =P_{0}^{(i+1)}(y)+x_{b} \cdot P_{1}^{(i+1)}(y)
\end{aligned}
$$

(by the identity $(39)$.)

$$
\left(\text { using } q^{(i)}\left(x_{b}\right)=y .\right)
$$

Using now our assumption whereby $f^{(i)}\left(x_{b}\right)=P^{(i)}\left(x_{b}\right)$ for each $b \in\{0,1\}$, and unwinding the prescription of Definition 4.6, we obtain:

$$
\begin{aligned}
f^{(i+1)}(y) & =\left[\begin{array}{ll}
1-r_{i}^{\prime} & r_{i}^{\prime}
\end{array}\right] \cdot\left[\begin{array}{cc}
x_{1} & -x_{0} \
-1 & 1
\end{array}\right] \cdot\left[\begin{array}{l}
P^{(i)}\left(x_{0}\right) \
P^{(i)}\left(x_{1}\right)
\end{array}\right] \quad \text { (by our hypothesis on } f^{(i)} \text {, and by Definition } 4.6 \text {.) } \
& =\left[\begin{array}{ll}
1-r_{i}^{\prime} & r_{i}^{\prime}
\end{array}\right] \cdot\left[\begin{array}{cc}
x_{1} & -x_{0} \
-1 & 1
\end{array}\right] \cdot\left[\begin{array}{cc}
1 & x_{0} \
1 & x_{1}
\end{array}\right] \cdot\left[\begin{array}{l}
P_{0}^{(i+1)}(y) \
P_{1}^{(i+1)}(y)
\end{array}\right] \text { (by the calculation just performed above.) } \
& =\left[\begin{array}{ll}
1-r_{i}^{\prime} & r_{i}^{\prime}
\end{array}\right] \cdot\left[\begin{array}{l}
P_{0}^{(i+1)}(y) \
P_{1}^{(i+1)}(y)
\end{array}\right] \quad \text { (cancellation of inverse matrices.) } \
& =P^{(i+1)}(y) . \quad\left(\text { by the definitions of } P_{0}^{(i+1)}(X), P_{1}^{(i+1)}(X), \text { and } P^{(i+1)}(X) .\right)
\end{aligned}
$$

To achieve the third equality above, we note that the matrices $\left[\begin{array}{cc}x_{1} & -x_{0} \ -1 & 1\end{array}\right]$ and $\left[\begin{array}{cc}1 & x_{0} \ 1 & x_{1}\end{array}\right]$ are inverses; there, we use the guarantee $x_{1}-x_{0}=1$, a basic consequence of Definition 4.1 (or rather of $\operatorname{ker}\left(q^{(i)}\right)=\{0,1\}$ ).

Applying Corollary 4.4, we note finally that $\left(\widehat{W}_{k}^{(0)}\right)_{k=0}^{\ell-1}$ and $\left(X_{j}^{(0)}\right)_{j=0}^{2^{\ell}-1}$ themselves equal precisely the standard subspace vanishing and novel basis polynomials, respectively. It follows that in the base case $i=0$ of Lemma 4.13-and again assuming honest behavior by the prover-we have that $f^{(0)}$ will equal the evaluation over $S^{(0)}$ of $P^{(0)}(X):=P(X)=\sum_{w \in \mathcal{B}_{\ell}} t(w) \cdot X_{\{w\}}^{(0)}(X)$. Applying Lemma 4.13 repeatedly, we conclude by induction that **$f^{(\ell)}$ will equal the evaluation over $S^{(\ell)}$ of the constant polynomial $\sum_{w \in \mathcal{B}_{\ell}} \widetilde{\mathrm{eq}}\left(w_{0}, \ldots, w_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot t(w)=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$**, so that $c=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ will hold, as desired.

The completeness of the verifier's query phase is self-evident (and is just as in [BBHR18a, § 4.1.1]); we note that $\mathcal{V}$ applies to each oracle $f^{(i)}$ the same folding procedure that $\mathcal{P}$ does. This completes the proof of completeness.

#### Remark 4.14
- Using the techniques of Subsection 4.1 and of Theorem 4.12 above, we are able to suggest a new explanation of the additive NTT algorithm of Lin, Chung and Han [LCH14, § III.], and of its correctness; we note also our Algorithm 2 above. (Li et al. $[\mathrm{Li}+18, \mathrm{Alg} .2]$ present yet a further-and very interestingperspective, which differs both from ours and from Lin-Chung-Han's.) We fix an index $i \in\{0, \ldots, \ell-1\}$ and a polynomial $P^{(i)}(X):=\sum_{j=0}^{2^{\ell-i}-1} a_{j} \cdot X_{j}^{(i)}(X)$ expressed with respect to the $i^{\text {th }}$-order novel basis. The key idea is that the values of $P^{(i)}(X)$ on the domain $S^{(i)}$ can be derived-using only $O\left(2^{\ell+\mathcal{R}-i}\right) K$-operationsgiven the values of $P^{(i)}(X)$ 's even and odd refinements $P_{0}^{(i+1)}(X)$ and $P_{1}^{(i+1)}(X)$ (as in the proof of Lemma 4.13 over the domain $S^{(i+1)}$. This is a direct consequence of the identity (39) above. Indeed, applying that identity, we see that, for $y \in S^{(i+1)}$ arbitrary, with fiber $\left(x_{0}, x_{1}\right):=q^{(i)^{-1}}(\{y\})$, say, we have the equalities $P^{(i)}\left(x_{0}\right):=P_{0}^{(i+1)}(y)+x_{0} \cdot P_{1}^{(i+1)}(y)$ and $P^{(i)}\left(x_{1}\right):=P_{0}^{(i+1)}(y)+x_{1} \cdot P_{1}^{(i+1)}(y)$. Since $x_{0}$ and $x_{1}$ in fact differ by exactly 1 , we see that $P^{(i)}\left(x_{1}\right)$ can be computed from $P^{(i)}\left(x_{0}\right)$ using a single further $K$-addition. We recover the key butterfly diagram of [LCH14, Fig. 1. (a)] (see also Algorithm 2 above) upon carrying out this procedure recursively, with the convention whereby we flatten (using the space's canonical basis) and interleave the two copies of $S^{(i+1)}$ at each instance. The base case of the recursion consists of the $2^{\ell}$-fold interleaving of the domain $S^{(\ell)}$, into which $P^{(0)}$ 's coefficients are tiled $2^{\mathcal{R}}$ times. The final stage of the butterfly diagram yields the desired evaluation of $P^{(0)}(X)$ on $S^{(0)}$. Algorithm 2 s twiddle factors in its $i^{\text {th }}$ stage, then, are nothing other than the respective first lifts $x_{0}$ of $y$, as the image $y=q^{(i)}\left(x_{0}\right)$ varies throughout $S^{(i+1)}$. These latter elements $x_{0}$, in turn, take precisely the form $\sum_{k=0}^{\ell+\mathcal{R}-i-2} u_{k} \cdot \widehat{W}_{i}\left(\beta_{i+1+k}\right)$, for $u \in \mathcal{B}_{\ell+\mathcal{R}-i-1} \cong S^{(i+1)}$ arbitrary; indeed, we suppress throughout the $0^{\text {th }}$ canonical basis element $\widehat{W}_{i}\left(\beta_{i}\right)=1$ of $S^{(i)}$, since that element is subsumed into each butterfly. We find it interesting that the same polynomial identity underlies both the correctness of [LCH14, § III.] and our above analysis of FRI's folding.

#### Remark 4.15
Though it seems inessential to the proof of Theorem 4.12, it is interesting to note that, for each $i \in\{0, \ldots, \ell-1\}$, the $i^{\text {th }}$-order basis $\left(X_{j}^{(i)}\right)_{j=0}^{2^{\ell-i}-1}$ is itself a novel polynomial basis in its own right, namely that attached to the set of vectors $\left(\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{\ell-1}\right)\right)$. Equivalently, the $i^{\text {th }}$-order subspace vanishing polynomials $\left(\widehat{W}_{k}^{(i)}\right)_{k=0}^{\ell-i-1}$ are simply the subspace vanishing polynomials attached to this latter set of vectors. Indeed, for each $k \in\{0, \ldots, \ell-i-1\},\left\langle\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{i+k-1}\right)\right\rangle \subset \operatorname{ker}\left(\widehat{W}_{k}^{(i)}\right)$ certainly holds, since $\widehat{W}_{k}^{(i)} \circ \widehat{W}_{i}=q^{(i+k-1)} \circ \cdots \circ q^{(i)} \circ \widehat{W}_{i}=\widehat{W}_{i+k}$, which annihilates $\left\langle\beta_{0}, \ldots, \beta_{i+k-1}\right\rangle$ (here, we use the definition of $\widehat{W}_{k}^{(i)}$ and Lemma 4.2). On the other hand, $\widehat{W}_{k}^{(i)}=q^{(i+k-1)} \circ \cdots \circ q^{(i)}$ 's kernel can be of dimension at most $k$ (say by degree considerations), while the vectors $\widehat{W}_{i}\left(\beta_{i}\right), \ldots, \widehat{W}_{i}\left(\beta_{i+k-1}\right)$ are linearly independent (a consequence of Corollary 4.5). We conclude that the above containment is an equality. Finally, the subspace polynomials $\left(\widehat{W}_{k}^{(i)}\right)_{k=0}^{\ell-i-1}$ are normalized. Indeed, using Lemma 4.2 again, we see that, for each $k \in\{0, \ldots, \ell-i-1\}, \widehat{W}_{k}^{(i)}\left(\widehat{W}_{i}\left(\beta_{i+k}\right)\right)=\left(q^{(i+k-1)} \circ \cdots \circ q^{(i)} \circ \widehat{W}_{i}\right)\left(\beta_{i+k}\right)=\widehat{W}_{i+k}\left(\beta_{i+k}\right)=1$ holds.

We now prove the security of Construction 4.11. Our key technical results below (see Propositions 4.20 and 4.23, essentially, jointly constitute a variant of FRI's soundness statement [BBHR18a, § 4.2.2]. Our proofs of these results incorporate - albeit in an attenuated way - various ideas present in [BBHR18a, § 4.2.2] and Ben $+23, \S 8.2$ ]. We also introduce a number of new ideas, which, by and large, pertain to our new folding technique (see Subsection 4.2).

We note that our protocol seems not to admit a security proof which invokes that of FRI in a strictly blackbox manner. Rather, our security argument-and, it would seem, any conceivable analysis of Construction 4.11-must inevitably concern itself not merely with the distance from the code of $\mathcal{A}$ 's initial committed word, but moreover with the consistency of its oracles, and in particular with whether its final oracle value $c$ relates as it should to its initial oracle.

#### Theorem 4.16
The IOPCS $\Pi=$ (Setup, Commit, $\mathcal{P}, \mathcal{V}$ ) of Construction 4.11 is secure.
**Proof**. We define a straight-line emulator $\mathcal{E}$ as follows.

1. By inspecting $\mathcal{A}$ 's messages to the vector oracle, $\mathcal{E}$ immediately recovers the function $f: S^{(0)} \rightarrow L$ underlying the handle $[f]$ output by $\mathcal{A}$.
2. $\mathcal{E}$ runs the Berlekamp-Welch decoder (i.e., Algorithm 1 on the word $f: S^{(0)} \rightarrow L$. If that algorithm outputs $P(X)=\perp$ or if $\operatorname{deg}(P(X)) \geq 2^{\ell}$, then $\mathcal{E}$ outputs $\perp$ and aborts.
3. Otherwise, $\mathcal{E}$ re-expresses the Berlekamp-Welch output polymomial $P(X)=\sum_{w \in \mathcal{B}_{\ell}} t_{w} \cdot X_{\{w\}}(X)$ in coordinates with respect to the novel polynomial basis. $\mathcal{E}$ writes $t\left(X_{0}, \ldots, X_{\ell-1}\right) \in L\left[X_{0}, \ldots, X_{\ell-1}\right]^{\preceq 1}$ for the multilinear whose Lagrange coordinates are $\left(t_{w}\right)_{w \in \mathcal{B}_{\ell}} . \mathcal{E}$ outputs $t\left(X_{0}, \ldots, X_{\ell-1}\right)$ and halts.
We begin by defining various notions, adapting BBHR18a, § 4.2.1]. For each $i \in\{0, \vartheta, \ldots, \ell\}$ (i.e., ascending in $\vartheta$-sized steps), we write $C^{(i)} \subset L^{2^{\ell+\mathcal{R}-i}}$ for the Reed-Solomon code $\mathrm{RS}_{L, S^{(i)}}\left[2^{\ell+\mathcal{R}-i}, 2^{\ell-i}\right]$. We recall that $C^{(i)}$ is of distance $d_{i}:=2^{\ell+\mathcal{R}-i}-2^{\ell-i}+1$. **We write $f^{(0)}, f^{(\vartheta)}, \ldots, f^{(\ell-\vartheta)}$ for the oracles committed by $\mathcal{A}$; we moreover write $f^{(\ell)}: S^{(\ell)} \rightarrow L$ for the identically- $c$ function (here, $c \in L$ is $\mathcal{A}$ 's final FRI message)**. For each $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$, we write $\Delta\left(f^{(i+\vartheta)}, g^{(i+\vartheta)}\right) \subset S^{(i+\vartheta)}$ for the disagreement set between the elements $f^{(i+\vartheta)}$ and $g^{(i+\vartheta)}$ of $L^{2^{\ell+\mathcal{R}-i-\vartheta}}$; that is, $\Delta\left(f^{(i+\vartheta)}, g^{(i+\vartheta)}\right)$ is the set of elements $y \in S^{(i+\vartheta)}$ for which $f^{(i+\vartheta)}(y) \neq g^{(i+\vartheta)}(y)$. We moreover write $\Delta^{(i)}\left(f^{(i)}, g^{(i)}\right) \subset S^{(i+\vartheta)}$ for the fiber-wise disagreement set of the elements $f^{(i)}$ and $g^{(i)}$ of $L^{2^{\ell+\mathcal{R}-i}}$. That is, $\Delta^{(i)}\left(f^{(i)}, g^{(i)}\right) \subset S^{(i+\vartheta)}$ denotes the set of elements $y \in S^{(i+\vartheta)}$ for which the respective restrictions of $f^{(i)}$ and $g^{(i)}$ to the fiber $\left(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)}\right)^{-1}(\{y\}) \subset S^{(i)}$ are not identically equal. We define $d^{(i)}\left(f^{(i)}, C^{(i)}\right):=\min _{g^{(i)} \in C^{(i)}}\left|\Delta^{(i)}\left(f^{(i)}, g^{(i)}\right)\right|$. **We note that, if $d^{(i)}\left(f^{(i)}, C^{(i)}\right)<$ $\frac{d_{i+\vartheta}}{2}$, then $d\left(f^{(i)}, C^{(i)}\right)<\frac{d_{i}}{2}$ a fortiori holds**. (Each offending fiber contributes at most $2^{\vartheta}$ errors; on the other hand, $2^{\vartheta} \cdot\left\lfloor\frac{d_{i+\vartheta}-1}{2}\right\rfloor \leq\left\lfloor\frac{d_{i}-1}{2}\right\rfloor$.) In any case, in case the oracle $f^{(i)}: S^{(i)} \rightarrow L$ is such that $d\left(f^{(i)}, L^{(i)}\right)<\frac{d_{i}}{2}$ happens to hold, we write $\bar{f}^{(i)} \in L^{(i)}$ for the unique codeword for which $d\left(f^{(i)}, \bar{f}^{(i)}\right)<\frac{d_{i}}{2}$.

We record the following key compliance condition:

#### Definition 4.17
For each index $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$, we say that $\mathcal{A}$ 's $i^{\text {th }}$ oracle $f^{(i)}$ is compliant if the conditions $d^{(i)}\left(f^{(i)}, C^{(i)}\right)<\frac{d_{i}}{2}, d\left(f^{(i+\vartheta)}, C^{(i+\vartheta)}\right)<\frac{d_{i+\vartheta}}{2}$, and $\bar{f}^{(i+\vartheta)}=$ fold $\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$ all hold.

We first argue that if any among $\mathcal{A}$ 's oracles $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$ is not compliant, then $\mathcal{V}$ will accept with negligible probability at most. This is exactly Proposition 4.23 below. In order to prepare for that proposition, we record a sequence of lemmas. We begin with the following elementary fact.

#### Lemma 4.18
For each $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$, if $d\left(f^{(i)}, C^{(i)}\right)<\frac{d_{i}}{2}$, then, for each tuple of folding challenges $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right) \in L^{\vartheta}$, we have that $\Delta\left(\right.$ fold $\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$, fold $\left.\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\right) \subset \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)$.

**Proof**. We proceed by contraposition; we fix an element $y \notin \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)$. By definition of that latter set, we conclude immediately that the restrictions $\left.f^{(i)}\right|_{\left(q^{\left.(i+\vartheta-1) \circ \ldots \circ q^{(i)}\right)^{-1}(\{y\})}\right.}=\left.\bar{f}^{(i)}\right|_{\left(q^{\left.(i+\vartheta-1) \circ \ldots \circ q^{(i)}\right)}\right)^{-1}(\{y\})}$ are identically equal. Applying Definition 4.8, we see under this guarantee that, regardless of the challenges $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$, fold $\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)(y)=$ fold $\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)(y)$ necessarily also holds.

We now define a sequence of **bad folding events**. Our definition of $E_{i}$ is case-based, and depends on the status of $f^{(i)}$. If $f^{(i)}$ is within the (fiber-wise) unique decoding radius, then $E_{i}$ captures the event whereby the generic inclusion of Lemma 4.18 becomes strict. Otherwise, $E_{i}$ captures the "bad batching" event whereby fold $\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$ becomes close to $C^{(i+\vartheta)}$.

#### Definition 4.19
For each $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$, we define the bad subset $E_{i} \subset L^{\vartheta}$ as the set of tuples $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right) \in L^{\vartheta}$ for which, as the case may be:

$$
\begin{aligned}
& \text { in case } \boldsymbol{d}^{(\boldsymbol{i})}\left(\boldsymbol{f}^{(\boldsymbol{i})}, \boldsymbol{C}^{(\boldsymbol{i})}\right)<\frac{\boldsymbol{d}_{\boldsymbol{i}+\vartheta}}{\mathbf{2}}: \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right) \not \subset \Delta\left(\text { fold }\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right), \text { fold }\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\right) \
& \text { in case } \boldsymbol{d}^{(\boldsymbol{i})}\left(\boldsymbol{f}^{(\boldsymbol{i})}, \boldsymbol{C}^{(\boldsymbol{i})}\right) \geq \frac{\boldsymbol{d}_{\boldsymbol{i}+\vartheta}}{\mathbf{2}}: d\left(\text { fold }\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right), C^{(i+\vartheta)}\right)<\frac{d_{i+\vartheta}}{2}
\end{aligned}
$$

We now bound the bad subsets $E_{i}$ of Definition 4.19. We recall that $\mu\left(E_{i}\right):=\frac{\left|E_{i}\right|}{|L|^{\vartheta}}$ denotes the probability mass of the set $E_{i} \subset L^{\vartheta}$.
#### Proposition 4.20.
For each $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}, \mu\left(E_{i}\right) \leq \vartheta \cdot \frac{\left|S^{(i+\vartheta)}\right|}{|L|}$ holds.
**Proof**. We treat separately the two cases of Definition 4.19
We **begin with the first case**. We fix an element $y \in \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)$, we moreover write $E_{i}^{y} \subset L^{\vartheta}$ for the set of tuples $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right) \in L^{\vartheta}$ for which $y \notin \Delta\left(\operatorname{fold}\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\right.$, fold $\left.\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\right)$. We argue that $\mu\left(E_{i}^{y}\right) \leq \frac{\vartheta}{|L|}$. This latter claim suffices to complete the proof of the first case; indeed, since $E_{i}=\bigcup_{y \in \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)} E_{i}^{y}$, assuming the claim, we conclude that $\mu\left(E_{i}\right) \leq\left|\Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)\right| \cdot \frac{\vartheta}{|L|} \leq\left|S^{(i+\vartheta)}\right| \cdot \frac{\vartheta}{|L|}$.

For $y \in \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)$ chosen as above, we apply Lemma 4.9 to the words $f^{(i)}$ and $\bar{f}^{(i)}$. Applying that lemma, we see that $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right) \in E_{i}^{y}$ holds if and only if we have the following matrix identity:

$$
0=\left[\bigotimes_{j=0}^{\vartheta-1}\left(1-r_{i+j}^{\prime}, r_{i+j}^{\prime}\right)\right] \cdot\left[M_{y}\right] \cdot\left[\begin{array}{c}
f^{(i)}\left(x_{0}\right)-\bar{f}^{(i)}\left(x_{0}\right)  \tag{40}\
\vdots \
f^{(i)}\left(x_{2^{\vartheta}-1}\right)-\bar{f}^{(i)}\left(x_{2^{\vartheta}-1}\right)
\end{array}\right]
$$

where we again write $\left(x_{0}, \ldots, x_{2^{\vartheta}-1}\right):=\left(q^{(i+\vartheta-1)} \circ \cdots \circ q^{(i)}\right)^{-1}(\{y\})$. Our hypothesis $y \in \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)$ entails precisely that the right-hand vector of 40 is not identically zero. By Lemma 4.9, $M_{y}$ is nonsingular; we conclude that the image of the right-hand vector of 40 under $M_{y}$ is likewise not identically zero. Writing $\left(a_{0}, \ldots, a_{2^{\vartheta}-1}\right)$ for this latter vector-which, we repeat, is not zero-we conclude that $E_{i}^{y} \subset L^{\vartheta}$ is precisely the vanishing locus in $L^{\vartheta}$ of the $\vartheta$-variate polynomial $s\left(X_{0}, \ldots, X_{\vartheta-1}\right):=$ $\sum_{v \in \mathcal{B}_{\vartheta}} a_{\{v\}} \cdot \widetilde{\mathrm{eq}}\left(X_{0}, \ldots, X_{\vartheta-1}, v_{0}, \ldots, v_{\vartheta-1}\right)$ over $L$. Since $s\left(X_{0}, \ldots, X_{\vartheta-1}\right)$ 's values on the cube $\{0,1\}^{\vartheta} \subset L^{\vartheta}$ are exactly $\left(a_{0}, \ldots, a_{2^{\vartheta}-1}\right), s\left(X_{0}, \ldots, X_{\vartheta-1}\right)$ is certainly not zero. Applying the Schwartz-Zippel lemma to $s\left(X_{0}, \ldots, X_{\vartheta-1}\right)$, we conclude that the relevant locus $E_{i}^{y} \subset L^{\vartheta}$ is of mass at most $\mu\left(E_{i}^{y}\right) \leq \frac{\vartheta}{|L|}$, as required.

We **turn to the second case of Definition 4.19** in particular, we assume that $d^{(i)}\left(f^{(i)}, C^{(i)}\right) \geq \frac{d_{i+\vartheta}}{2}$. We define an **interleaved word** $\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$-i.e., a $2^{\vartheta} \times 2^{\ell+\mathcal{R}-i-\vartheta}$ matrix, with entries in $L$-in the following way. For each $y \in S^{(i+\vartheta)}$, writing $M_{y}$ for the matrix guaranteed to exist by Lemma 4.9, we define the column:

$$
\left[\begin{array}{c}
f_{0}^{(i+\vartheta)}(y)  \tag{41}\
\vdots \
f_{2^{\vartheta}-1}^{(i+\vartheta)}(y)
\end{array}\right]:=\left[\quad M_{y}\right] \cdot\left[\begin{array}{c}
f^{(i)}\left(x_{0}\right) \
\vdots \
f^{(i)}\left(x_{2^{\vartheta}-1}\right)
\end{array}\right]
$$

We note that the resulting $2^{\vartheta} \times 2^{\ell+\mathcal{R}-i-\vartheta}$ matrix $\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$-i.e., that whose columns are given by the respective left-hand sides of (41), for $y \in S^{(i+\vartheta)}$ varying-satisfies, for each $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right) \in L^{\vartheta}$,

$$
\text { fold }\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)=\left[\bigotimes_{j=i}^{i+\vartheta-1}\left(1-r_{j}^{\prime}, r_{j}^{\prime}\right)\right] \cdot\left[\begin{array}{ccc}
- & f_{0}^{(i+\vartheta)} & -  \tag{42}\
& \vdots & \
- & f_{2 \vartheta-1}^{(i+\vartheta)} & -
\end{array}\right]
$$

Indeed, this is essentially the content of Lemma 4.9, which we apply here jointly to all elements $y \in S^{(i+\vartheta)}$.
We claim that the interleaved word $\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$ constructed in this way is far from the interleaved code $C^{(i+\vartheta)^{2}{ }^{\vartheta}}$.

#### Lemma 4.21
Under our hypothesis $d^{(i)}\left(f^{(i)}, C^{(i)}\right) \geq \frac{d_{i+\vartheta}}{2}$, we have $d^{2^{\vartheta}}\left(\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}, C^{(i+\vartheta)^{2}}\right) \geq \frac{d_{i+\vartheta}}{2}$. Proof. We fix an arbitrary interleaved codeword $\left(g_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1} \in C^{(i+\vartheta)^{2}{ }^{\vartheta}}$. We define a "lift" $g^{(i)} \in C^{(i)}$ of $\left(g_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$ in the following way. Writing, for each $j \in\left\{0, \ldots, 2^{\vartheta}-1\right\}, P_{j}^{(i+\vartheta)}(X):=\sum_{k=0}^{2^{\ell-i-\vartheta}-1} a_{j, k}$. $X_{k}^{(i+\vartheta)}(X)$ for the polynomial-expressed in coordinates with respect to the $i+\vartheta^{\text {th }}$-order novel polynomial basis-for which $g_{j}^{(i+\vartheta)}=\operatorname{Enc}\left(P_{j}^{(i+\vartheta)}\right)$ holds, we define

$$
P^{(i)}(X):=\sum_{j=0}^{2^{\vartheta}-1} \sum_{k=0}^{\ell-i-\vartheta} a_{j, k} \cdot X_{k \cdot 2^{\vartheta}+j}^{(i)}
$$

that is, $P^{(i)}$ 's list of $i^{\text {th }}$-order coefficients is precisely the $2^{\vartheta}$-fold interleaving of the polynomials $P_{0}^{(i+\vartheta)}(X), \ldots, P_{2^{\vartheta}-1}^{(i+\vartheta)}(X)$ 's respective lists of $i+\vartheta^{\text {th }}$-order coefficients. Finally, we define $g^{(i)}:=\operatorname{Enc}\left(P^{(i)}\right)$.

We argue that the codeword $g^{(i)} \in C^{(i)}$ constructed in this way stands in relation to $\left(g_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$ just as $f^{(i)}$ does to $\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$ (i.e., it also satisfies a matrix identity analogous to 41 for each $y \in S^{(i+\vartheta)}$ ). To prove this, **we fix an arbitrary element $y \in S^{(i+\vartheta)}$; we moreover fix a row-index $j \in\left\{0, \ldots, 2^{\vartheta}-1\right\}$**. We write $\left(j_{0}, \ldots, j_{\vartheta-1}\right)$ for the bits of $j$ (i.e., so that $j=\sum_{k=0}^{\vartheta-1} 2^{k} \cdot j_{k}$ holds). We first note that the functions $g_{j}^{(i+\vartheta)}$ and fold $\left(g^{(i)}, j_{0}, \ldots, j_{\vartheta-1}\right)$ agree identically over the domain $S^{(i+\vartheta)}$. Indeed, this is a direct consequence of Lemma 4.13 and of the construction of $g^{(i)}\left(g_{j}^{(i+\vartheta)}(y)\right.$ 's underlying polynomial's coefficients are the $j^{\text {th }}$ refinement of $g^{(i)}$ 's underlying polynomial's). On the other hand, applying Lemma 4.9 to $y \in S^{(i+\vartheta)}$ and $g^{(i)}$, with the folding tuple ( $j_{0}, \ldots, j_{\vartheta-1}$ ), we see that the dot product between $M_{y}$ 's $j^{\text {th }}$ row and $\left(g^{(i)}\left(x_{0}\right), \ldots, g^{(i)}\left(x_{2^{\vartheta}-1}\right)\right)$ is exactly fold $\left(g^{(i)}, j_{0}, \ldots, j_{\vartheta-1}\right)(y)=g_{j}^{(i+\vartheta)}(y)$, where the latter equality was just argued.

Since $g^{(i)} \in C^{(i)}$ is a codeword, our hypothesis $d^{(i)}\left(f^{(i)}, C^{(i)}\right) \geq \frac{d_{i+\vartheta}}{2}$ applies to it. That hypothesis entails precisely that, for at least $\frac{d_{i+\vartheta}}{2}$ elements $y \in S^{(i+\vartheta)}$, the restrictions $\left.f^{(i)}\right|_{\left(q^{\left.(i+\vartheta-1) \circ \ldots \circ q^{(i)}\right)}\right)^{-1}(\{y\})}$ and $\left.g^{(i)}\right|_{\left(q^{(i+\vartheta-1)} \circ \ldots \circ q^{(i)}\right)^{-1}(\{y\})}$ are not identically equal. For each such $y \in S^{(i+\vartheta)}$, since $M_{y}$ is nonsingular (and since both $f^{(i)}$ and $g^{(i)}$ satisfy (41), we conclude that the columns $\left(f_{j}^{(i+\vartheta)}(y)\right)_{j=0}^{2^{\vartheta}-1}$ and $\left(g_{j}^{(i+\vartheta)}(y)\right)_{j=0}^{2^{\vartheta}-1}$ are in turn unequal. Since $\left(g_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$ was arbitrary, we conclude that $d^{2^{\vartheta}}\left(\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}, C^{(i+\vartheta)^{2^{\vartheta}}}\right) \geq$ $\frac{d_{i+\vartheta}}{2}$.

**Applying Lemma 4.21, we conclude directly that the contraposition of Theorem 2.3 is fulfilled** with respect to the code $C^{(i+\vartheta)} \subset L^{2^{\ell+\mathcal{R}-i-\vartheta}}$, the proximity parameter $e:=\left\lfloor\frac{d_{i+\vartheta}-1}{2}\right\rfloor$, and the interleaved word $\left(f_{j}^{(i+\vartheta)}\right)_{j=0}^{2^{\vartheta}-1}$. That theorem's contraposition immediately implies that the set $E_{i} \subset L^{\vartheta}$ consisting of those tuples $\left(r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right) \in L^{\vartheta}$ for which $d\left(\right.$ fold $\left.\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right), C^{(i+\vartheta)}\right)<\frac{d_{i+\vartheta}}{2}$ holds-and here, we use (42)-is of mass at most $\mu\left(E_{i}\right) \leq \vartheta \cdot \frac{2^{\ell+\mathcal{R}-i-\vartheta}}{|L|}=\vartheta \cdot \frac{\left|S^{(i+\vartheta)}\right|}{|L|}$, as required. This **completes the proof of the proposition**.

#### Proposition 4.22
The probability that any among the bad events $E_{0}, E_{\vartheta}, \ldots, E_{\ell-\vartheta}$ occurs is at most $\frac{2^{\ell+\mathcal{R}}}{|L|}$. Proof. Applying Proposition 4.20, we upper-bound the quantity of interest as:

$$
\frac{\vartheta}{|L|} \cdot\left(\left|S_{\vartheta}\right|+\cdots+\left|S_{\ell}\right|\right)=\frac{\vartheta}{|L|} \cdot\left(2^{\ell+\mathcal{R}-\vartheta}+\cdots+2^{\mathcal{R}}\right) \leq \frac{\vartheta}{|L|} \cdot \frac{2^{\vartheta}}{2^{\vartheta}-1} \cdot 2^{\ell+\mathcal{R}-\vartheta} \leq \frac{2^{\ell+\mathcal{R}}}{|L|}
$$

which completes the proof. In the last two steps, we use the geometric series formula and the inequality $\frac{\vartheta}{2^{\vartheta}-1} \leq 1$ (which holds for each $\vartheta \geq 1$ ), respectively.

In light of Proposition 4.22, we freely assume that none of the events $E_{0}, E_{\vartheta}, \ldots, E_{\ell-\vartheta}$ occurs. Under this assumption, we finally turn to the following key proposition.

#### Proposition 4.23
If any of $\mathcal{A}$ 's oracles is not compliant, then $\mathcal{V}$ accepts with at most negligible probability.
**Proof**. We suppose that at least one of $\mathcal{A}$ 's oracles is not compliant; we write $i^{*} \in\{0, \vartheta, \ldots, \ell-\vartheta\}$ for the index of $\mathcal{A}$ 's highest-indexed noncompliant oracle.

#### Lemma 4.24
For $i^{*} \in\{0, \vartheta, \ldots, \ell-\vartheta\}$ as above, we have $d\left(\right.$ fold $\left.\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \bar{f}^{\left(i^{*}+\vartheta\right)}\right) \geq \frac{d_{i^{*}+\vartheta}}{2}$.
**Proof**. Assuming first that $d^{\left(i^{*}\right)}\left(f^{\left(i^{*}\right)}, C^{\left(i^{*}\right)}\right)<\frac{d_{i^{*}+\vartheta}}{2}$, we write $\bar{f}^{\left(i^{*}\right)} \in C^{\left(i^{*}\right)}$ for the codeword for which $\left|\Delta^{\left(i^{*}\right)}\left(f^{\left(i^{*}\right)}, \bar{f}^{\left(i^{*}\right)}\right)\right|<\frac{d_{i^{*}+\vartheta}}{2}$. We note that $d\left(f^{\left(i^{*}\right)}, \bar{f}^{\left(i^{*}\right)}\right)<\frac{d_{i^{*}}}{2}$ a fortiori holds; by Definition 4.17 and our choice of $i^{*}$, we thus must have in turn $\bar{f}^{\left(i^{*}+\vartheta\right)} \neq \operatorname{fold}\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)$. On the other hand, by Lemma 4.18. $\left|\Delta^{\left(i^{*}\right)}\left(f^{\left(i^{*}\right)}, \bar{f}^{\left(i^{*}\right)}\right)\right|<\frac{d_{i^{*}+\vartheta}}{2}$ implies that $d\left(\right.$ fold $\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)$, fold $\left.\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right)<$ $\frac{d_{i^{*}+\vartheta}}{2}$. Finally, by the reverse triangle inequality, $d\left(\right.$ fold $\left.\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \bar{f}^{\left(i^{*}+\vartheta\right)}\right)$ is at least:

$$
d\left(\bar{f}^{\left(i^{*}+\vartheta\right)}, \text { fold }\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right)-d\left(\text { fold }\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \text { fold }\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\right)
$$

Since $\bar{f}^{\left(i^{*}+\vartheta\right)}$ and fold $\left(\bar{f}^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)$ are unequal codewords in $C^{\left(i^{*}+\vartheta\right)}$, this quantity in turn is greater than or equal to $d_{i^{*}+\vartheta}-\frac{d_{i^{*}+\vartheta}}{2} \geq \frac{d_{i^{*}+\vartheta}}{2}$, and the proof of the first case is complete.

In the case $d^{\left(i^{*}\right)}\left(f^{\left(i^{*}\right)}, C^{\left(i^{*}\right)}\right) \geq \frac{d_{i^{*}+\vartheta}}{2}$, our assumption whereby $E_{i^{*}}$ didn't occur implies, by definition, that $d\left(\right.$ fold $\left.\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), C^{\left(i^{*}+\vartheta\right)}\right) \geq \frac{d_{i^{*}+\vartheta}}{2}$. Since $\bar{f}^{\left(i^{*}+\vartheta\right)} \in C^{\left(i^{*}+\vartheta\right)}$ is a codeword, $d\left(\right.$ fold $\left.\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \bar{f}^{\left(i^{*}+\vartheta\right)}\right) \geq \frac{d_{i^{*}+\vartheta}}{2}$ in particular holds, and the proof is again complete.

#### Lemma 4.25
Whenever its suffix $\left(v_{i^{*}+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right) \in \Delta\left(\operatorname{fold}\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right), \bar{f}^{\left(i^{*}+\vartheta\right)}\right), \mathcal{V}$ rejects.

**Proof**. We fix an iteration of the query phase's outer loop for which the lemma's hypothesis holds. We fix an arbitrary index $i \in\left\{i^{*}, i^{*}+\vartheta, \ldots, \ell-\vartheta\right\}$. If $\mathcal{V}$ rejects before finishing the inner loop $3 \mathrm{~s} i^{\text {th }}$ iteration, then there's nothing to prove. We argue that, conditioned on $\mathcal{V}$ reaching the end of its $i^{\text {th }}$ iteration, we have the inductive conclusion $c_{i+\vartheta} \neq \bar{f}^{(i+\vartheta)}\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ as of the end of that iteration.

In the base case $i=i^{*}, \mathcal{V}$ assigns $c_{i^{*}+\vartheta}:=\operatorname{fold}\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right)\left(v_{i^{*}+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ inline on line 6 On the other hand, the hypothesis of the lemma is precisely fold $\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\left(v_{i^{*}+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right) \neq$ $\bar{f}^{\left(i^{*}+\vartheta\right)}\left(v_{i^{*}+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$; we conclude immediately that $c_{i^{*}+\vartheta} \neq \bar{f}^{\left(i^{*}+\vartheta\right)}\left(v_{i^{*}+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ will hold as of the end of the $i^{* \text { th }}$ iteration, as desired.

We fix an index $i \in\left\{i^{*}+\vartheta, \ldots, \ell-\vartheta\right\}$. As of the beginning of the $i^{\text {th }}$ iteration, by induction, we have the hypothesis $c_{i} \neq \bar{f}^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)$. If $\bar{f}^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)=f^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ moreover holds, then we see immediately that $\mathcal{V}$ will reject on line 5, indeed, in this case $c_{i} \neq \bar{f}^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)=f^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ will hold. We conclude that, conditioned on $\mathcal{V}$ reaching the end of its $i^{\text {th }}$ iteration, we necessarily have $\bar{f}^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right) \neq f^{(i)}\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right)$, or in other words $\left(v_{i}, \ldots, v_{\ell+\mathcal{R}-1}\right) \in \Delta\left(f^{(i)}, \bar{f}^{(i)}\right)$. This guarantee implies a fortiori that $\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right) \in \Delta^{(i)}\left(f^{(i)}, \bar{f}^{(i)}\right)$, by definition of this latter set. Using our assumption whereby the event $E_{i}$ didn't occur, we conclude in turn that $\left(v_{i+\vartheta}, \ldots, v_{\ell-1}\right) \in$ $\Delta\left(\right.$ fold $\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$, fold $\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$ ). Since $\bar{f}^{(i+\vartheta)}=$ fold $\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$ (a consequence of the maximality of $i^{*}$ ), this latter set itself equals $\Delta$ (fold $\left.\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right), \bar{f}^{(i+\vartheta)}\right)$. We conclude that fold $\left(f^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right) \neq \bar{f}^{(i+\vartheta)}\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$, so that, after its assignment on line 6. $\mathcal{V}$ will obtain $c_{i+\vartheta} \neq \bar{f}^{(i+\vartheta)}\left(v_{i+\vartheta}, \ldots, v_{\ell+\mathcal{R}-1}\right)$, thereby preserving the inductive hypothesis.

Carrying through the induction, we see finally that either $\mathcal{V}$ will abort before finishing its inner loop 3 . or else it will have $c_{\ell} \neq \bar{f}^{(\ell)}\left(v_{\ell}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ as of its final check 7 . Since $c=\bar{f}^{(\ell)}\left(v_{\ell}, \ldots, v_{\ell+\mathcal{R}-1}\right)$ holds identically for each $v \in \mathcal{B}_{\mathcal{R}}$ (by definition of this latter oracle), we see that $\mathcal{V}$ will reject its check $c_{\ell} \stackrel{?}{=} c$.

We return to the proposition. Lemma 4.24 guarantees (i.e., assuming $E_{i^{*}}$ doesn't occur) that $c_{i^{*}+\vartheta} \in$ $\Delta\left(\right.$ fold $\left.\left(f^{\left(i^{*}\right)}, r_{i^{*}}^{\prime}, \ldots, r_{i^{*}+\vartheta-1}^{\prime}\right), \bar{f}^{\left(i^{*}+\vartheta\right)}\right)$ will hold with probability at least $\frac{1}{\left|S^{\left(i^{*}+\vartheta\right)}\right|} \cdot \frac{d_{i^{*}+\vartheta}}{2} \geq \frac{1}{2}-\frac{1}{2 \cdot 2^{\mathcal{R}}}$ in each of the verifier's query iterations. By Lemma 4.25, the verifier will reject in each such iteration (i.e., assuming none of the events $E_{i^{*}+\vartheta}, \ldots, E_{\ell-\vartheta}$ occurs). We see that $\mathcal{V}$ will accept with probability at most $\left(\frac{1}{2}+\frac{1}{2 \cdot 2^{\mathcal{R}}}\right)^{\gamma}$, which is negligible (we recall that $\mathcal{R}$ is a positive constant). This completes the proof of the proposition.

In light of Proposition 4.23, we assume that all of $\mathcal{A}$ 's oracles are compliant. Under this assumption, we note first that $d\left(f^{(0)}, C^{(0)}\right)<\frac{d_{0}}{2}$ will hold. We see that Algorithm 1 will terminate successfully in step 2 above. We write $t\left(X_{0}, \ldots, X_{\ell-1}\right) \in L\left[X_{0}, \ldots, X_{\ell-1}\right]^{\preceq 1}$ for the polynomial output by $\mathcal{E}$ in that step.

We now argue that $c=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ will hold. To this end, we apply Definition 4.17 repeatedly. In the base case $i=0$, we note that $\bar{f}^{(0)}$ will be the encoding of $P^{(0)}(X)=\sum_{w \in \mathcal{B}_{\ell}} t(w) \cdot X_{\{w\}}^{(0)}(X)$, precisely by $\mathcal{E}$ 's construction of $(t(w))_{w \in \mathcal{B}_{\ell}}$. On the other hand, for each $i \in\{0, \vartheta, \ldots, \ell-\vartheta\}$, writing $P^{(i)}(X) \in L[X]^{\prec 2^{\ell-i}}$ for the polynomial for which $\operatorname{Enc}\left(P^{(i)}\right)=\bar{f}^{(i)}$ holds, and using our assumption $\bar{f}^{(i+\vartheta)}=$ fold $\left(\bar{f}^{(i)}, r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$, we conclude that $\bar{f}^{(i+\vartheta)}$ will be exactly the encoding of that polynomial $P^{(i+\vartheta)}(X) \in$ $L[X]^{\prec 2^{\ell-i-\vartheta}}$ which results from repeatedly applying to $P^{(i)}(X)$ the conclusion of Lemma 4.13 (with the folding challenges $\left.r_{i}^{\prime}, \ldots, r_{i+\vartheta-1}^{\prime}\right)$. Carrying out the induction, we see that $\bar{f}^{(\ell)}$ will itself be identically equal to $\sum_{w \in \mathcal{B}_{\ell}} \widetilde{\mathrm{eq}}\left(w_{0}, \ldots, w_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot t(w)=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$, so that $c=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ indeed will hold.

We write $\left(r_{0}, \ldots, r_{\ell-1}\right) \in L^{\ell}$ for the evaluation point output by $\mathcal{V}$ and $s \in L$ for $\mathcal{A}$ 's response. To finish the proof, we argue that the probability with which $s \neq t\left(r_{0}, \ldots, r_{\ell-1}\right)$ and $\mathcal{V}$ accepts is negligible. We assume that $s \neq t\left(r_{0}, \ldots, r_{\ell-1}\right)$.

As in Construction 4.11, we write $h\left(X_{0}, \ldots, X_{\ell-1}\right):=\widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, X_{0}, \ldots, X_{\ell-1}\right) \cdot t\left(X_{0}, \ldots, X_{\ell-1}\right)$ (here, $t\left(X_{0}, \ldots, X_{\ell-1}\right)$ refers to what $\mathcal{E}$ extracted). Since $t\left(r_{0}, \ldots, r_{\ell-1}\right)=\sum_{w \in \mathcal{B}_{\ell}} h(w)$, our assumption $s \neq$ $t\left(r_{0}, \ldots, r_{\ell-1}\right)$ amounts to the condition $s \neq \sum_{w \in \mathcal{B}_{\ell}} h(w)$. The soundness analysis of the sumcheck (we refer to Thaler Tha22, § 4.1]) states that, under this very assumption, the probability that the verifier accepts its checks $s_{i} \stackrel{?}{=} h_{i}(0)+h_{i}(1)$ and $s_{\ell}=h\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ holds is at most $\frac{2 \cdot \ell}{|L|}$ over $\mathcal{V}$ 's choice of its folding challenges $\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$. We thus assume that $s_{\ell} \neq h\left(r_{0}^{\prime}, \ldots, r_{\ell-\kappa-1}^{\prime}\right)=\widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$.

Our conclusion whereby $c=t\left(r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$, established above, thus implies that $\mathcal{V}$ will reject its check $s_{\ell} \stackrel{?}{=} \widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right) \cdot c$. This completes the proof of the theorem.


#### Remark 4.26
In our proof of Theorem 4.16 above, our emulator $\mathcal{E}$ runs the Berlekamp-Welch decoder on the adversary-supplied word $f: S^{(0)} \rightarrow L$ (see its step 2). Most analyses of that algorithm (see e.g. Gur06, Rem. 4]) assume inputs guaranteed to reside within the unique decoding radius, and implicitly leave undefined the algorithm's behavior on arbitrary words. The behavior of Algorithm 1 on a general word $f: S^{(0)} \rightarrow L$ is far from obvious. As far as our proof of Theorem 4.16 is concerned, we need merely the guarantee whereby, regardless of its input, Algorithm 1 - and hence also $\mathcal{E}$ - runs in strict polynomial time. (That guarantee follows straightforwardly from Algorithm 1]s description.) Indeed, if $\mathcal{A}$ submits a word $f$ outside of the unique decoding radius, then - as our Propositions 4.22 and 4.23 above show - $\mathcal{V}$ will reject with overwhelming probability in any case, so that $\mathcal{E}$ 's output ultimately doesn't matter. As it happens, it's possible to show that, on input $f$ outside of the unique decoding radius, Algorithm 1 will either return $\perp$ on line 5 or else will return a polynomial $P(X)$ of degree greater than or equal to $2^{\ell}$ (and both of these outcomes can actually happen). We conclude in particular that $\mathcal{E}$ 's test $\operatorname{deg}(P(X)) \stackrel{?}{<} 2^{\ell}$ above is necessary.

### 4.4 Efficiency

We discuss the efficiency of Construction 4.11. We measure $L$-operations throughout. Though the choices $\operatorname{deg}\left(L / \mathbb{F}_{2}\right)=\omega(\log \lambda)$ and $\gamma=\omega(\log \lambda)$ suffice to make that construction's soundness error negligible, we in fact set $\operatorname{deg}\left(L / \mathbb{F}_{2}\right)=\lambda$ and $\gamma=\lambda$. These latter choices make Construction 4.11 exponentially secure, and make its efficiency easier to analyze. As usual, we understand the positive integers $\mathcal{R}$ and $\vartheta$ as constants.


#### Prover cost
In its commitment phase 2 , our prover must use Lin, Chung and Han's additive NTT LCH14 to encode its length- $2^{\ell}$ vector $(t(w))_{w \in \mathcal{B}_{\ell}}$ onto $S^{(0)}$ (see also Algorithm 2 above). For this task, $\ell \cdot 2^{\ell+\mathcal{R}-1}$ $L$-multiplications and $\ell \cdot 2^{\ell+\mathcal{R}} L$-additions suffice (see also Subsection 2.3).

To prepare its sumcheck 2 , the prover must tensor-expand ( $\left.\widetilde{\mathrm{eq}}\left(r_{0}, \ldots, r_{\ell-1}, w_{0}, \ldots, w_{\ell-1}\right)\right)_{w \in \mathcal{B}_{\ell}}$; this task takes $2^{\ell} L$-additions and $2^{\ell} L$-multiplications (recall Subsection 2.1). Our prover can carry out that sumcheck itself also in $O\left(2^{\ell}\right)$ time (we refer to Thaler Tha22, § 4.1]). Our prover is thus linear-time.

#### Verifier cost
To carry out the sumcheck 2 Construction 4.11 s verifier must expend just $O(\ell) L$ operations. It can compute $\widetilde{\text { eq }}\left(r_{0}, \ldots, r_{\ell-1}, r_{0}^{\prime}, \ldots, r_{\ell-1}^{\prime}\right)$ in step 3 in again $O(\ell) L$-operations. During its querying phase 4 , the verifier must finally, for $\gamma=\lambda$ repetitions, make $2^{\vartheta} \cdot \frac{\ell}{\vartheta}=O(\ell)$ queries to the IOP oracle and perform $O\left(2^{\vartheta} \cdot \frac{\ell}{\vartheta}\right)=O(\ell) L$-operations. Its total cost during that phase is thus $O(\lambda \cdot \ell) L$-operations.

#### The BCS transform
In practice, we must use Ben-Sasson, Chiesa and Spooner's transformation BCS16 to turn Construction 4.11 into an interactive protocol in the random oracle model. The resulting compiled protocol imposes further costs on both parties, as we now explain. First, its prover must moreover Merklehash both $f^{(0)}$ during its commitment phase and the positive-indexed oracles $f^{(\vartheta)}, \ldots, f^{(\ell-\vartheta)}$ during its evaluation phase; these commitments represent total work on the order of $O\left(2^{\ell+\mathcal{R}}\right)=O\left(2^{\ell}\right)$ hash invocations.

During the querying phase, both parties must handle Merkle paths. During each query repetition, the total length of all Merkle paths sent (measured in digests) is on the order of $O\left((\ell+\mathcal{R})^{2}\right)=O\left(\ell^{2}\right)$. Since there are $\gamma=\lambda$ total repetitions, the total cost for both parties during the querying phase is thus $O\left(\lambda \cdot \ell^{2}\right)$ hash operations.

---
# 🔖 Categories/Tags: 
- 

# 🔗 References: 
- [[Basefold]]