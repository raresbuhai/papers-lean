# BGHKLMM26: Optimal algorithms and hardness for Max-Cut in bounded degree graphs

Buhai, Ghoshal, Huang, Kothari, Lee, Makarychev, Makarychev. *Optimal algorithms and hardness for
Max-Cut in bounded degree graphs*. SODA 2027. [arXiv:2610.27216](https://arxiv.org/abs/2610.27216).
Numbers refer to the arXiv version (v2).

The results are [BGHKLMM26, Theorem 1.1], a randomized polynomial-time algorithm for Max 2-LIN(2)
that beats Goemans–Williamson by `c/(d log d)` when every variable appears in at most `d`
constraints; its converse under the Unique Games Conjecture, Theorem 1.2 and Corollary 1.3; the
unconditional integrality gap, Theorem 1.4; and the robust Majority is Stablest theorem behind
them, Theorem 7.1. They are stated in [Challenge.lean](Challenge.lean) with the definitions of
[Model.lean](Model.lean) and [Boolean.lean](Boolean.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them (see
[Checking a paper](../README.md#checking-a-paper)). Theorems 1.2 and 1.4 and Corollary 1.3 are
stated with `log d / d`, one logarithm better than the paper's `log² d / d`, because the Gaussian
lemma behind Theorem 7.1 is proved with the error `C √Δ` (see [below](#theorem-71)).

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 1.1 | `max2lin_approximation` | A randomized polynomial-time algorithm for weighted Max 2-LIN(2) whose expected value is at least `(α_GW + c/(d log d))` times the optimum when every variable appears in at most `d` constraints. |
| Theorem 1.2 | `maxCut_hardness` | Assuming the Unique Games Conjecture, telling graphs of maximum degree `d` with Max-Cut value at least `c* - C/d` from those with value at most `s* + C log d / d`, with bounded error in polynomial time, would put `NP` in `BPP`. |
| Corollary 1.3 | `maxCut_inapproximability` | Assuming the Unique Games Conjecture, a randomized polynomial-time algorithm whose expected cut is at least `(α_GW + C log d / d)` times the maximum on graphs of maximum degree `d` would put `NP` in `BPP`. |
| Theorem 1.4 | `maxCut_integrality_gap` | For every large `d`, some graph of maximum degree `d` has Goemans–Williamson SDP value with triangle inequalities at least `c* - C/d` and Max-Cut value at most `s* + C log d / d`. |
| Theorem 7.1 | `robust_majority_is_stablest` | For `ρ ∈ (-1, 0)`, a function `f : {0,1}^R → [0,1]` whose influences are at most `τ` and with `Cut_ρ(f) ≥ arccos ρ / π - η` is within `L¹` distance `C √η + h(τ)` of a linear threshold function, where `h(τ) → 0` as `τ → 0`. |
| The constant `ρ*` | `exists_unique_isGWMinimizer` | The Goemans–Williamson ratio has exactly one minimizer `ρ*` on `[-1, 1)`, which defines `c*` and `s*`. |

* **Max 2-LIN(2)** ([Model.lean](Model.lean)): `n` variables in `{±1}`, constraints `xᵢ xⱼ = b`
  with rational weights `w ≥ 0` on distinct pairs; `n` is in unary, so that the algorithm can
  output an assignment.
* **Randomized algorithms** (`BGHKLMM26.RunsInTime`): a multitape Turing machine reading the
  instance and `T |x| = (|x| + 2)^k` coin flips; the expectation is over the coins
  (`BGHKLMM26.coinMean`).
* **Max-Cut** (`BGHKLMM26.maxCutGap`): simple graphs encoded by their adjacency tables; the gap
  problem restricted to maximum degree at most `d`. `c* = (1 - ρ*)/2` and `s* = arccos ρ* / π` for
  the minimizer `ρ*` of the Goemans–Williamson ratio (`BGHKLMM26.exists_unique_isGWMinimizer`).
* **The Unique Games Conjecture** (`UniqueGames.UGC`, shared with the other papers in
  `Background/UniqueGames.lean`) is a hypothesis, in the form of Conjecture 4.10 (simple
  bi-regular bipartite instances), except that it asks for one number of labels rather than all
  large ones (weaker, and enough).
* **The conclusion** of Theorem 1.2 is that the gap problem in complexitylib's `PromiseBPP` implies
  `NP ⊆ BPP` for every encoding: it rules out bounded-error randomized algorithms.
* **Constants.** In Theorem 1.1, one `c > 0` for all `d ≥ 2`; in Theorem 1.2, Corollary 1.3 and
  Theorem 1.4, one `C` and one `d₀` for all `d ≥ d₀`.
* **Corollary 1.3** uses the algorithms and the guarantee of Theorem 1.1 (expected value over the
  coins), on Max 2-LIN(2) instances that are unweighted graphs (`BGHKLMM26.IsMaxCutInstance`), so
  it is the converse of Theorem 1.1. The algorithm may depend on `d`.
* **The SDP** of Theorem 1.4 (`BGHKLMM26.IsSDPSolution`, `BGHKLMM26.sdpValue`): unit vectors in
  `ℝⁿ` with the triangle inequalities of Section 3, valued by the average of `‖vᵢ - vⱼ‖² / 4` over
  the edges. The theorem exhibits a solution, and also states the integrality gap
  `MaxCut ≤ (α_GW + C log d / d) · SDP` that follows. Theorem 1.4 is unconditional.
* **Functions on the cube** ([Boolean.lean](Boolean.lean)), for Theorem 7.1, as in Sections 4 and
  7.1 of the paper: the influence `Inf_i(f) = ∑_{S ∋ i} f̂(S)²` for the characters
  `∏_{i ∈ S} (2xᵢ - 1)` (`BGHKLMM26.cubeInfluence`), `Cut_ρ(f) = E[f(X) + f(Y) - 2 f(X) f(Y)]`
  over `ρ`-correlated pairs (`BGHKLMM26.cubeCut`), and the LTFs `1(∑ᵢ wᵢ (2xᵢ - 1) + θ ≥ 0)`
  (`BGHKLMM26.IsCubeLTF`). `dist(f, ℒ_R) ≤ e` is stated as an LTF within `L¹` distance `e`, which
  is the same since there are finitely many LTFs; `C` and `h` depend only on `ρ`.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### Theorem 1.1

The analysis of Section 3 is over the reals: the Goemans–Williamson ratio, its unique minimizer
`ρ* ∈ (-4/5, -1/2)`, `0 < α_GW < 1`, the gap `κ` outside a rational window, and hyperplane
rounding (Lemma 3.3, [GW.lean](GW.lean), [Baseline.lean](Baseline.lean)); Sheppard's formula
through Owen's `T` function (from TauCeti), Gaussian calculus and the smoothed correlations
(Fact 3.9, [../Background/Gaussian.lean](../Background/Gaussian.lean),
[../Background/GaussianCalculus.lean](../Background/GaussianCalculus.lean),
[../Background/ArcsinSeries.lean](../Background/ArcsinSeries.lean)); and votes and energy
(Lemmas 3.10, 3.12), strips (Lemmas 3.13–3.15), the gain (Lemmas 3.16–3.20, Theorem 3.2) and the
two roundings (Lemmas 3.4, 3.5) ([Energy.lean](Energy.lean), [Strip.lean](Strip.lean),
[Gain.lean](Gain.lean), [Ideal.lean](Ideal.lean)).

The machine ([SDP.lean](SDP.lean), [Factor.lean](Factor.lean), [Numerics.lean](Numerics.lean),
[Algorithm.lean](Algorithm.lean)) solves the SDP with the sum-of-squares solver of
[../Background/SumOfSquares](../Background/SumOfSquares/README.md), obtains the vectors from a
positive definiteness test, draws Gaussians from coins through `Φ`, and rounds the projections to
`2^-p`. Its analysis ([Exact.lean](Exact.lean), [Accuracy.lean](Accuracy.lean),
[Robust.lean](Robust.lean), [Opt.lean](Opt.lean), [Assembly.lean](Assembly.lean)) shows that its
choices are exact, its projections accurate and its signs robust, and that `opt ≥ W/2`, which
gives the mean value (`BGHKLMM26.Alg.alg_mean`). Polynomial-time certificates give the running
time ([Run.lean](Run.lean), [PolyTime.lean](PolyTime.lean), [RunTime.lean](RunTime.lean),
`BGHKLMM26.Alg.exists_runsInTime`).

### Theorem 1.2

Assuming Theorem 7.1 (`BGHKLMM26.Hard.RobustMIS`, robust Majority is Stablest with the error
`C √η`), [Hardness/Main.lean](Hardness/Main.lean) proves the theorem
(`BGHKLMM26.Hard.maxCut_hardness_of_robustMIS`); [RobustMIS/Final.lean](RobustMIS/Final.lean)
proves Theorem 7.1 (`BGHKLMM26.RobustMIS.robustMIS`). The reduction
([Hardness/Defs.lean](Hardness/Defs.lean)) is the KKMO graph (Figure 5.1) without noise, sparsified
by a machine that decodes edges from blocks of coins and simplifies greedily with degree cap `d`.

* **Correlation and constraints.** The machine samples pairs with a dyadic correlation `ρ_d` close
  to `ρ*`, with the cut value Lipschitz in `ρ` and Theorem 7.1 applied at `ρ*`, and reads the
  index of a constraint modulo the number of constraints from enough coins.
* **The dense graph** has no noise `μ`: Majority is Stablest with low-degree influences gives its
  soundness, and the robust inverse is applied to the smoothed `T_{1-γ} g_u`. Majority is Stablest
  is OpenAI's ([../Imported/OAI](../Imported/OAI)), with its cut form for `ρ < 0` (Corollary 4.3).
* **The sparsification** succeeds with probability `9/10` on each side, so that it composes with
  a bounded-error algorithm (`BGHKLMM26.Hard.RandReducible`); `PromiseBPP` is closed under
  randomized reductions with two-sided error.
* **The multiscale union bound** (Lemma 6.6) starts at the scale `λ = K log D / D`
  (`BGHKLMM26.Hard.lam`), at which Bernstein's bound beats the Hamming balls of radius `C₁ √η`
  (`BGHKLMM26.Hard.radius_entropy_le`). The union over the tuples of LTFs is bounded by
  `exp(n / A(d))`, with the number of labels `R` large depending on `d` through the alphabet
  enlargement `π ↦ π × id`.

### Corollary 1.3

[Inapprox.lean](Inapprox.lean) (`BGHKLMM26.Inapprox.of_hardness`): a graph becomes a Max-Cut
instance in polynomial time, with one constraint per edge; the algorithm is run a number of times
depending on `d`, accepting if one of its cuts crosses more than a rational fraction between
`s` and `α c` of the edges. No-instances are never accepted, and by Markov's inequality each run
accepts a yes-instance with probability bounded below, so this solves Theorem 1.2's gap problem in
`PromiseBPP`.

### Theorem 1.4

[IntGap/Main.lean](IntGap/Main.lean) (`BGHKLMM26.IntGap.integrality_gap`): the reduction of
Theorem 1.2 applied to a Unique Games integrality gap instance. With probability `9/10` its output
is a no-instance, and with probability `9/10` an SDP solution for all its vertices keeps its value
on the sampled edges; some output does both.

* **The instance** ([IntGap/Cube.lean](IntGap/Cube.lean), [IntGap/Instance.lean](IntGap/Instance.lean))
  is Khot and Vishnoi's (KV15, Section 3) in a bipartite form: right vertices are Boolean functions
  on `{0,1}^k` modulo characters, left vertices a class and a set `Z` of `z` points, one constraint
  for each function vanishing outside `Z`. It is simple and bi-regular, and its tuples `T_{P,s}`
  (tensor squares of truth tables) are within `1 - 4z/2^k` along two constraints at one left
  vertex. Its value is at most `2^{-kz/(8·2^k)}`, by the label-extended graph and
  hypercontractivity on the cube of truth tables ([IntGap/Sound.lean](IntGap/Sound.lean)).
* **The SDP solution** ([IntGap/Tensor.lean](IntGap/Tensor.lean), [IntGap/KS.lean](IntGap/KS.lean),
  [IntGap/Mix.lean](IntGap/Mix.lean)): the long-code kernel (scales of tensor powers of the tuples)
  and Khot and Saket's local argument (FOCS 2009) for three points. At each scale, single-linkage
  clusters at radius `2^{-(i+1)T}` and labels matched through the clusters give correlations with
  the signed triangle inequalities, within `4/Δ + 2^{-T}` of the kernel. Mixing with the identity,
  `(1-δ) K + δ I`, makes them exact, and the vectors come from a factorization of the Gram matrix.
  On the dense graph of the reduction the kernel is at most `ρ (1 - 4zs/2^k)`, so the SDP value is
  at least `(1 - ρ)/2` up to `δ` and `4zs/2^k` ([IntGap/Dense.lean](IntGap/Dense.lean)).
* **The sampled graph** ([IntGap/Sample.lean](IntGap/Sample.lean),
  [IntGap/SoundAt.lean](IntGap/SoundAt.lean)): the completeness of the sparsification for an edge
  score in `[0, 1]`, applied to the SDP value, and the soundness of Theorem 1.2 for a given instance
  with enough labels and small value.

### Theorem 7.1

The robust Majority is Stablest theorem rests on the Gaussian lemma with the error `C √Δ`
(Lemma 7.4), which the paper takes from Heilman's robust Borell inequality. Here it is proved from
scratch ([RobustMIS/](RobustMIS), see its [README](RobustMIS/README.md)), in two steps. Eldan's
published estimate of the Gaussian noise stability deficit (Invent. Math. 2015), with the error
`C √(Δ log(e/Δ))`, brings the function close to the halfspace; it is proved by Eldan's argument in
analytic form (the heat flow, the deficit and drift identities, the static Gaussian bounds, the
bootstrap). A local spectral argument at the halfspace then gives the error `C √Δ` (the Mehler
kernel along its normal, and the spectral gap of the noise operator from TauCeti's Hermite basis).
With that error, the multiscale union bound of Lemma 6.6 starts at the scale `K log d / d`.

The transfer to the cube is by an invariance principle for pairs of polynomials (Bonami,
Lindeberg, mollification), in place of the anti-concentration of regular forms and Mossel–Neeman's
Lemma 7.3; then come the truncation and the smoothing removal, with a bound for regular LTFs in
place of Peres's bound.

[RobustMIS/Statement.lean](RobustMIS/Statement.lean)
(`BGHKLMM26.RobustMIS.Statement.robust_majority_is_stablest_cube`) states Theorem 7.1 as proved for
Theorem 1.2 (`BGHKLMM26.RobustMIS.robustMIS`) in the definitions of [Boolean.lean](Boolean.lean).
They agree with those of the proof: OpenAI's Walsh characters are `(-1)^{|S|} χ_S`, and
`corrAverage` is the expectation over `ρ`-correlated pairs. The proof gives, for each `ξ > 0`, a
`τ` below which the error is `C √η + ξ`; `h(τ)` is the least such `ξ`.

## Map of the files

| Files | Content |
| --- | --- |
| [Model.lean](Model.lean), [Boolean.lean](Boolean.lean), [Challenge.lean](Challenge.lean) | Max 2-LIN(2) and Max-Cut, randomized algorithms, the SDP, functions on the cube, and the statements. |
| [GW.lean](GW.lean), [Baseline.lean](Baseline.lean) | The Goemans–Williamson ratio: its unique minimizer `ρ* ∈ (-4/5, -1/2)`, `0 < α_GW < 1`, the gap `κ` outside a rational window, and hyperplane rounding (Lemma 3.3). |
| [../Background/Gaussian.lean](../Background/Gaussian.lean), [../Background/GaussianCalculus.lean](../Background/GaussianCalculus.lean), [../Background/ArcsinSeries.lean](../Background/ArcsinSeries.lean) | Sheppard's formula through Owen's `T` function (TauCeti), Gaussian calculus, the smoothed correlations (Fact 3.9). |
| [Energy.lean](Energy.lean), [Strip.lean](Strip.lean), [Gain.lean](Gain.lean), [Ideal.lean](Ideal.lean) | Section 3: votes and energy (Lemmas 3.10, 3.12), strips (3.13–3.15), the gain (3.16–3.20, Theorem 3.2), the two roundings (3.4, 3.5). |
| [SDP.lean](SDP.lean), [Factor.lean](Factor.lean), [Numerics.lean](Numerics.lean), [Algorithm.lean](Algorithm.lean) | The machine: the SDP by the sum-of-squares solver, the vectors from a positive definiteness test, Gaussians from coins through `Φ`, projections rounded to `2^-p`. |
| [Exact.lean](Exact.lean), [Accuracy.lean](Accuracy.lean), [Robust.lean](Robust.lean), [Opt.lean](Opt.lean), [Assembly.lean](Assembly.lean) | Exactness of the machine's choices, accuracy of its projections, robustness of the signs, `opt ≥ W/2`, and the mean value (`BGHKLMM26.Alg.alg_mean`). |
| [Run.lean](Run.lean), [PolyTime.lean](PolyTime.lean), [RunTime.lean](RunTime.lean) | Polynomial-time certificates and the running time of Theorem 1.1 (`BGHKLMM26.Alg.exists_runsInTime`). |
| [Hardness/Defs.lean](Hardness/Defs.lean) | The reduction: the KKMO graph (Figure 5.1) without noise, LTFs, `Cut_ρ`, the statement of Theorem 7.1, and the machine (edges decoded from blocks of coins, greedy simplification with degree cap `d`). |
| [Hardness/TwoSided.lean](Hardness/TwoSided.lean), [Hardness/Enlarge.lean](Hardness/Enlarge.lean) | `PromiseBPP` is closed under randomized reductions with two-sided error; the alphabet enlargement `π ↦ π × id`. |
| [../Imported/OAI](../Imported/OAI), [Stablest.lean](Stablest.lean), [Hardness/KKMO.lean](Hardness/KKMO.lean) | Majority is Stablest (from OpenAI's library), its cut form for `ρ < 0` (Corollary 4.3), and the KKMO completeness and soundness (Lemmas 5.1, 5.2, 5.4), with low-degree influences. |
| [Hardness/LTF.lean](Hardness/LTF.lean), [Hardness/KKMORobust.lean](Hardness/KKMORobust.lean) | LTFs: at most `(2^R + 1)^(R+1)` of them (Chow's theorem), Corollary 4.6, Claim 4.7, Lemma 4.8; the robust inverse of soundness (Lemma 5.3) from Theorem 7.1. |
| [Hardness/Decoder.lean](Hardness/Decoder.lean), [Hardness/Coins.lean](Hardness/Coins.lean), [Hardness/Glue.lean](Hardness/Glue.lean) | The law of a decoded edge against the KKMO graph; the coins as independent blocks. |
| [Hardness/Concentration.lean](Hardness/Concentration.lean), [Hardness/SparsifyMain.lean](Hardness/SparsifyMain.lean) | Hoeffding, Bernstein, binomial tails, Hamming balls; the sparsification (Section 6) for an abstract law. |
| [Hardness/Machine.lean](Hardness/Machine.lean), [Hardness/Main.lean](Hardness/Main.lean) | The reduction in polynomial time; completeness and soundness of the reduction, and Theorem 1.2 from Theorem 7.1. |
| [Inapprox.lean](Inapprox.lean) | Corollary 1.3 from Theorem 1.2. |
| [IntGap/Cube.lean](IntGap/Cube.lean), [IntGap/Instance.lean](IntGap/Instance.lean), [IntGap/Sound.lean](IntGap/Sound.lean) | Khot and Vishnoi's instance in a bipartite form, its tuples, and its value. |
| [IntGap/Tensor.lean](IntGap/Tensor.lean), [IntGap/KS.lean](IntGap/KS.lean), [IntGap/Mix.lean](IntGap/Mix.lean), [IntGap/Dense.lean](IntGap/Dense.lean) | The long-code kernel, Khot and Saket's local argument, the mixing with the identity, and the kernel on the dense graph. |
| [IntGap/Sample.lean](IntGap/Sample.lean), [IntGap/SoundAt.lean](IntGap/SoundAt.lean), [IntGap/Main.lean](IntGap/Main.lean) | Completeness of the sparsification for the SDP value, soundness for a given instance, and Theorem 1.4. |
| [RobustMIS/](RobustMIS) | Theorem 7.1: the Gaussian lemma in two steps, the invariance principle, the truncation and the smoothing removal (see its [README](RobustMIS/README.md)). |
| [RobustMIS/Statement.lean](RobustMIS/Statement.lean) | Theorem 7.1 in the definitions of [Boolean.lean](Boolean.lean). |
| [Solution.lean](Solution.lean) | The six theorems, checked by `lake comparator` ([comparator.json](comparator.json)). |

*Formalized with Claude (Anthropic).*
