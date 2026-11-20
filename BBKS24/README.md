# BBKS24: Semirandom planted clique and the restricted isometry property

Błasiok, Buhai, Kothari, Steurer. *Semirandom planted clique and the restricted isometry
property*. FOCS 2024. [arXiv:2404.14159](https://arxiv.org/abs/2404.14159). Numbers refer to the
arXiv version (v2).

The main result is [BBKS24, Theorem 4.1]: in the semirandom model `SRPC(n, k, p)` of
[Charikar, Steinhardt and Valiant](https://arxiv.org/abs/1611.02315), a simple greedy algorithm
lists at most `(1 + o(1)) n / k` cliques of size `k`, one of them the planted one, with probability
at least `0.99`, whenever `k ≥ O(√n log² n · max(1, (p/(1-p))⁴))`. Its case `p = 1/2` is
[BBKS24, Theorem 1.2 (= Theorem 3.1)], the main result of the introduction. The theorem is stated
in [Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks it (see
[Checking a paper](../README.md#checking-a-paper)). The running time is formalized as polynomial
rather than the paper's `O(n^(ω + 1/2))`, a word-RAM bound (see [below](#the-statements)).

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 4.1 | `semirandom_planted_clique` | One polynomial-time algorithm that, given `n`, `k` and the adjacency bits of a graph from `SRPC(n, k, p)` with `C √n log² n max(1, (p/(1-p))⁴) ≤ k ≤ n`, lists at most `(1 + o(1)) n / k` cliques of size `k`, one of them the planted one, with probability at least `0.99`, for every `p ∈ [0, 1)`, every planted set and every adversary. |

* **The model** ([Model.lean](Model.lean), `BBKS24.Adversary`): the planted set `S*` is an
  arbitrary `k`-set and the theorem holds for every one; the edges between `S*` and the rest are
  random and cannot be deleted (unlike in [BKS23](../BKS23)); the rest of the graph is adaptive and
  adversarial. The probability is over the random edges and the coins.
* **`p` is real and not given.** The algorithm's input is `n`, `k` and the adjacency bits, as in
  [BKS23](../BKS23); the guarantee holds for every real `0 ≤ p < 1`. The paper's algorithm uses
  `p`; ours tries a grid of guesses for it. `p = 0` is included.
* **Running time.** The paper's `O(n^(ω + 1/2))` is a word-RAM bound with fast matrix
  multiplication. On multitape Turing machines the theorem asks for polynomial time,
  `O((N + 2)^d)` on inputs of length `N`, with the explicit polynomial `T N = (N + 2)^d` as the
  number of coins (as in [BKS23](../BKS23), to rule out advice through the coin string's length).
* **Uniformity.** One `C`, one `δ` and one threshold for "large enough `n`" serve every `p`,
  every `k`, every `S*` and every adversary, so `p` may be any function of `n`.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### The algorithm

The algorithm ([Algorithm.lean](Algorithm.lean)) is the paper's Algorithm 1, derandomized and
with `p` unknown. For a guess `q` of the edge probability, let `χ` be the `q`-biased character of
a pair, `p₊ = √((1-q)/q)` for an edge and `-p₋ = -√(q/(1-q))` for a non-edge. For every triple
`α` of vertices and every vertex `j`, the algorithm computes the statistic
`⟨Ḡ_α, Ḡ_j⟩ = ∑ᵢ ∏_{a ∈ α} χ(a ~ i) · χ(j ~ i)`, where `a ~ i` is adjacency or equality, so that
every factor is `p₊` on the planted clique. It keeps the vertices with statistic at least
`k p₊⁴ / 2`, then those with at least `k - 1` neighbours among the kept ones
([Statistic.lean](Statistic.lean)). The paper picks `α` at random; the algorithm tries all
triples. The statistic depends only on how many rows `i` have each number of edges among the four
factors, so the test is an inequality between natural numbers (`BBKS24.Alg.selTest_iff`).

The guesses are the points `q = j/M ≥ 1/2` of a grid with `M = 2^b > n³`, `b = 3(⌊log₂ n⌋ + 1)`.
For smaller `p`, the coins add each pair independently with probability `j/M` for every
`j ≤ M/2`, and the algorithm runs at `q = 1/2` on the augmented graph. All candidate sets are
cleaned up as in [BKS23](../BKS23), keeping the `k`-cliques and pruning with threshold
`Δ = ⌊k²/(n L³)⌋ + 1`, `L = ⌊log₂ n⌋ + 1`. [GraphList.lean](GraphList.lean) has the list versions
of the graph notions the algorithm uses.

### Recovery from a good cut

[Statistic.lean](Statistic.lean) is the deterministic part of Sections 3 and 4 (Lemmas 3.2, 3.5,
3.6 and 4.2–4.4). For a triple `α ⊆ S*`, the statistic of `j ∈ S*` is `k p₊⁴` plus a sum over the
cut, and that of `j ∉ S*` is a sum of characters of the random edges of `j` plus the correlation
of the column `H_α = (∏_{a∈α} χ(a ~ i))_{i ∉ S*}` with the vector `u_j` that the adversary
chooses. If the sums over the cut are at most `t₁` and `t₂`, and no vector with entries at most
`p₋` has correlation at least `τ` with `s` columns `H_α`, then some triple `α ⊆ S*` has refined set
exactly `S*` (`BBKS24.exists_refine_eq`). The paper uses Markov's inequality for a random triple;
the proof averages over all triples of `S*`.

### The random cut is good

[Events.lean](Events.lean) bounds the probability of the three hypotheses (`BBKS24.prob_goodCut`),
for `1/2 ≤ q < 1`:

* the sums over the cut, for every triple `α ⊆ S*` and `j ∈ S*` (Lemmas 3.2 and 4.2), by
  Hoeffding's inequality and a union bound; the paper uses Bernstein's inequality, and Hoeffding's
  loses a factor `p₋⁴`, which the paper's bound on `k` absorbs;
* the degrees of the vertices `j ∉ S*` into `S*` (Lemma 4.3), by Hoeffding's inequality;
* few large correlations (Lemmas 3.3–3.5 and 4.4), from the sparse norm bound below, for the triple
  characters, which are orthonormal under the law of a block and bounded by `p₋³`.

### Sparse operator norms

[SparseNorm.lean](SparseNorm.lean) proves the one heavy ingredient: a matrix whose rows are
independent samples of a bounded orthonormal system has small operator norm on all sparse vectors
at once (`BBKS24.SparseNorm.sparse_norm_bound`, the upper half of the restricted isometry property
with constant `2`), and then no vector correlates with many of its columns (Lemma 3.3,
`BBKS24.SparseNorm.card_lt_of_sparseNormLE`, and `BBKS24.SparseNorm.few_large_correlations`). The
paper cites Rudelson and Vershynin; the formal proof follows Haviv and Regev (Section 3), which is
elementary: multiplicative Chernoff bounds, Markov's inequality, Maurey's sampling of columns, and
union bounds over nets at several scales. It carries over to independent rows from any
distribution and to rectangular matrices. The pieces are in [SparseNorm/](SparseNorm).

### Parameters and assembly

[Recovery.lean](Recovery.lean) fixes the parameters `t₁`, `t₂`, `τ` and `s`, and shows that each
event fails with probability at most `1/1200`, so that the planted set is recovered with
probability `1 - 1/400` for all large `n` and every `1/2 ≤ q < 1` (`BBKS24.eventually_recovers`).
[Assembly.lean](Assembly.lean) adds the cleanup, whose threshold the planted set passes with
probability `1 - 1/n` (`BBKS24.Asm.prob_not_noBiclique_le`), and the guesses. For `p ≥ 1/2` the
grid point `q = ⌊pM⌋/M ≤ p` recovers under `G(n, q)`, hence under `G(n, p)` up to the total
variation `C(n, 2)/M ≤ 1/(2n)`. For `p < 1/2` the coins add `G(n, j/M)` with `j = ⌊rM⌋`,
`r = (1/2 - p)/(1 - p)`, and the result is `G(n, p')` with `1/2 - 1/M ≤ p' ≤ 1/2`, where `q = 1/2`
recovers.

### Running time

[PolyTime.lean](PolyTime.lean) certifies every function of the algorithm in polynomial time, with
vertex numbers, grid points and counts in unary, and `k`, the pruning threshold and the integer
test in binary. The algorithm reads at most `n² b` coins, so it runs within
`c ((|x| + 2)^d + |(x, r)|)` steps ([RunTime.lean](RunTime.lean),
`BBKS24.Alg.exists_runsInTime`).

## Map of the files

| Files | Content |
| --- | --- |
| [Model.lean](Model.lean), [Challenge.lean](Challenge.lean) | The model `SRPC(n, k, p)`, randomized algorithms on Turing machines, and the statement. |
| [GraphList.lean](GraphList.lean), [Algorithm.lean](Algorithm.lean) | The algorithm on lists (`BBKS24.Alg.alg`) and what it outputs (`BBKS24.Alg.alg_spec`). |
| [Statistic.lean](Statistic.lean) | The statistic, the selected and refined sets, and recovery from a good cut (`BBKS24.exists_refine_eq`: Lemmas 3.2, 3.5, 3.6, 4.2–4.4). |
| [Events.lean](Events.lean) | The probability that the cut is good (`BBKS24.prob_goodCut`). |
| [SparseNorm.lean](SparseNorm.lean), [SparseNorm/](SparseNorm) | The sparse operator norm bound, following Haviv–Regev: tail bounds (`Tail`), Maurey's sampling (`Maurey`), the scales (`Levels`), the Chernoff event and the union bound over nets (`Core`), the parameters (`Params`); Lemma 3.3. |
| [Recovery.lean](Recovery.lean) | Recovery with probability `1 - 1/400` for all large `n` (`BBKS24.eventually_recovers`). |
| [../Background/RandomGraph.lean](../Background/RandomGraph.lean), [../Background/Pruning.lean](../Background/Pruning.lean), [../Background/Sampling.lean](../Background/Sampling.lean) | Shared with [BKS23](../BKS23): `G(V, p)` as coins on the pairs, the cut and its law, characters, total variation (`abs_binomialRandom_sub_le`), bicliques (`prob_not_noBiclique`); the pruning and Corrádi's bound; chunks of coins and the law of the augmented graph (`sum_mass_coins_sup`). |
| [Assembly.lean](Assembly.lean) | The success probability (`BBKS24.Asm.le_successProb`, `BBKS24.Asm.eventually_le_successProb`). |
| [PolyTime.lean](PolyTime.lean), [RunTime.lean](RunTime.lean) | Polynomial-time certificates (`BBKS24.Alg.algN_polytime`) and the running time (`BBKS24.Alg.exists_runsInTime`). |
| [Solution.lean](Solution.lean) | The theorem, checked by `lake comparator` ([comparator.json](comparator.json)). |

*Formalized with [Claude Code](https://claude.com/claude-code).*
