module

public import BHSV25.Model
public import BHSV25.BK.Main
public import BHSV25.UG.Bridge

/-!
# The hardness of almost-bipartite independent set

[BHSV25, Fact 8.1], the starting point of every hardness reduction in the paper: Bansal and Khot
proved, assuming the Unique Games Conjecture, that for all small `ε, γ > 0` it is NP-hard to tell
graphs with two disjoint independent sets of `(1/2 - ε) n` vertices each from graphs with no
independent set of `γ n` vertices; Bafna, Hsieh and Kothari note that the graphs can have maximum
degree `o(n)`.

This file states it as `BHSV25.BansalKhot`, for graphs of maximum degree at most `η n` for every
`η > 0`, and proves it from the Unique Games Conjecture on graphs (`UniqueGames.KhotUGC`;
`BHSV25.bansalKhot`): the double cover and a regularization (`BHSV25/UG/`) give hardness on
left-regular bipartite instances whose parallel constraints agree, from which the reduction of
`BHSV25/BK/` starts (the route below). The hardness theorems of `Challenge.lean` assume the
conjecture itself, and their proofs go through this statement.

Bansal and Khot's test, as described by Manurangsi (arXiv:1705.03581, Section 4.2): pick
`x ∈ {0,1}^R` and a set `D` of coordinates, each in `D` with probability `ε_T`; the test accepts if
the long codes `f_{v_1}, …, f_{v_t}` of `t` random neighbours of a random `u` are all constant,
with the same value, on the subcube `C_D(x) = {y : y_j = x_j for j ∉ D}`. Soundness rests on
Mossel, O'Donnell and Oleszkiewicz's "It Ain't Over Till It's Over" [MOO10, Theorem 4.9]. The
formalization is a self-contained variant of their reduction, with these choices:

* One vertex per random string `(u, k, z, a)`: by folding, the second accepting configuration of
  `(u, k, z, a)` is the first of `(u, k, ¬z, a)`, so the yes-case independent sets are
  `{accepted, z_{σ(u)} = b}`.
* Soundness through the averaged long codes `g_u` and the single-function theorem, with the
  KKMO decoding of BGHKLMM26, instead of the multi-function form with cross-influences
  (Manurangsi's Theorem 11, after Svensson 2013); `t` enters only through the `t`-th moment.
* Free coordinates `{j : a_j = 0}` for uniform `a ∈ [M]^R` (density `1/M`), so all vertices have
  the same weight and the graph is unweighted with no replication.
* Self-conflicting vertices (all coordinates free) are discarded in the soundness; that parallel
  constraints agree is used there.
* The instances are left-regular with agreeing parallel constraints, not simple and bi-regular:
  right-regularity is never used, and parallel constraints with the same table are harmless.
  These are the instances that the conjecture on graphs gives after the double cover and a
  regularization (step 1).
* The left vertices are capped at the number of constraints, so the output has polynomial size
  on every input; `R = 0` (no yes-instances) is handled by a constant map.

## The route

1. **From the conjecture to left-regular instances** (`BHSV25/UG/`,
   `BHSV25.UG.lrHard_of_khotUGC`): the double cover (`BHSV25/UG/Cover.lean`) at most doubles the
   value, and Khot and Regev's regularization (`BHSV25/UG/Regular.lean`) moves it by at most
   `1/ℓ`; `BHSV25/UG/Bridge.lean` composes them.
2. **The reduction** (`BHSV25/BK/Graph.lean`, `BHSV25/BK/Vertices.lean`,
   `BHSV25/BK/Copies.lean`): one vertex `(u, k, z, a)` per random string, two vertices adjacent
   when they demand incompatible values of a folded long code, and `⌈1/η⌉ + 1` disjoint copies for
   the maximum degree.
3. **Completeness** (`BHSV25/BK/Complete.lean`): the accepted vertices with `z_{σ(u)} = b`, for
   `b = 0, 1`, are two disjoint independent sets.
4. **Soundness** (`BHSV25/BK/Sound.lean`): an independent set gives folded long codes under which
   its vertices accept, and their averages `g_u` have small subcube moments unless `u` has an
   influential coordinate, which the decoding (`BHSV25/BK/Basic.lean`) makes rare.
5. **It Ain't Over Till It's Over** (`BHSV25/BK/AintOver.lean`, proved in
   `BHSV25/BK/AintProof.lean`): an invariance principle between the three-valued ensemble of a
   random subcube and uniform signs (`BHSV25/BK/Ensemble.lean`, `BHSV25/BK/Invariance*.lean`), and
   reverse hypercontractivity on the cube (`BHSV25/BK/HyperReverse.lean`), with no Gaussian space.
6. **Parameters, assembly and polynomial time** (`BHSV25/BK/Main.lean`,
   `BHSV25/BK/Machine.lean`).

References:
* N. Bansal, S. Khot, *Optimal long code test with one free bit*, FOCS 2009.
* M. Bafna, J.-T. Hsieh, P. K. Kothari, *Rounding large independent sets on expanders*, STOC 2025.
* P. Manurangsi, *Inapproximability of maximum biclique problems, minimum k-cut and densest
  at-least-k-subgraph from the small set expansion hypothesis*, arXiv:1705.03581.
* E. Mossel, R. O'Donnell, K. Oleszkiewicz, *Noise stability of functions with low influences:
  invariance and optimality*, Annals of Mathematics 171 (2010) [MOO10].
* S. Khot, O. Regev, *Vertex cover might be hard to approximate to within 2 - ε*, JCSS 74 (2008)
  [KR08].
-/

@[expose] public section

namespace BHSV25

open Cslib.Complexity

open Classical in
/-- Every vertex has at most `η n` neighbours. -/
def Graph.MaxDegreeLE (G : Graph) (η : ℝ) : Prop := ∀ v, (G.2.degree v : ℝ) ≤ η * G.1

/-- The **gap problem of Bansal and Khot** with parameters `ε`, `γ` and `η`, on graphs of maximum
degree at most `η n`: the yes-instances have two disjoint independent sets of at least
`(1/2 - ε) n` vertices each, and the no-instances have no independent set of `γ n` vertices. (The
no-instances also ask `γ ≤ 1/2 - ε`, so that the two sides are disjoint.) -/
noncomputable def bkGap (ε γ η : ℝ) : PromiseProblem Graph where
  yes := {G | G.MaxDegreeLE η ∧ ∃ I J : Finset (Fin G.1), Disjoint I J ∧
    G.2.IsIndepSet (I : Set (Fin G.1)) ∧ G.2.IsIndepSet (J : Set (Fin G.1)) ∧
    (1 / 2 - ε) * G.1 ≤ I.card ∧ (1 / 2 - ε) * G.1 ≤ J.card}
  no := {G | G.MaxDegreeLE η ∧ γ ≤ 1 / 2 - ε ∧
    ∀ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) → (I.card : ℝ) < γ * G.1}
  disjoint := Set.disjoint_left.2 fun G hyes hno ↦ by
    obtain ⟨-, I, -, -, hI, -, hIc, -⟩ := hyes
    obtain ⟨-, hγ, hno⟩ := hno
    have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    linarith [hno I hI, mul_le_mul_of_nonneg_right hγ hn]

/-- **[BHSV25, Fact 8.1]**: for all small enough `ε, γ > 0` and every `η > 0`, the gap problem
`bkGap ε γ η` is NP-hard, under deterministic polynomial-time reductions from every problem in
`NP`. -/
def BansalKhot : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε γ η : ℝ, 0 < ε → ε ≤ ε₀ → 0 < γ → γ ≤ ε₀ → 0 < η →
    PromiseProblem.NPHard encGraph (bkGap ε γ η)

/-- **Bansal and Khot's theorem**: the Unique Games Conjecture implies [BHSV25, Fact 8.1]. -/
theorem bansalKhot (hUGC : UniqueGames.KhotUGC) : BansalKhot :=
  BK.bansalKhot_of (UG.lrHard_of_khotUGC hUGC) BK.itAintOver

end BHSV25
