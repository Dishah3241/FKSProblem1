# FKS Problem 1 on at most twice the dimension vertices

A Lean-checked proof of FKS Problem 1 for graphs on at most `2d` vertices: **for every
`d ≥ 4`, every finite simple graph on at most `2d` vertices, of maximum degree at most
`d`, with no connected component isomorphic to `K_{d+1}`, has spherical dimension at
most `d`**.
The question is from Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*,
J. Combin. Theory Ser. A 171 (2020), 105146,
[§5, Problem 1](https://arxiv.org/abs/1802.03092).

> A **spherical placement** is an injective map into Euclidean ℝᵈ with every vertex on
> the sphere of radius `1/√2` about the origin and every edge at distance exactly one.
> Non-edges are unconstrained and may also have length one. On this sphere, edge
> distance one is equivalent to orthogonality.

The research audience is discrete geometers and extremal graph theorists studying spherical
unit-distance representations, graph dimension and bounded-degree embedding problems.

**Without the vertex bound the answer is no.** Mishra and Senthilkumar (2026, [anshM123/FKS-Problem-One](https://github.com/anshM123/FKS-Problem-One)) showed
that the square of the nine-cycle, a connected 4-regular graph that is not `K₅`, has no spherical
representation in `ℝ⁴`, with a Lean proof against this question's formal-conjectures statement (finding A58;
the manager compiled it). It has nine vertices, so the bound proved here is sharp at `d = 4`: every graph on
at most `2d = 8` vertices works, and the first counterexample has `2d + 1`. The question for `d ≥ 5` is
still open. `Problem1` and `Problem1At4` stay stated here, carrying the template's open mark, since this
repository does not contain the disproof.
The source's exception “except `K_{d+1}`” is read componentwise (A40): `K_{d+1}` together
with an isolated vertex is a counterexample to a literal exception of only the whole graph
`K_{d+1}`. Its clique forces `d + 1` nonzero orthogonal vectors in ℝᵈ. Under the degree
bound, excluding a complete component of order `d + 1` is equivalent to excluding a
clique of that order; the repository proves this bridge. “Maximum degree `d`” is read as
at most `d`, consistent with the source's bounded-degree proposition.

**Novelty.** This is a Lean-checked proof of FKS Problem 1 for graphs on at most `2d` vertices. It follows from
published results — FKS Lemma 13 with Tutte's theorem, which is the route taken here, or equitable colouring
(Hajnal–Szemerédi, Chen–Lih–Wu) — and a two-lineage literature check found it stated nowhere. It is not claimed as a
new result. The unrestricted problem is false at `d = 4` (see above).

| | |
|---|---|
| Proof | `Problem1Bounded.proof` is proved for every `d ≥ 4`; no `sorry` in the development; only `propext`, `Classical.choice` and `Quot.sound` |
| General problem | `Problem1` and `Problem1At4` are Prop definitions, not admitted theorems; both are false, refuted at `d = 4` by Mishra and Senthilkumar (2026, [anshM123/FKS-Problem-One](https://github.com/anshM123/FKS-Problem-One)) |
| Comparator | Accepted by Lean and NanoDa in the local macOS run ([record](docs/comparator-2026-09-29.md)) |
| Library | [GraphDimension at the pinned revision](https://github.com/Dishah3241/GraphDimension/tree/db8062bb838b4ac31ea4d5648ea2a8b51685cfa0); main proof `SimpleGraph.SphereEmbeddable.of_card_le_two_mul` |
| Statement review | Two statements authored blind and proved equivalent in [Stage1](FKSProblem1/Stage1/Equivalence.lean); owner signed [Compass rows 1–15](docs/compass.md) on 2026-09-28 |
| Release review | opencode (muse-spark-1.3), run `20260929-143246-251327e6`: "publish after fixes", both fixes applied ([record](docs/review-2026-09-29.md)) |
| Blueprint | [Source](blueprint/src/content.tex); publication pending |
| `formal-conjectures` | Statement authored here; the manager's parallel open-statement submission is separate from this bounded proof |
| Mathlib | Reusable proof machinery is in GraphDimension; no Mathlib PR for this release |
| Palomar | [PALOMAR-2026-09-30-000028](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-30-000028&version=1), registered at commit `2779dea`, trust level high ([record](docs/palomar-2026-09-29.md)) |

**Review.** A release review by opencode (muse-spark-1.3), a model family that wrote none of this proof or its
library leaves, found the statement faithful, the target right and every gate passing, and asked for two
documentation fixes, both applied ([record](docs/review-2026-09-29.md)). grok is not independent here: it wrote
GraphDimension's L1 and M1 leaves and this repository's fidelity companions. The managing agent, Claude Code (Claude
Opus 5.5), contributed integration and fixes, including the bridge's location, layering and release coordination.

## The statement

[InlineFKSProblem1.lean](FKSProblem1/Standalone/Mathlib/InlineFKSProblem1.lean) imports only
Mathlib and states the following, using the exact spherical and complete-component predicates
defined in that file:

```lean
def Problem1BoundedAt (d : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 2 * d → G.maxDegree ≤ d →
    ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G

def Problem1Bounded : Prop := ∀ (d : ℕ) (_hd3 : 3 < d), Problem1BoundedAt d
```

`Fin n` covers every finite simple graph up to relabelling; `n = 0` is included.
The generated [Challenge.lean](Challenge.lean) advertises precisely `Problem1Bounded`,
and [Solution.lean](Solution.lean) proves it as `FKSProblem1.Palomar.target`.
The challenge's deliberate proof hole is excluded from the development's zero-`sorry` count.
The proved fidelity companions separate spherical from unrestricted placements, require
injectivity, distinguish the component exception, exhibit a five-cycle witness at `d = 4`,
and refute the bounded statement without its dimension restriction using `K₃,₃` at `d = 3`.

## The proof

Pad the graph with isolated vertices to obtain exactly `2d` vertices. This preserves the
degree bound and the exclusion of a clique of order `d + 1`. The complement then has
minimum degree at least `d - 1`. If it has a perfect matching, place each matched pair at
opposite vertices of the radius-`1/√2` cross-polytope. Matching pairs are non-edges of the
original graph, and every other pair is orthogonal, so every edge has length one.

Otherwise Tutte's theorem supplies a violating vertex set in the complement. Component
sizes and parity rule out nonempty violating sets, except a set of size `d - 1`, which
would produce the forbidden clique. An empty violating set forces two complete components
of order `d` in the complement, so the original graph is bipartite. Place its two parts
injectively on circles in two orthogonal coordinate planes in ℝ⁴, then append zero
coordinates for larger `d`. Finally restrict to the original vertices and transfer through
the degree, complete-component and spherical-predicate bridges to the frozen statement.

## Checking it

Lean and Mathlib are pinned to `v4.35.0-rc2`; the exact dependency revisions are in
[lake-manifest.json](lake-manifest.json). In a linked worktree, first run
`scripts/worktree-setup.sh`. Ensure `lake` is on `PATH`, including for the scripts below:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake exe axioms
lake exe fidelity
lake exe module-system
lake exe layering
lake exe proof-links
lake exe standalone-mathlib
lake exe style
lake exe documentation
lake exe palomar-compatibility
scripts/check-palomar-challenge.sh
scripts/lint-env.sh
leanblueprint all
leanblueprint checkdecls
scripts/audit-probes.sh
```

CI runs these checks. The audit probes test committed `HEAD`, so the manager must repeat
release verification after committing the release files. Comparator's command and the
macOS isolation caveat are in its [record](docs/comparator-2026-09-29.md).
