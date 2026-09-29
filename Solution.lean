/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem1.Standalone.Mathlib.InlineFKSProblem1Proof

/-!
# FKS Problem 1: graphs of maximum degree d embed on a sphere in R^d

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace FKSProblem1.Palomar

/-- FKS Problem 1 restricted to graphs on at most `2 * d` vertices, for every `d > 3`: every
graph of maximum degree at most `d` with no connected component isomorphic to `K_{d+1}` has
spherical dimension at most `d`. -/
theorem target :
    FKSProblem1.Standalone.Mathlib.InlineFKSProblem1.Problem1Bounded :=
  FKSProblem1.Standalone.Mathlib.InlineFKSProblem1.Problem1Bounded.proof

end FKSProblem1.Palomar
