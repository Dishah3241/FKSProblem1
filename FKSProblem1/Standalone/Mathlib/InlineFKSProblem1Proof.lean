/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem1.Standalone.Mathlib.InlineFKSProblem1

import FKSProblem1.Standalone.Mathlib.StatementAProof

/-!
# Proof of the inlined statement

The inline statement repeats statement A's declarations with the same bodies, so each proof is the
corresponding proof in `StatementAProof`: the bounded first target through the degree, component
and spherical bridges and the shared library's at-most-`2 * d`-vertex result, and the fidelity
companions from the elementary placements. FKS 2020 Problem 1 itself and its `d = 4`
instance are false (Mishra and Senthilkumar, 2026), a disproof not contained here; only the
restriction to at most `2 * d` vertices is proved.
-/

public section

namespace FKSProblem1.Standalone.Mathlib.InlineFKSProblem1

theorem HasSphericalDimAtMost.separating.proof :
    HasSphericalDimAtMost.separating :=
  FKSProblem1.StatementA.HasSphericalDimAtMost.separating.proof

theorem HasCompleteComponent.separating.proof :
    HasCompleteComponent.separating :=
  FKSProblem1.StatementA.HasCompleteComponent.separating.proof

theorem Problem1At.separating.proof : Problem1At.separating :=
  FKSProblem1.StatementA.Problem1At.separating.proof

theorem Problem1.witness.proof : Problem1.witness :=
  FKSProblem1.StatementA.Problem1.witness.proof

theorem Problem1.dropHd3.proof : Problem1.dropHd3 :=
  FKSProblem1.StatementA.Problem1.dropHd3.proof

theorem Problem1At4.witness.proof : Problem1At4.witness :=
  FKSProblem1.StatementA.Problem1At4.witness.proof

theorem Problem1BoundedAt.separating.proof : Problem1BoundedAt.separating :=
  FKSProblem1.StatementA.Problem1BoundedAt.separating.proof

theorem Problem1Bounded.proof : Problem1Bounded :=
  FKSProblem1.StatementA.Problem1Bounded.proof

theorem Problem1Bounded.witness.proof : Problem1Bounded.witness :=
  FKSProblem1.StatementA.Problem1Bounded.witness.proof

theorem Problem1Bounded.dropHd3.proof : Problem1Bounded.dropHd3 :=
  FKSProblem1.StatementA.Problem1Bounded.dropHd3.proof

end FKSProblem1.Standalone.Mathlib.InlineFKSProblem1
