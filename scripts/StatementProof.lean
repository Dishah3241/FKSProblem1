/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

/-! Exact statement-proof type contract shared by the proof-links and fidelity audits. -/

open Lean

namespace StatementProof

private def forallArity : Expr → Nat
  | .forallE _ _ body _ => forallArity body + 1
  | _ => 0

private def forallBody : Expr → Expr
  | .forallE _ _ body _ => forallBody body
  | body => body

/-- The proof concludes with the claim applied to its original parameters in order,
without additional assumptions. Kernel checking establishes their typing. -/
public def isExactProofType (claim : Name) (claimType proofType : Expr) : Bool :=
  let arity := forallArity claimType
  if forallArity proofType != arity then
    false
  else
    let result := forallBody proofType
    let arguments := result.getAppArgs
    result.getAppFn.constName? == some claim &&
      arguments.size == arity &&
      arguments.zipIdx.all fun (argument, index) =>
        argument == .bvar (arity - index - 1)

end StatementProof
