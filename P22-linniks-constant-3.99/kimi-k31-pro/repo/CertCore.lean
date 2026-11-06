module

/-!
# The leaf-certificate checker, without Mathlib

A copy of the checker `GradedNear.Cert.checkLeaf` (`GradedNear/Defs.lean`, section "Exact
certificates for the leaf LPs") that depends on Lean core only, so that it can be compiled to a
native executable (`CertRunNative.lean`, `lake build certrun`) without compiling Mathlib.

The definitions are those of `GradedNear.Defs`, with `Int`, `Nat`, core `Rat` and core `List`
functions. The pieces that `GradedNear.Defs` takes from Mathlib are replaced:
* `List.zipWith3` is `CertCore.zipWith3` (the same recursion);
* the ceiling `⌈·⌉ : ℚ → ℤ` is `ratCeil q = -Rat.floor (-q)`, which is how Mathlib's
  `FloorRing ℚ` instance defines it.

The one function computed differently is `caseValue`, the dual check of a case, where almost all
the time goes (every column, every case, every box). Instead of building the list of costs of a
column and summing its products with the duals `Z`, it accumulates the sum row by row
(`dotAcc`), skipping rows whose dual or cost is `0`, with the per-row constants of the costs
computed once per case (`costPrep`, `costOf`); the products of the duals `V`, `U`, `P - M` with
zero column coefficients are skipped too (`addMul`), and the budgets are computed only for rows
with a nonzero dual (`budgetAcc`). The casts of the duals to `Int` are done once per case. The
results are the same integers, by `0 * x = 0`, `x + 0 = x`, the associativity of `+`,
`x ^ 2 = x * x` and `max y 0 = y` for `y > 0`.

`GradedNear.Cert.checkLeaf_toCore` and `GradedNear.Cert.checkLeaf_ofCore`
(`GradedNear/Cert/FastEq.lean`) prove that `CertCore.checkLeaf` computes exactly
`GradedNear.Cert.checkLeaf` on the data converted field by field, so the soundness theorem
`GradedNear.Cert.checkLeaf_sound` applies to the values computed by the compiled checker.
-/

@[expose] public section

namespace CertCore

/-! ## The checker -/

/-! ### The dual check of a case, computed row by row -/

/-- The constants of the column costs of a row on the box interval `[a, b]` for case `c`: the
case, the shift `m` (`b·S/TS` for `c = 2`, `(a + b)·HS` otherwise) and, for the tangent cases,
`h = 2(b - a)·HS`. -/
structure CostPrep where
  c : Nat
  m : Int
  h : Int

end CertCore
