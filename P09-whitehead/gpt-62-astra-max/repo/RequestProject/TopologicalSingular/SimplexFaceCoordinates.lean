module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47; isolated geometry for Lean 4.28.0.
-/
public import RequestProject.TopologicalSingular.StickSimplex

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {j : ℕ}

variable (i : Fin (j + 2))

theorem faceMap_injective : Function.Injective (faceMap (j := j) i) := by
  intro x y h
  refine Subtype.ext (funext fun k => ?_)
  have := congrArg (fun z : stdSimplex ℝ (Fin _) => z.1 (i.succAbove k)) h
  simpa using this

variable {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0)

/-- The inverse of the `i`-th face inclusion, deleting the `i`-th coordinate. -/
def dropMap :
    stdSimplex ℝ (Fin (j + 1)) :=
  ⟨Fin.removeNth i x.1, fun k => x.2.1 _, by
    have h := x.2.2
    rw [Fin.sum_univ_succAbove _ i, hx, zero_add] at h
    exact h⟩

theorem faceMap_dropMap :
    faceMap i (dropMap i hx) = x := by
  refine Subtype.ext (funext fun k => ?_)
  refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> aesop

end FiniteChains.TopologicalSingular
