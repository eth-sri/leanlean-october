module

public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/

@[expose] public section

namespace PDE

variable {d : ℕ} (i : Fin d) (x : Vec d)

include i in
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec : Vec d :=
  Pi.single i (1 : ℝ)

@[simp]
theorem basisVec_apply (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

theorem vecDot_basisVec_right (i : Fin d) :
    vecDot x (basisVec i) = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · grind
  simp

/-- Coordinate reconstruction in the native basis. -/
theorem sum_smul_basisVec :
    ∑ i : Fin d, x i • basisVec i = x := by
  funext j
  simp

end PDE
