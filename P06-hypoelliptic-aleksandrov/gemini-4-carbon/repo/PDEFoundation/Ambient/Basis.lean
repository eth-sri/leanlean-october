module

public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/

@[expose] public section

namespace PDE

/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

@[simp]
theorem basisVec_apply {d : ℕ} (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]


theorem vecDot_basisVec_right {d : ℕ} (x : Vec d) (i : Fin d) :
    vecDot x (basisVec i) = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    simp at hi



/-- Coordinate reconstruction in the native basis. -/
theorem sum_smul_basisVec {d : ℕ} (x : Vec d) :
    ∑ i : Fin d, x i • basisVec i = x := by
  funext j
  simp [basisVec_apply]

end PDE
