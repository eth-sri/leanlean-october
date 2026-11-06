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

variable {d : ℕ} (x : Vec d) (i : Fin d)

@[simp]
theorem basisVec_apply  (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

theorem vecDot_basisVec_left  (x : Vec d) :
    vecDot (basisVec i) x = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · simp_all
  simp

theorem vecDot_basisVec_right  :
    vecDot x (basisVec i) = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · simp_all
  simp

theorem vecNormSq_basisVec  :
    vecNormSq (basisVec i) = 1 := by
  rw [vecNormSq, vecDot_basisVec_left]
  simp

theorem vecEuclideanNorm_basisVec  :
    vecEuclideanNorm (basisVec i) = 1 := by
  rw [vecEuclideanNorm, vecNormSq_basisVec, Real.sqrt_one]

/-- Coordinate reconstruction in the native basis. -/
theorem sum_smul_basisVec  :
    ∑ i : Fin d, x i • basisVec i = x := by
  aesop

end PDE
