module

public import PDEFoundation.Ambient.EuclideanNorm
import Aesop



/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/

@[expose] public section

namespace PDE

/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 )

variable {d : ℕ}

@[simp]
theorem basisVec_apply  (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  simp_all [basisVec] <;> aesop

theorem vecDot_basisVec_left  (i : Fin d) (x : Vec d) :
    vecDot (basisVec i) x = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    simp at hi

theorem vecDot_basisVec_right  (x : Vec d) (i : Fin d) :
    vecDot x (basisVec i) = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    simp at hi

variable (i : Fin d)

theorem vecNormSq_basisVec   :
    vecNormSq (basisVec i) = 1 := by
  rw [vecNormSq, vecDot_basisVec_left]
  simp

theorem vecEuclideanNorm_basisVec   :
    vecEuclideanNorm (basisVec i) = 1 := by
  rw [vecEuclideanNorm, vecNormSq_basisVec, Real.sqrt_one]

/-- Coordinate reconstruction in the native basis. -/
theorem sum_smul_basisVec  (x : Vec d) :
    ∑ i : Fin d, x i • basisVec i = x := by
  funext j
  simp [basisVec_apply]

end PDE
