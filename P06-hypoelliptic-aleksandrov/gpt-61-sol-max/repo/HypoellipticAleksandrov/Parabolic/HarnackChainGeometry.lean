module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry

/-!
# Fixed finite-chain geometry for parabolic Harnack

This module contains only the geometry of the square-root-free finite chain
from `(1, 0)` to `(4, z)`.  The velocity work boxes remain coordinate cubes,
while their containment is proved in the explicit Euclidean ball geometry.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

section

/-- A closed coordinate cube controls the explicit squared Euclidean distance. -/
theorem vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube
    {d : ℕ} {v v0 : PDE.Vec d} {r : ℝ}
    (hv : v ∈ velocityClosedCube v0 r) :
    PDE.vecNormSq (v - v0) ≤ (d : ℝ) * r ^ 2 := by
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, (v - v0) i ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi


      simpa only [Pi.sub_apply, sq_abs] using ((sq_le_sq₀ (abs_nonneg (v i - v0 i)) (le_trans (abs_nonneg (v i - v0 i)) (hv i))).mpr (hv i))
    _ = (d : ℝ) * r ^ 2 := by simp [nsmul_eq_mul]

end

end HypoellipticAleksandrov.Parabolic
