module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationGeometry

/-! # Nested dyadic backward cylinders -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- The physical dyadic radius used in the forced oscillation iteration. -/
def dyadicRadius (r : ℝ) (n : ℕ) : ℝ := r * (1 / 2 : ℝ) ^ n

variable {r : ℝ}

/-- Positive radii remain positive at each finite dyadic stage. -/
theorem dyadicRadius_pos  (hr : 0 < r) (n : ℕ) : 0 < dyadicRadius r n :=
  mul_pos hr (pow_pos (by norm_num) n)

/-- Every dyadic radius is bounded by the original radius. -/
theorem dyadicRadius_le  (hr : 0 ≤ r) (n : ℕ) : dyadicRadius r n ≤ r := (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) :
      (1 / 2 : ℝ) ^ n ≤ 1) hr).trans_eq (mul_one r)

variable (r : ℝ) (n : ℕ)

/-- Successor radii are exactly half the preceding radii. -/
theorem dyadicRadius_succ  :
    dyadicRadius r (n + 1) = dyadicRadius r n / 2 := by
  simp only [dyadicRadius, pow_succ]
  ring

/-- Squared dyadic radii give the geometric quadratic forcing. -/
theorem dyadicRadius_sq  :
    dyadicRadius r n ^ 2 = r ^ 2 * (1 / 4 : ℝ) ^ n := by
  rw [dyadicRadius, mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

variable {N : ℕ} (T : ℝ) (v : PDE.Vec N)

/-- Smaller closed backward cylinders lie in larger closed backward cylinders. -/
theorem backward_ball_closed_mono
    {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    scalarParabolicClosedCylinder (T - s ^ 2) T (PDE.euclideanBall v s) ⊆
      scalarParabolicClosedCylinder (T - r ^ 2) T (PDE.euclideanBall v r) := by
  intro z hz
  constructor
  · constructor
    ·
      linarith only [hz.1.1, (sq_le_sq₀ hs.le (hs.le.trans hsr) |>.mpr hsr)]
    · exact hz.1.2
  · apply closure_mono _ hz.2
    intro y hy
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (hs.trans_le hsr)]
    exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).mp hy).trans_le hsr

/-- Every positive-radius backward cylinder is nonempty. -/
theorem backward_ball_nonempty
    {r : ℝ} (hr : 0 < r) :
    (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v r)).Nonempty := by
  refine ⟨(T - r ^ 2 / 2, v), ?_, ?_⟩
  · simp_all
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr, sub_self]
    simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hr

end HypoellipticAleksandrov.Parabolic.LocalHolder
