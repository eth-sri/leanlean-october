module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# A bounded interval is a one-dimensional ball

For `d = 1` an admissible bounded interval `(lo, hi)` is the Euclidean ball with centre
`(lo + hi)/2` and radius `(hi - lo)/2`, and the Euclidean distance to the centre is the absolute
value of the scalar coordinate.  The distance `d = r₀ - |y - m|` to the lateral boundary of the
ball is the distance to the nearer of the two endpoints.  Consequently an admissible domain
other than `ℝ^d` is always a ball, and the ball barriers of (A.1) apply to it.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set

/-- The midpoint of the interval `(lo, hi)` as a point of `Vec 1`. -/
def intervalCentre (lo hi : ℝ) : PDE.Vec 1 := fun _ => (lo + hi) / 2

/-- The Euclidean norm on `Vec 1` is the absolute value of the coordinate. -/
theorem vecEuclideanNorm_vec_one (x : PDE.Vec 1) : PDE.vecEuclideanNorm x = |x 0| := by
  unfold PDE.vecEuclideanNorm
  rw [PDE.vecNormSq_eq_sum_sq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

/-- A bounded interval is a Euclidean ball in `Vec 1`. -/
theorem oneDimensionalAxisBox_eq_euclideanBall {lo hi : ℝ} (hlohi : lo < hi) :
    PDE.oneDimensionalAxisBox lo hi =
      PDE.euclideanBall (intervalCentre lo hi) ((hi - lo) / 2) := by
  ext x
  rw [PDE.mem_oneDimensionalAxisBox_iff,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), vecEuclideanNorm_vec_one]
  simp only [PDE.vecOneCoordinate, Pi.sub_apply, intervalCentre]
  grind

/-- An admissible evolution domain is `ℝ^d` or a Euclidean ball: the bounded-interval case
`d = 1` is a ball. -/
theorem eq_univ_or_exists_euclideanBall_of_isAdmissibleEvolutionDomain {n : ℕ}
    {Ω : Set (PDE.Vec n)} (hΩ : IsAdmissibleEvolutionDomain Ω) :
    Ω = Set.univ ∨ ∃ (c : PDE.Vec n) (r : ℝ), 0 < r ∧ Ω = PDE.euclideanBall c r := by
  rcases hΩ with h | h | ⟨hn, lo, hi, hlohi, h⟩
  · simp_all
  · simp_all
  · cases hn
    have h' : Ω = PDE.oneDimensionalAxisBox lo hi := by omega
    exact Or.inr ⟨intervalCentre lo hi, (hi - lo) / 2, by linarith,
      h'.trans (oneDimensionalAxisBox_eq_euclideanBall hlohi)⟩

end HypoellipticAleksandrov.KineticAleksandrov

end
