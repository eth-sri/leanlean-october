module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BProcessBaseline
public import Mathlib
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open Complex Set
open scoped ContDiff
namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
def atkinsonPhaseExponential (T v : ℝ) : ℂ := Complex.exp ((T * v : ℝ) * I)

section
variable (T v : ℝ)
include T v
theorem hasDerivAt_atkinsonPhaseExponential :
    HasDerivAt (atkinsonPhaseExponential T)
      ((T : ℂ) * I * atkinsonPhaseExponential T v) v := by
  have h := ((((hasDerivAt_id v).const_mul T).ofReal_comp).mul_const I).cexp
  convert h using 1
  · rfl
  · simp only [atkinsonPhaseExponential, Complex.ofReal_mul, mul_one, id_eq]
    ring

theorem iteratedDeriv_two_atkinsonPhaseExponential :
    iteratedDeriv 2 (atkinsonPhaseExponential T) v =
      ((T : ℂ) * I) ^ 2 * atkinsonPhaseExponential T v := by
  have he : deriv (atkinsonPhaseExponential T) =
      fun w => (T : ℂ) * I * atkinsonPhaseExponential T w :=
    funext (fun w => (hasDerivAt_atkinsonPhaseExponential T w).deriv)
  have h := (hasDerivAt_atkinsonPhaseExponential T v).const_mul ((T : ℂ) * I)
  pm_7329 he h.deriv
  ring

theorem norm_atkinsonPhaseExponential_derivatives :
    ‖atkinsonPhaseExponential T v‖ = 1 ∧
    ‖deriv (atkinsonPhaseExponential T) v‖ = |T| ∧
    ‖iteratedDeriv 2 (atkinsonPhaseExponential T) v‖ = T ^ 2 := by
  have hn : ‖atkinsonPhaseExponential T v‖ = 1 := by
    simp [atkinsonPhaseExponential, Complex.norm_exp, Complex.mul_re]
  refine ⟨hn, ?_, ?_⟩
  · rw [(hasDerivAt_atkinsonPhaseExponential T v).deriv]
    simp_all
  · rw [iteratedDeriv_two_atkinsonPhaseExponential]
    simp_all
end

end TaoTrudgianYang2025
