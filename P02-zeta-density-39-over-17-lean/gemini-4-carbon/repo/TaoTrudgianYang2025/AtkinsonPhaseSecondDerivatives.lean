module
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import Mathlib

@[expose] public section
noncomputable section
open Complex Set
open scoped ContDiff
namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
def atkinsonPhaseExponential (T v : ℝ) : ℂ := Complex.exp ((T * v : ℝ) * I)

theorem hasDerivAt_atkinsonPhaseExponential (T v : ℝ) :
    HasDerivAt (atkinsonPhaseExponential T)
      ((T : ℂ) * I * atkinsonPhaseExponential T v) v := by
  convert (((((hasDerivAt_id v).const_mul T).ofReal_comp).mul_const I).cexp) using 1
  · rfl
  · simp only [atkinsonPhaseExponential, Complex.ofReal_mul, mul_one, id_eq]
    ring

theorem iteratedDeriv_two_atkinsonPhaseExponential (T v : ℝ) :
    iteratedDeriv 2 (atkinsonPhaseExponential T) v =
      ((T : ℂ) * I) ^ 2 * atkinsonPhaseExponential T v := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (funext (fun w => (hasDerivAt_atkinsonPhaseExponential T w).deriv))]
  convert ((hasDerivAt_atkinsonPhaseExponential T v).const_mul ((T : ℂ) * I)).deriv using 1
  ring

theorem norm_atkinsonPhaseExponential_derivatives (T v : ℝ) :
    ‖atkinsonPhaseExponential T v‖ = 1 ∧
    ‖deriv (atkinsonPhaseExponential T) v‖ = |T| ∧
    ‖iteratedDeriv 2 (atkinsonPhaseExponential T) v‖ = T ^ 2 := by
  have hn : ‖atkinsonPhaseExponential T v‖ = 1 := by
    simp [atkinsonPhaseExponential, Complex.norm_exp, Complex.mul_re]
  refine ⟨hn, ?_, ?_⟩
  · rw [(hasDerivAt_atkinsonPhaseExponential T v).deriv]
    simp only [norm_mul, hn, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
  · rw [iteratedDeriv_two_atkinsonPhaseExponential]
    simp only [norm_mul, norm_pow, hn, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, sq_abs]

end TaoTrudgianYang2025
