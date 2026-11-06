module
public import GuthMaynard.Improvement.OperatorKernel
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- Actual frequency-presentation operator on the time Hilbert space. -/
def operatorFrequency (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (A : ℝ → ℂ) (f : ℝ → ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  operatorIntegral ν (fun x => A x • operatorPhase μ (f x))
    (fun x => operatorPhase μ (f x))

section
variable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : ℝ → ℂ} {f : ℝ → ℝ} {B : ℝ} (hA : Measurable A) (hf : Measurable f)
include μ ν A f B hA hf
/-- All analytic premises for the nuclear presentation follow from ordinary
bounded measurable data and finite frequency/time measures. -/
theorem operator_frequency_inputs
    (_hB : 0 ≤ B) (hb : ∀ x, ‖A x‖ ≤ B) :
    AEStronglyMeasurable (fun x => A x • operatorPhase μ (f x)) ν ∧
    AEStronglyMeasurable (fun x => operatorPhase μ (f x)) ν ∧
    Integrable (fun x => ‖A x • operatorPhase μ (f x)‖*‖operatorPhase μ (f x)‖) ν := by
  have hp : AEStronglyMeasurable (fun x => operatorPhase μ (f x)) ν :=
    (operator_phase_continuous μ).comp_aestronglyMeasurable hf.aestronglyMeasurable
  refine ⟨hA.aestronglyMeasurable.smul hp,hp,?_⟩
  have hi : Integrable (fun x => ‖A x‖) ν :=
    (integrable_const B).mono' hA.norm.aestronglyMeasurable (by
      filter_upwards with x
      simpa only [Real.norm_eq_abs,abs_norm] using hb x)
  have he (x : ℝ) : ‖A x • operatorPhase μ (f x)‖*‖operatorPhase μ (f x)‖ =
      ‖A x‖*μ.real univ := by
    rw [norm_smul,mul_assoc,← pow_two,operator_phase_norm_sq]
  simp_rw [he]
  exact hi.mul_const _

/-- Genuine operator cubic trace equals the independently defined time
kernel cubic. A countable Hilbert basis is explicit; no spectral basis or
trace identity is included as a premise. -/
theorem operator_frequency_cubic
    (hB : 0 ≤ B) (hb : ∀ x, ‖A x‖ ≤ B)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    operatorDiagonalTrace b ((operatorFrequency μ ν A f)^3) =
      kernelCubic μ (frequencyKernel ν A f) := by
  pm_4550
  pm_4552
  pm_957 hx hy hxy operator_frequency_inputs μ ν hA hf hB hb
  rw [operatorFrequency,operatorIntegral_cubic_cycle ν b hx hy hxy,
    frequencyKernel_cubic μ ν hA hf hB hb]
  let Q : Triple → ℂ := fun x => (A x.1*A x.2.1*A x.2.2)*
    (measureFourier μ (f x.2.2-f x.1)*measureFourier μ (f x.1-f x.2.1)*
      measureFourier μ (f x.2.1-f x.2.2))
  have hQ : Integrable Q (tripleMeasure ν) := by
    have hi := (cubicIntegrand_integrable μ ν hA hf hB hb).integral_prod_left
    simpa only [cubicIntegrand_time_integral] using hi
  change _ = ∫ x, Q x ∂tripleMeasure ν
  have hQi : Integrable Q (ν.prod (ν.prod ν)) := hQ
  rw [tripleMeasure,integral_prod _ hQi]
  pm_878 hQi.prod_right_ae
end

end GuthMaynard.Improvement
