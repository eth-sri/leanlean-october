module
public import AtomicRadialFubini
import WeylPort.Analytic.RealLaplace

public section

open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

section
variable {a : ℝ → ℂ}
include a
theorem spatialCubicMode_measurable {F : ℝ → ℂ}
    (ha : Measurable a) (hF : Continuous F) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2) := by
  have hp := phase_measurable
  pm_5232 hf hF.measurable hm
  unfold spatialCubicMode
  fun_prop

theorem spatialCubicMode_support {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Function.support (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2) ⊆
      Icc l u ×ˢ (Icc l u ×ˢ Icc l u) := by pm_4546

theorem spatialCubicMode_integrable {F : ℝ → ℂ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2) := by
  pm_4547 F
  apply (integrableOn_const hE.measure_lt_top.ne (C := B^3*M^3)).mono'
    (spatialCubicMode_measurable ha.measurable hF L m).aestronglyMeasurable
  filter_upwards with x
  simp only [spatialCubicMode,norm_mul,phase_norm,mul_one]
  calc
    _ ≤ (B*B*B)*(M*M*M) := by
      gcongr <;> first | exact hb _ | exact hbF _
    _ = _ := by ring

/-- Actual coordinate reordering followed by the proved radial Fubini identity. -/
theorem spatialCubicMode_integral_radial {F : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ x : Triple, spatialCubicMode a F L m x.1 x.2.1 x.2.2) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct F p := by pm_4548 hF hM hbF F
end

/-- Complete retained finite cubic kernel, with all three actual Fourier
factors, equals its finite sum of compact-ratio radial integrals. -/
theorem retained_cubic_radial_assembly (ν : Measure ℝ) [IsFiniteMeasure ν] {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic ν (retainedPoissonKernel (volume.restrict (Icc l u)) a L S) =
      (L:ℂ)^3 * ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          radialKernel a L (m₁,m₂,m₃) p * ratioFourierProduct (measureFourier ν) p := by
  pm_69 B hB hb assembly_cutoff_bound ha.continuous hs
  have hF := operator_measureFourier_continuous ν
  have hM : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hbF (ξ : ℝ) : ‖measureFourier ν ξ‖ ≤ ν.real univ := by
    simpa only [measureFourier,one_mul] using norm_integral_le_of_norm_le_const
      (μ := ν) (f := fun t => phase (-ξ*t)) (C := 1)
      (Filter.Eventually.of_forall (fun t => (phase_norm _).le))
  rw [retainedPoissonKernel_cubic ν _ ha.continuous.measurable hB.le hb]
  pm_6991
  have heq : ∀ x : Triple,
      (∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        (a x.1*a x.2.1*a x.2.2)*phase (-L*((m₁:ℝ)*x.1+(m₂:ℝ)*x.2.1+(m₃:ℝ)*x.2.2))) *
        (measureFourier ν (mellinFrequency x.2.2-mellinFrequency x.1)*
          measureFourier ν (mellinFrequency x.1-mellinFrequency x.2.1)*
          measureFourier ν (mellinFrequency x.2.1-mellinFrequency x.2.2)) =
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S, spatialCubicMode a (measureFourier ν) L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 := by
    intro x
    simp only [Finset.sum_mul,spatialCubicMode,mul_assoc]
  simp_rw [heq]
  rw [integral_const_mul]
  congr 1
  have hsint : ∀ m, Integrable (fun x : Triple => spatialCubicMode a (measureFourier ν) L m x.1 x.2.1 x.2.2)
      (tripleMeasure (volume.restrict (Icc l u))) := by
    pm_5391 hF hM hbF
    pm_89 tripleMeasure Measure.prod_restrict Measure.volume_eq_prod IntegrableOn h
  change (∫ x : Triple, ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
    spatialCubicMode a (measureFourier ν) L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 ∂tripleMeasure (volume.restrict (Icc l u))) = _
  pm_4549
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => Function.notMem_support.mp
    (fun hn => hx (spatialCubicMode_support hs (measureFourier ν) L (m₁,m₂,m₃) hn)))]
  exact spatialCubicMode_integral_radial ha hl hlu hs hF hM hbF L (m₁,m₂,m₃)

end GuthMaynard.Improvement.AtomicCubic
