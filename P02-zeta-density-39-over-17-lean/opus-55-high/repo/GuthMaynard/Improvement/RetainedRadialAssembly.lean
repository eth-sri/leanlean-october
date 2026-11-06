module
public import GuthMaynard.Improvement.RadialFubini
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

theorem assembly_cutoff_bound {a : ℝ → ℂ} (ha : Continuous a) {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖a x‖ ≤ B := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  pm_4545
  intro x
  by_cases hx : x ∈ Icc l u
  aesop
  simp_all

theorem spatialCubicMode_measurable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Measurable a) (hi : Integrable μ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2) := by
  have hp := phase_measurable
  pb_2744
  pm_5232 hf hc.measurable hm
  unfold spatialCubicMode
  fun_prop

theorem spatialCubicMode_support {a : ℝ → ℂ} {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (μ : ℝ → ℝ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Function.support (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2) ⊆
      Icc l u ×ˢ (Icc l u ×ˢ Icc l u) := by pm_4546

theorem spatialCubicMode_integrable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2) := by
  pm_4517
  pm_4547 μ
  apply (integrableOn_const hE.measure_lt_top.ne (C := B^3*(∫ t, μ t)^3)).mono'
    (spatialCubicMode_measurable ha.measurable hi L m).aestronglyMeasurable
  filter_upwards with x
  simp only [spatialCubicMode,norm_mul,phase_norm,mul_one]
  calc
    _ ≤ (B*B*B)*((∫ t, μ t)*(∫ t, μ t)*(∫ t, μ t)) := by
      gcongr <;> first | exact hb _ | exact time_fourier_norm_le_mass hm h0 hi _
    _ = _ := by ring

/-- Actual coordinate reordering followed by the proved radial Fubini identity. -/
theorem spatialCubicMode_integral_radial {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ x : Triple, spatialCubicMode a μ L m x.1 x.2.1 x.2.2) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct μ p := by pm_4548 hm h0 hi μ

/-- Complete retained finite cubic kernel, with all three actual Fourier
factors, equals its finite sum of compact-ratio radial integrals. -/
theorem retained_cubic_radial_assembly {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic (timeMeasure μ) (retainedPoissonKernel (volume.restrict (Icc l u)) a L S) =
      (L:ℂ)^3 * ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          radialKernel a L (m₁,m₂,m₃) p * ratioFourierProduct μ p := by
  pm_69 B hB hb assembly_cutoff_bound ha.continuous hs
  rw [retained_cubic_time_density _ hm h0 hi ha.continuous.measurable hB.le hb]
  pm_6991
  have heq : ∀ x : Triple,
      (∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        (a x.1*a x.2.1*a x.2.2)*phase (-L*((m₁:ℝ)*x.1+(m₂:ℝ)*x.2.1+(m₃:ℝ)*x.2.2))) *
        (𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.2.2-mellinFrequency x.1)*
          𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.1-mellinFrequency x.2.1)*
          𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.2.1-mellinFrequency x.2.2)) =
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S, spatialCubicMode a μ L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 := by
    intro x
    simp only [Finset.sum_mul,spatialCubicMode,mul_assoc]
  simp_rw [heq]
  rw [integral_const_mul]
  congr 1
  have hsint : ∀ m, Integrable (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2)
      (tripleMeasure (volume.restrict (Icc l u))) := by
    pm_5391 hm h0 hi
    pm_89 tripleMeasure Measure.prod_restrict Measure.volume_eq_prod IntegrableOn h
  change (∫ x : Triple, ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
    spatialCubicMode a μ L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 ∂tripleMeasure (volume.restrict (Icc l u))) = _
  pm_4549
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => Function.notMem_support.mp
    (fun hn => hx (spatialCubicMode_support hs μ L (m₁,m₂,m₃) hn)))]
  exact spatialCubicMode_integral_radial ha hl hlu hs hm h0 hi L (m₁,m₂,m₃)

end GuthMaynard.Improvement
