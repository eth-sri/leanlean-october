module
public import GuthMaynard.Improvement.RadialDecay
public import GuthMaynard.Improvement.CubicTimeMeasure

@[expose] public section
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

def radialKernel (a : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) : ℂ :=
  ∫ r, radialAmplitude a p.1 p.2 r*phase (-L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))*r)
def ratioFourierProduct (μ : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  𝓕 (fun t => (μ t:ℂ)) (-mellinFrequency p.1)*
  𝓕 (fun t => (μ t:ℂ)) (mellinFrequency p.1-mellinFrequency p.2)*
  𝓕 (fun t => (μ t:ℂ)) (mellinFrequency p.2)
def radialDiscard (a : ℝ → ℂ) (μ : ℝ → ℝ) (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) : ℂ :=
  if H < |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| then radialKernel a L m p*ratioFourierProduct μ p else 0

theorem radialKernel_measurable {a : ℝ → ℂ} (ha : Measurable a) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (radialKernel a L m) := by
  have hp := phase_measurable
  have hh : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      radialAmplitude a z.1.1 z.1.2 z.2*phase (-L*((m.1:ℝ)*z.1.1+(m.2.1:ℝ)*z.1.2+(m.2.2:ℝ))*z.2)) := by
    unfold radialAmplitude
    fun_prop
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

theorem ratioFourierProduct_measurable {μ : ℝ → ℝ} (hi : Integrable μ) : Measurable (ratioFourierProduct μ) := by
  have hc : Continuous (𝓕 (fun t => (μ t:ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (Complex.ofRealCLM.integrable_comp hi)
  unfold ratioFourierProduct mellinFrequency
  fun_prop

theorem ratioFourierProduct_bound {μ : ℝ → ℝ} (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    (hi : Integrable μ) (p : ℝ × ℝ) : ‖ratioFourierProduct μ p‖ ≤ (∫ t, μ t)^3 := by
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  unfold ratioFourierProduct
  simp only [norm_mul]
  calc
    _ ≤ (∫ t, μ t)*(∫ t, μ t)*(∫ t, μ t) := by gcongr <;> exact time_fourier_norm_le_mass hm h0 hi _
    _ = _ := by ring


