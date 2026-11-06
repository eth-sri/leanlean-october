module
public import OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesUniform

@[expose] public section

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(FourierBridge.coefficientMomentBound 0 C'+
    FourierBridge.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 C' hC')
      (FourierBridge.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := FourierBridge.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hiN := AnalyticBridge.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring
