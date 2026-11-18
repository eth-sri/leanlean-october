module

public import RequestProject.SawtoothKernel

@[expose] public section
noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Interval
open scoped InnerProductSpace ComplexConjugate

private lemma sign_ae_split {F : ℝ → ℂ} {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ((fun s => (Real.sign (θ - s) : ℂ) * F s) =ᵐ[volume.restrict (Ι (0 : ℝ) θ)] F) ∧
    ((fun s => (Real.sign (θ - s) : ℂ) * F s) =ᵐ[volume.restrict (Ι θ (2 * π))] fun s => -F s) := by
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ θ := by simp [ae_iff, measure_singleton]
  refine ⟨?_, ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by linarith [lt_of_le_of_ne hmem.2 hs])]; simp
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]; simp

lemma intervalIntegrable_sign_mul_of_integrable {F : ℝ → ℂ} {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * F s) volume 0 (2 * π) := by
  obtain ⟨e1, e2⟩ := sign_ae_split (F := F) hθ
  exact (h1.congr_ae e1.symm).trans (h2.neg.congr_ae e2.symm)

lemma intervalIntegral_sign_mul_of_integrable {F : ℝ → ℂ} {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    ∫ s in (0 : ℝ)..(2 * π), (Real.sign (θ - s) : ℂ) * F s =
      (∫ s in (0 : ℝ)..θ, F s) - ∫ s in θ..(2 * π), F s := by
  obtain ⟨e1, e2⟩ := sign_ae_split (F := F) hθ
  rw [← intervalIntegral.integral_add_adjacent_intervals (h1.congr_ae e1.symm) (h2.neg.congr_ae e2.symm),
    intervalIntegral.integral_congr_ae_restrict e1,
    intervalIntegral.integral_congr_ae_restrict e2, intervalIntegral.integral_neg]
  ring

lemma sawtoothKernel_add_correctedKernel {W : ℝ → Ell2 →L[ℂ] Ell2} (θ s : ℝ) :
    sawtoothKernel θ s + correctedKernel W θ s =
      Complex.I * Real.sign (θ - s) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ := by
  simp only [sawtoothKernel, correctedKernel]; ring

end PolyaNeumann
end
