module
public import GuthMaynard.Improvement.SmoothingFourier

@[expose] public section
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement

def kernelBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
def compactKernel : ℝ → ℝ := kernelBump.normed volume

theorem compactKernel_nonneg (x : ℝ) : 0 ≤ compactKernel x :=
  kernelBump.nonneg_normed (μ := volume) x

theorem compactKernel_integrable : Integrable compactKernel :=
  kernelBump.integrable_normed

theorem compactKernel_mass : ∫ x, compactKernel x = 1 :=
  kernelBump.integral_normed

theorem compactKernel_smooth : ContDiff ℝ ∞ compactKernel :=
  kernelBump.contDiff_normed

theorem compactKernel_compact : HasCompactSupport compactKernel :=
  kernelBump.hasCompactSupport_normed

theorem compactKernel_zero {x : ℝ} (hx : 2 ≤ |x|) : compactKernel x = 0 := by
  have hs := kernelBump.support_normed_eq (μ := volume)
  have hn : x ∉ Function.support compactKernel := by
    rw [show Function.support compactKernel = Metric.ball 0 2 from hs]
    simpa [Metric.mem_ball, Real.dist_eq, not_lt] using hx
  simpa [Function.support] using hn

theorem compactKernel_bound : ∃ B : ℝ, 0 < B ∧ ∀ x, ‖compactKernel x‖ ≤ B := by
  refine ⟨(∫ x, kernelBump x)⁻¹, inv_pos.mpr kernelBump.integral_pos, ?_⟩
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (compactKernel_nonneg x)]
  change kernelBump x / (∫ y, kernelBump y) ≤ _
  simpa [one_div] using div_le_div_of_nonneg_right kernelBump.le_one
    kernelBump.integral_pos.le

theorem compactKernel_schwartz : ∃ ψ : 𝓢(ℝ, ℂ),
    (ψ : ℝ → ℂ) = fun x => (compactKernel x : ℂ) := by
  have hc : HasCompactSupport (fun x => (compactKernel x : ℂ)) :=
    compactKernel_compact.comp_left (g := Complex.ofReal) (by simp)
  have hd : ContDiff ℝ ∞ (fun x => (compactKernel x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp compactKernel_smooth
  exact ⟨hc.toSchwartzMap hd, rfl⟩

end GuthMaynard.Improvement
