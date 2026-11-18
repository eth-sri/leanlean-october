module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsRegularizedBarrier
import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped Topology Convolution

/-- The position convolution can integrate the mollifier at a fixed displacement. -/
theorem positionConvolution_displacement (eta : ℝ → ℝ) (Phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) :
    positionConvolution eta Phi q = ∫ Y, eta Y * Phi (q.1 - Y, q.2) := by
  simpa only [positionConvolution, sub_sub_cancel] using (integral_sub_left_eq_self (fun Y => eta (q.1 - Y) * Phi (Y, q.2)) volume q.1).symm


/-- A nonnegative normalized position convolution preserves the same coordinate modulus. -/
theorem positionConvolution_modulus (eta : ℝ → ℝ)
    (heta : IsNonnegativeUnitSmoothMollifier eta) (Phi : (ℝ × ℝ) → ℝ)
    (hPhi : Continuous Phi) (alpha D : ℝ) (hD : 0 ≤ D)
    (hm : ∀ z w : ℝ × ℝ, |Phi z - Phi w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)) :
    ∀ z w : ℝ × ℝ, |positionConvolution eta Phi z - positionConvolution eta Phi w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)  := by
  intro z w
  have positionConvolution_displacement_integrable (q : ℝ × ℝ) :
      Integrable (fun Y => eta Y * Phi (q.1 - Y, q.2)) volume := by
    have hc : Continuous (fun Y => eta Y * Phi (q.1 - Y, q.2)) :=
      heta.1.continuous.mul
        (hPhi.comp ((continuous_const.sub continuous_id).prodMk continuous_const))
    exact hc.integrable_of_hasCompactSupport heta.2.1.mul_right
  let B := D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hzi := positionConvolution_displacement_integrable z
  have hwi := positionConvolution_displacement_integrable w
  have hηi : Integrable eta volume :=
    heta.1.continuous.integrable_of_hasCompactSupport heta.2.1
  have hbd (Y : ℝ) : |eta Y * Phi (z.1 - Y, z.2) - eta Y * Phi (w.1 - Y, w.2)| ≤
      eta Y * B := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (heta.2.2.1 Y)]
    apply mul_le_mul_of_nonneg_left _ (heta.2.2.1 Y)
    have he : z.1 - Y - (w.1 - Y) = z.1 - w.1 := by ring
    simpa using hm (z.1 - Y, z.2) (w.1 - Y, w.2)
  rw [positionConvolution_displacement, positionConvolution_displacement,
    ← integral_sub hzi hwi]
  calc
    _ ≤ ∫ Y, |eta Y * Phi (z.1 - Y, z.2) - eta Y * Phi (w.1 - Y, w.2)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ Y, eta Y * B := integral_mono (hzi.sub hwi).abs (hηi.mul_const B) hbd
    _ = B := by rw [integral_mul_const, heta.2.2.2, one_mul]


/-- The positive position smoothing radius tends to zero. -/
def barrierMollifierRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Every smoothing radius is strictly positive. -/
theorem barrierMollifierRadius_pos (n : ℕ) : 0 < barrierMollifierRadius n := by
  dsimp only [barrierMollifierRadius]
  positivity

/-- The source position bump at the actual shrinking radius. -/
def barrierMollifierBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨barrierMollifierRadius n / 2, barrierMollifierRadius n,
    half_pos (barrierMollifierRadius_pos n), half_lt_self (barrierMollifierRadius_pos n)⟩

/-- The actual nonnegative normalized smooth position mollifier. -/
def barrierMollifier (n : ℕ) : ℝ → ℝ := (barrierMollifierBump n).normed volume

/-- Every sequence member satisfies the mollifier conditions. -/
theorem barrierMollifier_spec (n : ℕ) : IsNonnegativeUnitSmoothMollifier (barrierMollifier n) :=
  ⟨(barrierMollifierBump n).contDiff_normed,
    (barrierMollifierBump n).hasCompactSupport_normed,
    (barrierMollifierBump n).nonneg_normed, (barrierMollifierBump n).integral_normed⟩

/-- The outer support radii tend to zero. -/
theorem barrierMollifierRadius_tendsto :
    Tendsto barrierMollifierRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The actual position-smoothed continuous barrier converges at every physical point. -/
theorem barrier_position_mollifier_tendsto {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (q : ℝ × ℝ) :
    Tendsto (fun n => positionConvolution (barrierMollifier n)
      (bellmanOriginExtension phi) q) atTop (𝓝 (bellmanOriginExtension phi q)) := by
  have hc : Continuous (fun X => bellmanOriginExtension phi (X, q.2)) :=
    (h.origin_extension_continuous ha).comp (continuous_id.prodMk continuous_const)
  simpa [positionConvolution_displacement, barrierMollifier, convolution_def, ContinuousLinearMap.lsmul_apply] using (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := barrierMollifierBump) barrierMollifierRadius_tendsto hc q.1)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

