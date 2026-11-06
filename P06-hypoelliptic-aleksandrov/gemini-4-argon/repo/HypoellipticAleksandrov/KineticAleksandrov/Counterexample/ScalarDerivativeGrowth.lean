module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNormalized
import Mathlib.Tactic

/-! # Actual first and second derivative power bounds on the similarity rays -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology ContDiff

/- The actual second derivative of a positive-ray power remainder. -/
theorem scalar_deriv_tail_ratio (f : ℝ → ℝ) (alpha c ) (hf : ContDiff ℝ 2 f)
    (hr : IsBigO atTop (deriv (fun s => f s - c * Real.rpow s alpha))
      (fun s => Real.rpow s (alpha - 4))) :
    Tendsto (fun s => deriv f s / Real.rpow s (alpha - 1)) atTop (𝓝 (c * alpha)) := by
  have hzero : Tendsto (fun s =>
      deriv (fun t => f t - c * Real.rpow t alpha) s / Real.rpow s (alpha - 1))
      atTop (𝓝 0) := by
    apply scalar_tail_ratio _ (alpha - 1) 0
    simpa only [zero_mul, sub_zero, show alpha - 1 - 3 = alpha - 4 by ring] using hr
  have ht := hzero.add_const (c * alpha)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [scalar_power_remainder_deriv f alpha c s hs (hf.differentiable (by norm_num) s)]
  have hp : Real.rpow s (alpha - 1) ≠ 0 := by
    simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hs (alpha - 1)).ne'
  field_simp
  ring

/- A twice differentiated remainder gives a finite normalized second-derivative limit. -/
theorem scalar_deriv2_tail_ratio (f : ℝ → ℝ) (alpha c ) (hf : ContDiff ℝ 2 f)
    (hr : IsBigO atTop (deriv (deriv (fun s => f s - c * Real.rpow s alpha)))
      (fun s => Real.rpow s (alpha - 5))) :
    Tendsto (fun s => deriv (deriv f) s / Real.rpow s (alpha - 2))
      atTop (𝓝 (c * alpha * (alpha - 1))) := by
  have hzero : Tendsto (fun s =>
      deriv (deriv (fun t => f t - c * Real.rpow t alpha)) s /
        Real.rpow s (alpha - 2)) atTop (𝓝 0) := by
    apply scalar_tail_ratio _ (alpha - 2) 0
    simpa only [zero_mul, sub_zero, show alpha - 2 - 3 = alpha - 5 by ring] using hr
  have ht := hzero.add_const (c * alpha * (alpha - 1))
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have _h_inl_8 : deriv (deriv (fun t => f t - c * Real.rpow t alpha)) s =
      deriv (deriv f) s - c * alpha * (alpha - 1) * Real.rpow s (alpha - 2) := by
      have he : deriv (fun t => f t - c * Real.rpow t alpha) =ᶠ[𝓝 s]
          fun t => deriv f t - c * alpha * Real.rpow t (alpha - 1) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        exact scalar_power_remainder_deriv f alpha c t ht (hf.differentiable (by norm_num) t)
      rw [he.deriv_eq]
      have hp := (Real.hasDerivAt_rpow_const (p := alpha - 1) (Or.inl hs.ne')).const_mul
        (c * alpha)
      have hd := (hf.differentiable_deriv_two s).hasDerivAt.sub hp
      simpa only [Real.rpow_eq_pow, Pi.sub_def, Pi.mul_def,
        show alpha - 1 - 1 = alpha - 2 by ring, mul_assoc] using hd.deriv

    /- A differentiated power remainder gives a finite normalized first-derivative limit. -/
  rw [_h_inl_8]
  have hp : Real.rpow s (alpha - 2) ≠ 0 := by
    simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hs (alpha - 2)).ne'
  field_simp
  ring

/- The actual positive-ray remainder derivatives agree locally with the U-branch derivatives. -/
theorem scalar_isBigO_of_power_ratio (f : ℝ → ℝ) (beta c )
    (ht : Tendsto (fun s => f s / Real.rpow s beta) atTop (𝓝 c)) :
    IsBigO atTop f (fun s => Real.rpow s beta) := by
  refine isBigO_of_div_tendsto_nhds ?_ c ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hp : Real.rpow s beta ≠ 0 := by
      simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hs beta).ne'
    exact fun hz => False.elim (hp hz)
  · simpa only [Pi.div_def] using ht

/- Both actual velocity derivative orders have their leading power bounds on the positive ray. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
