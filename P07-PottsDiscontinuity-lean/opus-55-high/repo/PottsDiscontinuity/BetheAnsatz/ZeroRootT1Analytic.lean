module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT0Limit

/-!
# Local analytic input for the paired T₁ limit

The only pole in a paired ML-edge contribution is the moved-root factor `L(e^{it})`.
This module records its residue with the complex phase convention used in the source.
-/

public section

open Complex Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- The derivative of the unit phase `z(t)=exp(i t)` at zero. -/
theorem hasDerivAt_z_zero : HasDerivAt z I 0 := by
  convert! (hasDerivAt_exp_smul_const (I : ℂ) (0 : ℂ)).comp_ofReal using 1
  · ext t
    simp [z, smul_eq_mul, mul_comm, Complex.exp_eq_exp_ℂ]
  simp

/-- The exponential denominator has slope `-i` at zero. -/
theorem tendsto_one_sub_z_div_id_zero :
    Tendsto (fun t : ℝ => ((1 - z t) / (t : ℂ))) (𝓝[≠] (0 : ℝ)) (𝓝 (-I)) := by
  have hslope := hasDerivAt_z_zero.tendsto_slope_zero
  have hfun : (fun t : ℝ => ((1 - z t) / (t : ℂ))) =
      fun t => -(t⁻¹ • (z (0 + t) - z 0)) := by
    funext t
    simp
    ring
  simp_all

/-- Dividing `t` by `1-z(t)` has limit `i` on the punctured neighborhood. -/
theorem tendsto_id_div_one_sub_z_zero :
    Tendsto (fun t : ℝ => (t : ℂ) / (1 - z t)) (𝓝[≠] (0 : ℝ)) (𝓝 I) := by
  have h := tendsto_one_sub_z_div_id_zero.inv₀ (by simp : (-I : ℂ) ≠ 0)
  simp_all

/-- The principal pole residue of `L(e^{it})`. -/
theorem tendsto_t_mul_L_z_zero (c : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) * L c (z t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * (c : ℂ) ^ 2)) := by
  have hz : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [z_zero] using hasDerivAt_z_zero.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hregular : Tendsto (fun t : ℝ =>
      (t : ℂ) + (c : ℂ) ^ 2 * (z t * ((t : ℂ) / (1 - z t))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (I * (c : ℂ) ^ 2)) := by
    simpa [mul_comm] using ((continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds).add
      ((tendsto_const_nhds (x := (c : ℂ) ^ 2)).mul (hz.mul tendsto_id_div_one_sub_z_zero))
  grind [L, z]

end PottsDiscontinuity.BetheAnsatz
