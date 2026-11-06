module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT0Limit

/-!
# Local analytic input for the paired T₁ limit

The only pole in a paired ML-edge contribution is the moved-root factor `L(e^{it})`.
This module records its residue with the complex phase convention used in the source.
-/

@[expose] public section

open Complex Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- The derivative of the unit phase `z(t)=exp(i t)` at zero. -/
theorem hasDerivAt_z_zero : HasDerivAt z I 0 := by
  convert! (hasDerivAt_exp_smul_const I  0 ).comp_ofReal using 1
  · ext t
    simp [z, mul_comm, Complex.exp_eq_exp_ℂ]
  · simp

/-- The exponential denominator has slope `-i` at zero. -/
theorem tendsto_one_sub_z_div_id_zero :
    Tendsto (fun t : ℝ =>  (1 - z t) / (t : ℂ) ) (𝓝[≠] (0 : ℝ)) (𝓝 (-I)) := by
  have hslope := hasDerivAt_z_zero.tendsto_slope_zero
  
  rw [(by
         simp_all <;> grind : (fun t  =>  (1 - z t) / (t ) ) =
      fun t => -(t⁻¹ • (z (0 + t) - z 0)))]
  exact hslope.neg

/-- Dividing `t` by `1-z(t)` has limit `i` on the punctured neighborhood. -/
theorem tendsto_id_div_one_sub_z_zero :
    Tendsto (fun t : ℝ => (t : ℂ) / (1 - z t)) (𝓝[≠] (0 : ℝ)) (𝓝 I) := by
  have h := tendsto_one_sub_z_div_id_zero.inv₀ (by simp )
  simp_all

/-- The principal pole residue of `L(e^{it})`. -/
theorem tendsto_t_mul_L_z_zero (c : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) * L c (z t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * (c : ℂ) ^ 2)) := by
  
  have hratio := tendsto_id_div_one_sub_z_zero
  have hprod : Tendsto (fun t  => z t * ( t  / (1 - z t)))
      (𝓝[≠] 0) (𝓝 I) := by
    simpa using (by
                   have hAt  := hasDerivAt_z_zero.continuousAt
                   simpa only [z_zero] using
                     hAt.tendsto.mono_left (nhdsWithin_le_nhds ) : Tendsto z (𝓝[≠] 0) (𝓝 1)).mul hratio
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝 0) := Tendsto.mono_left (ContinuousAt.tendsto (Continuous.continuousAt continuous_ofReal)) nhdsWithin_le_nhds
  have hregular : Tendsto (fun t  =>
       t  +  c  ^ 2 * (z t * ( t  / (1 - z t))))
      (𝓝[≠] 0) (𝓝 (I *  c  ^ 2)) := by
    have hscaled : Tendsto (fun t  =>  c  ^ 2 *
        (z t * ( t  / (1 - z t)))) (𝓝[≠]  0 )
        (𝓝 ( c  ^ 2 * I)) := tendsto_const_nhds.mul hprod
    have hadd := ht.add hscaled
    grind
  have heq : (fun t  =>  t  * L c (z t)) =ᶠ[𝓝[≠] 0]
      fun t =>  t  +  c  ^ 2 * (z t * ((t ) / (1 - z t))) := by
    filter_upwards [eventually_z_ne_one_zero] with t ht
    
    unfold L
    field_simp
  apply hregular.congr'
  filter_upwards [heq] with t ht
  exact ht.symm

end PottsDiscontinuity.BetheAnsatz
