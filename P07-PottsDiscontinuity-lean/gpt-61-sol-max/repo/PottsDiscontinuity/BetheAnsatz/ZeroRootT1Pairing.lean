module

public import Mathlib

/-!
# Abstract cancellation of a simple pole against a first-order zero

The paired T₁ summand has a pole of residue `i ĝ` and a factor vanishing to
first order. This lemma isolates the analytic multiplication step from the
permutation and word combinatorics.
-/

@[expose] public section

open Complex Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- A first-order zero cancels a pole with residue `i*h`, leaving `h*d`.
The derivative is written as `i*d`, matching the phase convention `exp(iθ)`. -/
theorem tendsto_pole_mul_one_sub_of_hasDerivAt {f g : ℝ → ℂ} {h d : ℂ}
    (hf : HasDerivAt f (I * d) 0) (hf0 : f 0 = 1)
    (hg : Tendsto (fun t : ℝ => (t : ℂ) * g t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (I * h))) :
    Tendsto (fun t : ℝ => g t * (1 - f t)) (𝓝[≠] (0 : ℝ)) (𝓝 (h * d)) := by
  have hquot : Tendsto (fun t  => (1 - f t) /  t )
      (𝓝[≠] 0) (𝓝 (-(I * d))) := by
    have hslope := hf.tendsto_slope_zero.neg
    
    rw [(by
           simp_all <;> grind : (fun t  => (1 - f t) / (t )) =
        fun t => -(t⁻¹ • (f (0 + t) - f 0)))]
    exact hslope
  have hprod := hg.mul hquot
   
  rw [(by
         calc
            I * h  *  -(I * d)  = -(I * I) * (h * d) := by ring
           _ = h * d := by simp :  I * h  *  -(I * d)  = h * d)] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  calc
     t  * g t * ((1 - f t) /  t ) =
         t  * g t * ((1 - f t) * (t : ℂ)⁻¹) := by rw [div_eq_mul_inv]
    _ = g t * (1 - f t) := by field_simp

end PottsDiscontinuity.BetheAnsatz
