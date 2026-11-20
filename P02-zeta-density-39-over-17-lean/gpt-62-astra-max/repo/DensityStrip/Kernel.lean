module
public import TaoTrudgianYang2025.ExponentPairAllHeights
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalLargeValues
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalDichotomy
public import GuthMaynard.NativeSource.GuthMaynard.WeylZeta
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open Real Complex Finset Filter Asymptotics Expdb TaoTrudgianYang2025 GuthMaynard.NativeMoment
open scoped ComplexConjugate FourierTransform
namespace DensityStrip

private theorem log_model (P : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsApproximateModelPhaseFunction Real.log 1 P δ := by
  refine ⟨isModelPhaseFunction_log.1 0, ?_⟩
  simp [modelPhaseErrorAt, iteratedDerivWithin_log_eq_rpow_neg_one, hδ]

private theorem log_sum_norm (N a b : ℕ) (hN : 0 < N) (ha : N ≤ a) (t : ℝ) :
    ‖∑ n ∈ Icc a b, (n : ℂ) ^ (-(t:ℂ)*I)‖ =
    ‖exponentialSumAt Real.log (t/(2*π)) N a b‖ := by
  let c := Complex.exp ((t * Real.log N : ℝ) * I)
  have hc : ‖c‖ = 1 := by simp only [c, Complex.norm_exp, mul_I_re, ofReal_im, neg_zero, Real.exp_zero]
  rw [← Complex.norm_conj, ← one_mul ‖exponentialSumAt ..‖, ← hc, ← norm_mul,
    map_sum, exponentialSumAt, mul_sum]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn' := hN.trans_le (ha.trans (mem_Icc.mp hn).1)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn'.ne'), ← Complex.exp_conj,
    oscillatory, Real.fourierChar_apply, ← Complex.exp_add]
  rw [Real.log_div (by positivity) (by positivity)]
  have hp : 2*π ≠ 0 := by positivity
  rw [show 2*π*(t/(2*π)*(Real.log n-Real.log N)) = t*(Real.log n-Real.log N) by field_simp]
  congr 1
  simp only [← Complex.natCast_log, map_mul, map_neg, Complex.conj_ofReal, conj_I, ofReal_mul, ofReal_sub]
  ring

/-- Exponent-pair estimate in the Dirichlet normalization, including prefixes
and the first derivative term at small ordinates. -/
theorem log_prefix_bound {k l e : ℝ} (h : ExponentPair k l) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N a b : ℕ} {t : ℝ}, 0 < N → N ≤ a → b ≤ 2*N → 0 < t →
      ‖∑ n ∈ Icc a b, (n:ℂ) ^ (-(t:ℂ)*I)‖ ≤
        C*(t^(k+e)*(N:ℝ)^(l-k)+(N:ℝ)/t) := by
  obtain ⟨δ,hδ,P,_,C,hC,hb⟩ := h.allPositiveHeight_bound (σ:=1) zero_lt_one he
  refine ⟨C*(2*π),by positivity,?_⟩
  intro N a b t hN ha hb' ht
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hπ : 1 ≤ 2*π := by linarith [pi_gt_three]
  have hC0 : 0 ≤ C := by linarith
  have hke : 0 ≤ k+e := by linarith [h.inTriangle.1]
  rw [log_sum_norm N a b hN ha]
  apply (hb _ _ Real.log a b (by positivity) (by exact_mod_cast hN)
    (by exact_mod_cast ha) (by exact_mod_cast hb') (log_model P hδ.le)).trans
  rw [Real.div_rpow (by positivity) hn.le, div_mul_eq_mul_div,
    mul_div_assoc, ← Real.rpow_sub hn, show l+e-(k+e)=l-k by ring]
  have hpow := Real.rpow_le_rpow (by positivity) (div_le_self ht.le hπ) hke
  have hscale : 0 ≤ t^(k+e)*(N:ℝ)^(l-k) := by positivity
  calc
    _ ≤ C*(t^(k+e)*(N:ℝ)^(l-k)+(N:ℝ)/(t/(2*π))) := by gcongr
    _ ≤ _ := by
      rw [div_div_eq_mul_div]
      simp only [div_eq_mul_inv]
      nlinarith only [mul_nonneg hC0 (mul_nonneg (sub_nonneg.mpr hπ) hscale)]

end DensityStrip
