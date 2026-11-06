module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsEuler
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsCoefficients
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsLaplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Gamma-normalized algebraic expansion for positive first parameter

Euler's representation and its moment expansion give the literal Kummer normalization.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set Filter Asymptotics

/- The full Gamma polynomial equals the normalized algebraic expansion. -/
theorem M_negative_expansion_positive (a : ℝ) (b : Pos)
    (ha : 0 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => X ^ (-a - (N : ℝ))) := by
  have _h_xinl_0 : IsBigO atTop (fun X => (∫ t in (0 : ℝ)..1, eulerLaplace a (b.1 - a) X t) - gammaPolynomial a (b.1 - a) N X) (fun X => X ^ (-a - (N : ℝ))) := by
    let c := (b.1 - a)
    have hc := (sub_pos.mpr hab)
    have _h_xinl_0 : IsBigO atTop (fun X => ∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t) (fun X => X ^ (-a - (N : ℝ))) := by
      let r := (-a - (N : ℝ))
      have he : IsBigO atTop (fun X : ℝ => Real.exp (-(X / 2))) (fun X => X ^ r) := by
        simpa only [neg_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg] using
          (isLittleO_exp_neg_mul_rpow_atTop (a := 1 / 2) (by norm_num) r).isBigO
      apply IsBigO.trans ?_ he
      refine IsBigO.of_bound (∫ t in (0 : ℝ)..1, betaWeight a c t) ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm] using
        eulerLaplace_tail_bound a c X ha hc hX
    have h := ((eulerLaplace_near_remainder_isBigO a c N ha hc).add
      (polynomialLaplace_half_isBigO a c (-a - (N : ℝ)) N ha)).add
      _h_xinl_0
    apply h.congr_left
    intro X
    have he := intervalIntegrable_eulerLaplace a c X ha hc
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (he.mono_set (by
        rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
        intro t ht
        exact ⟨ht.1, by linarith only [ht.2]⟩ : uIcc (0 : ℝ) (1 / 2) ⊆ uIcc 0 1))
      (he.mono_set (by
        rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
        intro t ht
        exact ⟨by linarith only [ht.1], ht.2⟩ : uIcc (1 / 2 : ℝ) 1 ⊆ uIcc 0 1))
    linarith only [hs]
  apply (_h_xinl_0 |>.const_mul_left (Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)))).congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [M_euler_integral a b ha hab (-X)]
    have he : (∫ t in (0 : ℝ)..1, Real.exp (-X * t) * betaWeight a (b.1 - a) t) =
        ∫ t in (0 : ℝ)..1, eulerLaplace a (b.1 - a) X t := by
      apply intervalIntegral.integral_congr
      intro t _
      change Real.exp (-X * t) * betaWeight a (b.1 - a) t =
        betaWeight a (b.1 - a) t * Real.exp (-(X * t))
      rw [neg_mul, mul_comm]
    have _h_inl_7 : Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)) *
      gammaPolynomial a (b.1 - a) N X = mExpansion a b.1 N X := by
        have hGa := ne_of_gt (Real.Gamma_pos_of_pos ha)
        have hGc := ne_of_gt (Real.Gamma_pos_of_pos (sub_pos.mpr hab))
        simp only [gammaPolynomial, mExpansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [Gamma_add_nat a ha n]
        have he : X ^ (-(a + n)) = X ^ (-a) * X⁻¹ ^ n := by
          rw [show -(a + (n : ℝ)) = -a + -(n : ℝ) by ring,
            Real.rpow_add hX, Real.rpow_neg hX.le (n : ℝ), Real.rpow_natCast, inv_pow]
        rw [he, show 1 - (b.1 - a) = a - b.1 + 1 by ring]
        field_simp
        change Real.Gamma b.1 * poch (a - b.1 + 1) n * Real.rpow X (-a) * poch a n =
          Real.Gamma b.1 * poch (a - b.1 + 1) n * poch a n * Real.rpow X (-a)
        ring

      /- The negative-axis expansion for a positive first parameter. -/
    rw [he, mul_sub, _h_inl_7]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
