module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsCoefficients
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsLaplace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Euler-integral estimates for the negative-axis expansion

The near-endpoint Taylor error and the far-endpoint exponential tail are estimated separately.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set Filter Asymptotics

/- The negative-axis Euler kernel. -/
def eulerLaplace (a c X t : ℝ) : ℝ := betaWeight a c t * Real.exp (-(X * t))

/- Integrability of the Euler kernel for positive endpoint parameters. -/
theorem intervalIntegrable_eulerLaplace (a c X : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntervalIntegrable (eulerLaplace a c X) volume 0 1 := by
  exact (intervalIntegrable_betaWeight a c ha hc).mul_continuousOn
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(X * t)))).continuousOn

/- Integrability of a Gamma moment on the first half interval. -/
theorem intervalIntegrable_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    IntervalIntegrable (laplaceMoment a X) volume 0 (1 / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact (integrable_laplaceMoment a X ha hX).mono_set Ioc_subset_Ioi_self

/- The first half Gamma moment differs from its full value by an exponentially small tail. -/
theorem laplaceMoment_half_isBigO (a r : ℝ) (ha : 0 < a) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..(1 / 2), laplaceMoment a X t) -
        X ^ (-a) * Real.Gamma a) (fun X => X ^ r) := by
  have _h_xinl_0 : IsBigO atTop (fun X => ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t)
      (fun X => X ^ r) := by
    have he : IsBigO atTop (fun X : ℝ => Real.exp (-(X / 4)))
        (fun X => X ^ (r + a)) := by
      simpa only [neg_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg] using
        (isLittleO_exp_neg_mul_rpow_atTop (a := 1 / 4) (by norm_num) (r + a)).isBigO
    have hp : IsBigO atTop (fun X : ℝ => (X / 2) ^ (-a) * Real.Gamma a)
        (fun X => X ^ (-a)) := by
      refine IsBigO.of_bound ((|(2 : ℝ) ^ (-a)|)⁻¹ * |Real.Gamma a|) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      rw [Real.div_rpow hX.le (by norm_num), Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_div, div_eq_mul_inv]
      ring_nf
      rfl
    have hh := he.mul_atTop_rpow_of_isBigO_rpow (r + a) (-a) r hp (by linarith)
    apply IsBigO.trans ?_ hh
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hn : 0 ≤ ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t := by
      apply setIntegral_nonneg measurableSet_Ioi
      intro t ht
      apply laplaceMoment_nonneg a X t
      change 1 / 2 < t at ht
      linarith only [ht]
    have hb : (∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t) ≤
      Real.exp (-(X / 4)) * ((X / 2) ^ (-a) * Real.Gamma a) := by
        have hi := integrable_laplaceMoment a X ha hX
        have hi2 := integrable_laplaceMoment a (X / 2) ha (half_pos hX)
        have hsub : Ioi (1 / 2 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi (by norm_num)
        have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ laplaceMoment a (X / 2) t :=
          ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => laplaceMoment_nonneg a _ t ht.le)
        calc
          _ ≤ ∫ t in Ioi (1 / 2 : ℝ), Real.exp (-(X / 4)) * laplaceMoment a (X / 2) t := by
            apply setIntegral_mono_on (hi.mono_set hsub)
              ((hi2.mono_set hsub).const_mul (Real.exp (-(X / 4)))) measurableSet_Ioi
            intro t ht
            have hX := hX.le
            have ht := ht.le
            have ht0 : 0 ≤ t := le_trans (by norm_num) ht
            have he : -(X * t) ≤ -(X / 4) - (X / 2) * t := by
              nlinarith only [mul_nonneg hX (sub_nonneg.mpr ht)]
            have heq : Real.exp (-(X / 4) - (X / 2) * t) =
                Real.exp (-(X / 4)) * Real.exp (-((X / 2) * t)) := by
              rw [← Real.exp_add, sub_eq_add_neg]
            have hh2 := Real.exp_le_exp.mpr he
            rw [heq] at hh2
            simpa only [laplaceMoment, mul_left_comm] using
              mul_le_mul_of_nonneg_left hh2 (Real.rpow_nonneg ht0 (a - 1))
          _ = Real.exp (-(X / 4)) * ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a (X / 2) t :=
            integral_const_mul _ _
          _ ≤ Real.exp (-(X / 4)) * ∫ t in Ioi (0 : ℝ), laplaceMoment a (X / 2) t := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact setIntegral_mono_set hi2 hn (Filter.Eventually.of_forall hsub)
          _ = _ := by rw [integral_laplaceMoment a (X / 2) ha (half_pos hX)]

      /- Every discarded Gamma moment is smaller than any prescribed algebraic order. -/
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.rpow_nonneg (half_pos hX).le _)
          (Real.Gamma_pos_of_pos ha).le)), one_mul]
    exact hb
  apply _h_xinl_0.neg_left.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have he := intervalIntegral.integral_Ioi_sub_Ioi
      (integrable_laplaceMoment a X ha hX) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [integral_laplaceMoment a X ha hX] at he
    linarith only [he]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/- The far endpoint of the Euler integral has an exponential bound. -/
theorem eulerLaplace_tail_bound (a c X : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hX : 0 ≤ X) :
    |∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t| ≤
      Real.exp (-(X / 2)) * (∫ t in (0 : ℝ)..1, betaWeight a c t) := by
  have hb := intervalIntegrable_betaWeight a c ha hc
  have he := intervalIntegrable_eulerLaplace a c X ha hc
  have hsub : Set.uIcc (1 / 2 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    intro t ht
    exact ⟨by linarith only [ht.1], ht.2⟩
  have hn : 0 ≤ ∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact mul_nonneg (betaWeight_nonneg a c t ⟨by linarith only [ht.1], ht.2⟩)
      (Real.exp_pos _).le
  rw [abs_of_nonneg hn]
  calc
    _ ≤ ∫ t in (1 / 2 : ℝ)..1, Real.exp (-(X / 2)) * betaWeight a c t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (he.mono_set hsub)
        ((hb.mono_set hsub).const_mul _)
      intro t ht
      rw [eulerLaplace, mul_comm]
      apply mul_le_mul_of_nonneg_right _
        (betaWeight_nonneg a c t ⟨by linarith only [ht.1], ht.2⟩)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hX (sub_nonneg.mpr ht.1)]
    _ = Real.exp (-(X / 2)) * ∫ t in (1 / 2 : ℝ)..1, betaWeight a c t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp (-(X / 2)) * ∫ t in (0 : ℝ)..1, betaWeight a c t := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_mono_set hb.1
        (ae_restrict_of_forall_mem measurableSet_Ioc
          (fun t ht => betaWeight_nonneg a c t ⟨ht.1.le, ht.2⟩))
      exact Filter.Eventually.of_forall (fun t ht => ⟨by linarith only [ht.1], ht.2⟩)

/- The far endpoint is smaller than every prescribed algebraic order. -/
def polynomialLaplace (a c : ℝ) (N : ℕ) (X t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
    laplaceMoment (a + n) X t

/- Multiplying a Gamma kernel by a monomial shifts its moment index. -/
theorem laplaceMoment_mul_pow (a X t : ℝ) (ht : 0 < t) (n : ℕ) :
    laplaceMoment a X t * t ^ n = laplaceMoment (a + n) X t := by
  rw [laplaceMoment, laplaceMoment, ← Real.rpow_natCast, mul_right_comm,
    ← Real.rpow_add ht]
  congr 2
  ring

/- The polynomial Gamma kernel is the Taylor polynomial times the zeroth kernel. -/
theorem eulerLaplace_near_remainder_isBigO (a c : ℝ) (N : ℕ)
    (ha : 0 < a) (hc : 0 < c) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..(1 / 2), eulerLaplace a c X t) -
        ∫ t in (0 : ℝ)..(1 / 2), polynomialLaplace a c N X t)
      (fun X => X ^ (-a - (N : ℝ))) := by
  obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 < C ∧ ∀ X t : ℝ, 0 < t → t ≤ 1 / 2 →
      |eulerLaplace a c X t - polynomialLaplace a c N X t| ≤
        C * laplaceMoment (a + N) X t := by
      obtain ⟨C, hC, hb⟩ := betaFactor_remainder_bound (1 - c) N
      refine ⟨C, hC, ?_⟩
      intro X t ht ht1
      have he : eulerLaplace a c X t =
          laplaceMoment a X t * (1 - t) ^ (-(1 - c)) := by
        rw [eulerLaplace, betaWeight, laplaceMoment]
        rw [show -(1 - c) = c - 1 by ring]
        ring
      have _h_inl_16 : polynomialLaplace a c N X t = laplaceMoment a X t * betaPolynomial (1 - c) N t := by
          simp only [polynomialLaplace, betaPolynomial, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [← laplaceMoment_mul_pow a X t ht n]
          ring

        /- Integrability of the polynomial Gamma kernel on the first half interval. -/
      rw [he, _h_inl_16, ← mul_sub, abs_mul,
        abs_of_nonneg (laplaceMoment_nonneg a X t ht.le)]
      calc
        _ ≤ laplaceMoment a X t * (C * t ^ N) :=
          mul_le_mul_of_nonneg_left (hb t ht.le ht1) (laplaceMoment_nonneg a X t ht.le)
        _ = C * laplaceMoment (a + N) X t := by
          rw [← laplaceMoment_mul_pow a X t ht N]
          ring

    /- The first half Taylor error has the required algebraic order. -/
  have haN := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg N)
  refine IsBigO.of_bound (C * Real.Gamma (a + N)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have he := (intervalIntegrable_eulerLaplace a c X ha hc).mono_set
    (show uIcc (0 : ℝ) (1 / 2) ⊆ uIcc (0 : ℝ) 1 by
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
      intro t ht
      exact ⟨ht.1, by linarith only [ht.2]⟩)
  have hp : IntervalIntegrable (polynomialLaplace a c N X) volume 0 (1 / 2) := by
      have hs := IntervalIntegrable.sum (Finset.range N) (fun n _ =>
        (intervalIntegrable_laplaceMoment (a + n) X
          (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hX).const_mul
          (poch (1 - c) n / (n.factorial : ℝ)))
      convert hs using 1
      ext t
      simp only [polynomialLaplace, Finset.sum_apply]

    /- The Taylor remainder is dominated by the next positive Gamma moment. -/
  rw [← intervalIntegral.integral_sub he hp]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(1 / 2),
        ‖eulerLaplace a c X t - polynomialLaplace a c N X t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..(1 / 2), C * laplaceMoment (a + N) X t := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        (he.sub hp).norm ((intervalIntegrable_laplaceMoment (a + N) X haN hX).const_mul C)
      intro t ht
      exact hb X t ht.1 ht.2.le
    _ = C * ∫ t in (0 : ℝ)..(1 / 2), laplaceMoment (a + N) X t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C * ∫ t in Ioi (0 : ℝ), laplaceMoment (a + N) X t := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_mono_set (integrable_laplaceMoment (a + N) X haN hX)
        (ae_restrict_of_forall_mem measurableSet_Ioi
          (fun t ht => laplaceMoment_nonneg (a + N) X t ht.le))
      exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
    _ = C * Real.Gamma (a + N) * ‖X ^ (-a - (N : ℝ))‖ := by
      rw [integral_laplaceMoment (a + N) X haN hX,
        Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)]
      rw [show -(a + (N : ℝ)) = -a - (N : ℝ) by ring]
      ring

/- Full moments evaluate the polynomial Gamma kernel. -/
def gammaPolynomial (a c : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
    (X ^ (-(a + n)) * Real.Gamma (a + n))

/- Replacing all half moments by full moments costs less than every algebraic order. -/
theorem polynomialLaplace_half_isBigO (a c r : ℝ) (N : ℕ) (ha : 0 < a) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..(1 / 2), polynomialLaplace a c N X t) -
        gammaPolynomial a c N X) (fun X => X ^ r) := by
  have hs : IsBigO atTop
      (fun X => ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
        ((∫ t in (0 : ℝ)..(1 / 2), laplaceMoment (a + n) X t) -
          X ^ (-(a + n)) * Real.Gamma (a + n))) (fun X => X ^ r) := by
    have hn (n : ℕ) (_ : n ∈ Finset.range N) :=
      (laplaceMoment_half_isBigO (a + n) r
        (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n))).const_mul_left
        (poch (1 - c) n / (n.factorial : ℝ))
    convert IsBigO.sum hn using 1
    ext X
    simp only [Finset.sum_apply]
  apply hs.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    simp only [polynomialLaplace, gammaPolynomial]
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul, mul_sub, Finset.sum_sub_distrib]
    · intro n _
      exact (intervalIntegrable_laplaceMoment (a + n) X
        (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hX).const_mul _
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/- The complete Euler integral has its algebraic moment expansion. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
