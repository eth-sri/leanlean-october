module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.EulerIntegral
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal

/-- Compatibility of the two rising-factorial recurrences. -/
theorem poch_shift (a : ℝ) (n : ℕ) :
    a * poch (a + 1) n = (a + n) * poch a n := by
  rw [← poch_succ_left, poch_succ, mul_comm]

/-- The coefficient identity underlying the positive-parameter continuation. -/
theorem coeff_contiguous_succ (a : ℝ) (b : Pos) (n : ℕ) :
    coeff a b (n + 1) = coeff (a + 1) (next b) (n + 1) +
      ((a - b.1) / (b.1 * (b.1 + 1))) * coeff (a + 1) (next (next b)) n := by
  have hb := ne_of_gt b.2
  have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
  have hp1 := ne_of_gt (poch_pos (next b) n)
  have hp2 := ne_of_gt (poch_pos (next (next b)) n)
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs := poch_shift (b.1 + 1) n
  change (b.1 + 1) * poch (next (next b)).1 n =
    (b.1 + 1 + n) * poch (next b).1 n at hs
  simp only [coeff, poch_succ_left a n, poch_succ (a + 1) n,
    poch_succ_left b.1 n, poch_succ_left (next b).1 n,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  change a * poch (a + 1) n / (b.1 * poch (next b).1 n * ((n + 1) * n.factorial)) =
    poch (a + 1) n * (a + 1 + n) /
      ((b.1 + 1) * poch (next (next b)).1 n * ((n + 1) * n.factorial)) +
      (a - b.1) / (b.1 * (b.1 + 1)) *
        (poch (a + 1) n / (poch (next (next b)).1 n * n.factorial))
  field_simp
  nlinarith only [(congrArg (fun x => a * poch (a + 1) n * x) hs)]



/-- The finite negative-axis expansion with its Gamma normalization. -/
def mExpansion (a b : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  Real.Gamma b / Real.Gamma (b - a) * Real.rpow X (-a) *
    ∑ n ∈ Finset.range N, poch a n * poch (a - b + 1) n /
      (n.factorial : ℝ) * X⁻¹ ^ n

/-- Iterated ordinary derivatives, including the zeroth derivative. -/
def jet (j : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[j]) f






/-- The Gamma-normalized coefficient of each negative-axis power. -/
def expansionCoeff (a b : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma b / Real.Gamma (b - a) * poch a n * poch (a - b + 1) n /
    (n.factorial : ℝ)

/-- Writing the finite expansion as individual real powers. -/
theorem mExpansion_eq_sum (a b : ℝ) (N : ℕ) (X : ℝ) (hX : 0 < X) :
    mExpansion a b N X =
      ∑ n ∈ Finset.range N, expansionCoeff a b n * Real.rpow X (-(a + n)) := by
  simp only [mExpansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hx : Real.rpow X (-(a + n)) = Real.rpow X (-a) * X⁻¹ ^ n := by
    change X ^ (-(a + (n : ℝ))) = X ^ (-a) * X⁻¹ ^ n
    rw [show -(a + (n : ℝ)) = -a + -(n : ℝ) by ring,
      Real.rpow_add hX, Real.rpow_neg hX.le (n : ℝ), Real.rpow_natCast, inv_pow]
  rw [hx]
  unfold expansionCoeff
  ring

/-- Raising both parameters matches differentiation of an expansion coefficient. -/
theorem expansionCoeff_deriv (a : ℝ) (b : Pos) (n : ℕ) :
    -(a + n) * expansionCoeff a b.1 n =
      -(a / b.1) * expansionCoeff (a + 1) (b.1 + 1) n := by
  have hb := ne_of_gt b.2
  rw [expansionCoeff, expansionCoeff, Real.Gamma_add_one hb,
    show b.1 + 1 - (a + 1) = b.1 - a by ring,
    show a + 1 - (b.1 + 1) + 1 = a - b.1 + 1 by ring]
  have hsm := congrArg (fun x =>
    -Real.Gamma b.1 * poch (a - b.1 + 1) n * x /
      (Real.Gamma (b.1 - a) * (n.factorial : ℝ))) (poch_shift a n)
  field_simp at hsm ⊢
  nlinarith only [hsm]




/-- The positive Gamma moment kernel at Laplace scale X. -/
def laplaceMoment (a X t : ℝ) : ℝ := t ^ (a - 1) * Real.exp (-(X * t))

/-- The positive-scale Gamma moment is integrable. -/
theorem integrable_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    IntegrableOn (laplaceMoment a X) (Ioi 0) volume := by
  change IntegrableOn (fun t => t ^ (a - 1) * Real.exp (-(X * t))) (Ioi 0) volume
  simpa using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1)
      (b := X) (by linarith only [ha]) zero_lt_one hX

/-- Nonnegativity of the moment kernel. -/
theorem laplaceMoment_nonneg (a X t : ℝ) (ht : 0 ≤ t) : 0 ≤ laplaceMoment a X t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

/-- The full Gamma moment at positive Laplace scale. -/
theorem integral_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    (∫ t in Ioi (0 : ℝ), laplaceMoment a X t) = X ^ (-a) * Real.Gamma a := by
  change (∫ t in Ioi 0, t ^ (a - 1) * Real.exp (-(X * t))) = _
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hX,
    one_div, Real.inv_rpow hX.le, Real.rpow_neg hX.le]






/-- The negative-axis Euler kernel. -/
def eulerLaplace (a c X t : ℝ) : ℝ := betaWeight a c t * Real.exp (-(X * t))


/-- Integrability of a Gamma moment on the first half interval. -/
theorem intervalIntegrable_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    IntervalIntegrable (laplaceMoment a X) volume 0 (1 / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact (integrable_laplaceMoment a X ha hX).mono_set Ioc_subset_Ioi_self




/-- The Euler Taylor polynomial multiplied by the Gamma kernel. -/
def polynomialLaplace (a c : ℝ) (N : ℕ) (X t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
    laplaceMoment (a + n) X t

/-- Multiplying a Gamma kernel by a monomial shifts its moment index. -/
theorem laplaceMoment_mul_pow (a X t : ℝ) (ht : 0 < t) (n : ℕ) :
    laplaceMoment a X t * t ^ n = laplaceMoment (a + n) X t := by
  rw [laplaceMoment, laplaceMoment, ← Real.rpow_natCast, mul_right_comm,
    ← Real.rpow_add ht]
  congr 2
  ring





/-- Full moments evaluate the polynomial Gamma kernel. -/
def gammaPolynomial (a c : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
    (X ^ (-(a + n)) * Real.Gamma (a + n))






/-- The negative-axis expansion for a positive first parameter. -/
theorem M_negative_expansion_positive (a : ℝ) (b : Pos)
    (ha : 0 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => X ^ (-a - (N : ℝ)))   := by
  have eulerLaplace_expansion (c : ℝ) (hc : 0 < c) :
      IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..1, eulerLaplace a c X t) - gammaPolynomial a c N X)
      (fun X => X ^ (-a - (N : ℝ))) := by
    let betaPolynomial (q : ℝ) (N : ℕ) (t : ℝ) :=
      ∑ n ∈ Finset.range N, poch q n / (n.factorial : ℝ) * t ^ n
    have intervalIntegrable_eulerLaplace (X : ℝ) :
        IntervalIntegrable (eulerLaplace a c X) volume 0 1 := by
      exact (intervalIntegrable_betaWeight a c ha hc).mul_continuousOn
        (by fun_prop : Continuous (fun t => Real.exp (-(X * t)))).continuousOn
    have betaFactor_remainder_bound (q : ℝ) :
        ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
        |(1 - t) ^ (-q) - betaPolynomial q N t| ≤ C * t ^ N := by
      have betaFactor_hasFPowerSeries :
          HasFPowerSeriesOnBall (fun t => 1 / (1 - t) ^ q)
          (FormalMultilinearSeries.ofScalars ℝ (fun n => poch q n / (n.factorial : ℝ)))
          0 1 := by
        have multichoose_eq_poch (q : ℝ) (n : ℕ) :
            Ring.multichoose q n = poch q n / (n.factorial : ℝ) := by
          apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
          rw [mul_comm, ← nsmul_eq_mul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
            Polynomial.ascPochhammer_smeval_eq_eval]
          rfl
        convert Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero q using 1
        ext n
        simp [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, ← Ring.multichoose_eq, multichoose_eq_poch]
      have betaPolynomial_eq_partialSum (q : ℝ) (N : ℕ) (t : ℝ) :
          betaPolynomial q N t =
          (FormalMultilinearSeries.ofScalars ℝ
            (fun n => poch q n / (n.factorial : ℝ))).partialSum N t := by
        simp only [betaPolynomial, FormalMultilinearSeries.partialSum,
          FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      have hl : ((3 / 4 : ℝ≥0) : ℝ≥0∞) < 1 := by
        rw [← ENNReal.coe_one, ENNReal.coe_lt_coe]
        norm_num
      obtain ⟨r, hr, C, hC, hb⟩ := (betaFactor_hasFPowerSeries)
        |>.uniform_geometric_approx' hl
      refine ⟨C * (r / (3 / 4)) ^ N, mul_pos hC (pow_pos (div_pos hr.1 (by norm_num)) _), ?_⟩
      intro t ht ht1
      have htball : t ∈ Metric.ball 0 (3 / 4 : ℝ≥0) := by
        simp [Metric.mem_ball, dist_zero_right, abs_of_nonneg ht]
        norm_num
        linarith only [ht1]
      have hh := hb t htball N
      rw [zero_add, one_div, ← Real.rpow_neg (sub_nonneg.mpr (by linarith only [ht1])),
        ← betaPolynomial_eq_partialSum] at hh
      simpa [NNReal.coe_div, NNReal.coe_ofNat, abs_of_nonneg ht, mul_pow, div_pow, mul_assoc, mul_div_assoc, div_mul_eq_mul_div] using hh
    have polynomialLaplace_half_isBigO (r : ℝ) :
        IsBigO atTop
        (fun X => (∫ t in (0 : ℝ)..(1 / 2), polynomialLaplace a c N X t) -
          gammaPolynomial a c N X) (fun X => X ^ r) := by
      have laplaceMoment_half_isBigO (a : ℝ) (ha : 0 < a) :
          IsBigO atTop
          (fun X => (∫ t in (0 : ℝ)..(1 / 2), laplaceMoment a X t) -
            X ^ (-a) * Real.Gamma a) (fun X => X ^ r) := by
        have laplaceMoment_tail_isBigO :
            IsBigO atTop (fun X => ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t)
            (fun X => X ^ r) := by
          have laplaceMoment_tail_bound (X : ℝ) (hX : 0 < X) :
              (∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t) ≤
              Real.exp (-(X / 4)) * ((X / 2) ^ (-a) * Real.Gamma a) := by
            have laplaceMoment_tail_pointwise (t : ℝ) (hX : 0 ≤ X) (ht : 1 / 2 ≤ t) :
                laplaceMoment a X t ≤ Real.exp (-(X / 4)) * laplaceMoment a (X / 2) t := by
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
            have hi2 := integrable_laplaceMoment a (X / 2) ha (half_pos hX)
            have hsub : Ioi (1 / 2 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi (by norm_num)
            have hn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ laplaceMoment a (X / 2) t :=
              ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => laplaceMoment_nonneg a _ t ht.le)
            calc
              _ ≤ ∫ t in Ioi (1 / 2 : ℝ), Real.exp (-(X / 4)) * laplaceMoment a (X / 2) t := by
                apply setIntegral_mono_on ((integrable_laplaceMoment a X ha hX).mono_set hsub)
                  ((hi2.mono_set hsub).const_mul (Real.exp (-(X / 4)))) measurableSet_Ioi
                intro t ht
                exact laplaceMoment_tail_pointwise t hX.le ht.le
              _ = Real.exp (-(X / 4)) * ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a (X / 2) t :=
                integral_const_mul _ _
              _ ≤ Real.exp (-(X / 4)) * ∫ t in Ioi 0, laplaceMoment a (X / 2) t := by
                apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                exact setIntegral_mono_set hi2 hn (Filter.Eventually.of_forall hsub)
              _ = _ := by rw [integral_laplaceMoment a (X / 2) ha (half_pos hX)]
          have he : IsBigO atTop (fun X => Real.exp (-(X / 4)))
              (fun X => X ^ (r + a)) := by
            simpa [neg_div, div_eq_mul_inv, mul_comm, mul_neg] using
              (isLittleO_exp_neg_mul_rpow_atTop (a := 1 / 4) (by norm_num) (r + a)).isBigO
          have hp : IsBigO atTop (fun X => (X / 2) ^ (-a) * Real.Gamma a)
              (fun X => X ^ (-a)) := by
            refine IsBigO.of_bound ((|2 ^ (-a)|)⁻¹ * |Real.Gamma a|) ?_
            filter_upwards [eventually_gt_atTop 0] with X hX
            rw [Real.div_rpow hX.le (by norm_num), Real.norm_eq_abs, Real.norm_eq_abs,
              abs_mul, abs_div, div_eq_mul_inv]
            ring_nf
            rfl
          apply IsBigO.trans ?_ (he.mul_atTop_rpow_of_isBigO_rpow (r + a) (-a) r hp (by linarith))
          refine IsBigO.of_bound 1 ?_
          filter_upwards [eventually_gt_atTop 0] with X hX
          have hn : 0 ≤ ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t := by
            apply setIntegral_nonneg measurableSet_Ioi
            intro t ht
            apply laplaceMoment_nonneg a X t
            change 1 / 2 < t at ht
            linarith only [ht]
          have hb := laplaceMoment_tail_bound X hX
          simp only [Pi.mul_apply]
          rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (Real.rpow_nonneg (half_pos hX).le _)
                (Real.Gamma_pos_of_pos ha).le)), one_mul]
          exact hb
        apply (laplaceMoment_tail_isBigO).neg_left.congr'
        · filter_upwards [eventually_gt_atTop 0] with X hX
          have he := intervalIntegral.integral_Ioi_sub_Ioi
            (integrable_laplaceMoment a X ha hX) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          rw [integral_laplaceMoment a X ha hX] at he
          linarith only [he]
        · exact Filter.Eventually.of_forall (fun _ => rfl)
      have hs : IsBigO atTop
          (fun X => ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
            ((∫ t in (0 : ℝ)..(1 / 2), laplaceMoment (a + n) X t) -
              X ^ (-(a + n)) * Real.Gamma (a + n))) (fun X => X ^ r) := by
        have hn (n : ℕ) (_ : n ∈ Finset.range N) :=
          (laplaceMoment_half_isBigO (a + n)
            (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n))).const_mul_left
            (poch (1 - c) n / (n.factorial : ℝ))
        convert IsBigO.sum hn using 1
        ext X
        simp only [Finset.sum_apply]
      apply hs.congr'
      · filter_upwards [eventually_gt_atTop 0] with X hX
        simp only [polynomialLaplace, gammaPolynomial]
        rw [intervalIntegral.integral_finsetSum]
        · simp only [intervalIntegral.integral_const_mul, mul_sub, Finset.sum_sub_distrib]
        · intro n _
          exact (intervalIntegrable_laplaceMoment (a + n) X
            (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hX).const_mul _
      · exact Filter.Eventually.of_forall (fun _ => rfl)
    have eulerLaplace_near_remainder_isBigO :
        IsBigO atTop
        (fun X => (∫ t in (0 : ℝ)..(1 / 2), eulerLaplace a c X t) -
          ∫ t in (0 : ℝ)..(1 / 2), polynomialLaplace a c N X t)
        (fun X => X ^ (-a - (N : ℝ))) := by
      have eulerLaplace_remainder_pointwise :
          ∃ C : ℝ, 0 < C ∧ ∀ X t : ℝ, 0 < t → t ≤ 1 / 2 →
          |eulerLaplace a c X t - polynomialLaplace a c N X t| ≤
            C * laplaceMoment (a + N) X t := by
        have polynomialLaplace_eq (X : ℝ) (t : ℝ) (ht : 0 < t) :
            polynomialLaplace a c N X t = laplaceMoment a X t * betaPolynomial (1 - c) N t := by
          simp only [polynomialLaplace, betaPolynomial, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [← laplaceMoment_mul_pow a X t ht n]
          ring
        obtain ⟨C, hC, hb⟩ := betaFactor_remainder_bound (1 - c)
        refine ⟨C, hC, ?_⟩
        intro X t ht ht1
        have he : eulerLaplace a c X t =
            laplaceMoment a X t * (1 - t) ^ (-(1 - c)) := by
          rw [eulerLaplace, betaWeight, laplaceMoment]
          rw [show -(1 - c) = c - 1 by ring]
          ring
        rw [he, polynomialLaplace_eq X t ht, ← mul_sub, abs_mul,
          abs_of_nonneg (laplaceMoment_nonneg a X t ht.le)]
        calc
          _ ≤ laplaceMoment a X t * (C * t ^ N) :=
            mul_le_mul_of_nonneg_left (hb t ht.le ht1) (laplaceMoment_nonneg a X t ht.le)
          _ = C * laplaceMoment (a + N) X t := by
            rw [← laplaceMoment_mul_pow a X t ht N]
            ring
      have intervalIntegrable_polynomialLaplace (X : ℝ) (hX : 0 < X) :
          IntervalIntegrable (polynomialLaplace a c N X) volume 0 (1 / 2) := by
        have hs := IntervalIntegrable.sum (Finset.range N) (fun n _ =>
          (intervalIntegrable_laplaceMoment (a + n) X
            (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hX).const_mul
            (poch (1 - c) n / (n.factorial : ℝ)))
        convert hs using 1
        ext t
        simp only [polynomialLaplace, Finset.sum_apply]
      obtain ⟨C, hC, hb⟩ := eulerLaplace_remainder_pointwise
      have haN := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg N)
      refine IsBigO.of_bound (C * Real.Gamma (a + N)) ?_
      filter_upwards [eventually_gt_atTop 0] with X hX
      have he := (intervalIntegrable_eulerLaplace X).mono_set
        (show uIcc 0 (1 / 2) ⊆ uIcc 0 1 by
          rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
          intro t ht
          exact ⟨ht.1, by linarith only [ht.2]⟩)
      have hp := intervalIntegrable_polynomialLaplace X hX
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
        _ ≤ C * ∫ t in Ioi 0, laplaceMoment (a + N) X t := by
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
    have eulerLaplace_tail_isBigO (r : ℝ) :
        IsBigO atTop (fun X => ∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t)
        (fun X => X ^ r) := by
      have eulerLaplace_tail_bound (X : ℝ) (hX : 0 ≤ X) :
          |∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t| ≤
          Real.exp (-(X / 2)) * (∫ t in (0 : ℝ)..1, betaWeight a c t) := by
        have hb := intervalIntegrable_betaWeight a c ha hc
        have he := intervalIntegrable_eulerLaplace X
        have hsub : Set.uIcc (1 / 2 : ℝ) 1 ⊆ Set.uIcc 0 1 := by
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
      have he : IsBigO atTop (fun X => Real.exp (-(X / 2))) (fun X => X ^ r) := by
        simpa [neg_div, div_eq_mul_inv, mul_comm, mul_neg] using
          (isLittleO_exp_neg_mul_rpow_atTop (a := 1 / 2) (by norm_num) r).isBigO
      apply IsBigO.trans ?_ he
      refine IsBigO.of_bound (∫ t in (0 : ℝ)..1, betaWeight a c t) ?_
      filter_upwards [eventually_ge_atTop 0] with X hX
      simpa [abs_of_pos (Real.exp_pos _), mul_comm] using
        eulerLaplace_tail_bound X hX
    have h := ((eulerLaplace_near_remainder_isBigO).add
      (polynomialLaplace_half_isBigO (-a - (N : ℝ)))).add
      (eulerLaplace_tail_isBigO (-a - (N : ℝ)))
    apply h.congr_left
    intro X
    have he := intervalIntegrable_eulerLaplace X
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
  have gammaPolynomial_normalized (X : ℝ) (hX : 0 < X) :
      Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)) *
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
  have h := (eulerLaplace_expansion (b.1 - a) (sub_pos.mpr hab))
    |>.const_mul_left (Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)))
  apply h.congr'
  · filter_upwards [eventually_gt_atTop 0] with X hX
    rw [M_euler_integral a b ha hab (-X)]
    have he : (∫ t in (0 : ℝ)..1, Real.exp (-X * t) * betaWeight a (b.1 - a) t) =
        ∫ t in (0 : ℝ)..1, eulerLaplace a (b.1 - a) X t := by
      apply intervalIntegral.integral_congr
      intro t _
      change Real.exp (-X * t) * betaWeight a (b.1 - a) t =
        betaWeight a (b.1 - a) t * Real.exp (-(X * t))
      rw [neg_mul, mul_comm]
    rw [he, mul_sub, gammaPolynomial_normalized X hX]
  · exact Filter.Eventually.of_forall (fun _ => rfl)









/-- Monotonicity of algebraic asymptotic orders on the positive half-line. -/
theorem rpow_isBigO_of_le (r s : ℝ) (hrs : r ≤ s) :
    IsBigO atTop (fun X : ℝ => X ^ r) (fun X => X ^ s) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hX]) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hX]) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hX hrs


/-- The complete algebraic expansion with its exact remainder order. -/
theorem M_negative_expansion (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => Real.rpow X (-a - (N : ℝ)))    := by
  have expansionCoeff_contiguous_second (n : ℕ) :
      -((a - b.1) / (b.1 * (b.1 + 1))) *
      expansionCoeff (a + 1) (b.1 + 2) n =
      Real.Gamma b.1 / Real.Gamma (b.1 - a) *
        poch (a + 1) n * poch (a - b.1) n / (n.factorial : ℝ) := by
    have hb := ne_of_gt b.2
    have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
    have hc := ne_of_gt (sub_pos.mpr hab)
    have hG := ne_of_gt (Real.Gamma_pos_of_pos (sub_pos.mpr hab))
    rw [expansionCoeff, show b.1 + 2 = (b.1 + 1) + 1 by ring,
      Real.Gamma_add_one hb1, Real.Gamma_add_one hb,
      show (b.1 + 1 + 1) - (a + 1) = (b.1 - a) + 1 by ring,
      Real.Gamma_add_one hc, show a + 1 - (b.1 + 1 + 1) + 1 = a - b.1 by ring]
    field_simp
    ring
  have M_contiguous (z : ℝ) :
      M a b z = M (a + 1) (next b) z +
      ((a - b.1) * z / (b.1 * (b.1 + 1))) * M (a + 1) (next (next b)) z := by
    have hs := (hasSum_M (a + 1) (next (next b)) z).mul_left
      ((a - b.1) * z / (b.1 * (b.1 + 1)))
    have he (n : ℕ) :
        ((a - b.1) * z / (b.1 * (b.1 + 1))) *
          (coeff (a + 1) (next (next b)) n * z ^ n) =
        ((a - b.1) / (b.1 * (b.1 + 1))) *
          coeff (a + 1) (next (next b)) n * z ^ (n + 1) := by
      rw [pow_succ]
      ring
    simp only [he] at hs
    let f : ℕ → ℝ := fun n => (coeff a b n - coeff (a + 1) (next b) n) * z ^ n
    have hf (n : ℕ) : f (n + 1) =
        ((a - b.1) / (b.1 * (b.1 + 1))) *
          coeff (a + 1) (next (next b)) n * z ^ (n + 1) := by
      dsimp [f]
      rw [coeff_contiguous_succ]
      ring
    have hsum : HasSum f
        (((a - b.1) * z / (b.1 * (b.1 + 1))) * M (a + 1) (next (next b)) z) := by
      have h0 : f 0 = 0 := by simp [f]
      simpa [h0] using (hs.congr_fun (fun n => hf n)).zero_add (f := f)
    have hdiff := (hasSum_M a b z).sub (hasSum_M (a + 1) (next b) z)
    have hdiff' : HasSum f (M a b z - M (a + 1) (next b) z) := by
      convert hdiff using 1
      ext n
      dsimp [f]
      ring
    have h := hdiff'.unique hsum
    linarith only [h]
  have M_negative_expansion_succ (N : ℕ) :
      IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 (N + 1) X)
      (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
    have mExpansion_contiguous (X : ℝ) (hX : 0 < X) :
        mExpansion a b.1 (N + 1) X = mExpansion (a + 1) (b.1 + 1) N X +
        (-((a - b.1) / (b.1 * (b.1 + 1))) * X) *
          mExpansion (a + 1) (b.1 + 2) (N + 1) X := by
      have expansionCoeff_contiguous_succ (n : ℕ) :
          expansionCoeff a b.1 (n + 1) = expansionCoeff (a + 1) (b.1 + 1) n +
          -((a - b.1) / (b.1 * (b.1 + 1))) *
            expansionCoeff (a + 1) (b.1 + 2) (n + 1) := by
        rw [expansionCoeff_contiguous_second, expansionCoeff, expansionCoeff,
          Real.Gamma_add_one (ne_of_gt b.2),
          show b.1 + 1 - (a + 1) = b.1 - a by ring,
          show a + 1 - (b.1 + 1) + 1 = a - b.1 + 1 by ring,
          poch_succ_left a n, poch_succ (a - b.1 + 1) n,
          poch_succ (a + 1) n, poch_succ_left (a - b.1) n,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hn : (n + 1 : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      have expansionCoeff_contiguous_zero :
          expansionCoeff a b.1 0 = -((a - b.1) / (b.1 * (b.1 + 1))) *
          expansionCoeff (a + 1) (b.1 + 2) 0 := by
        rw [expansionCoeff_contiguous_second]
        simp only [expansionCoeff, poch_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      rw [mExpansion_eq_sum a b.1 (N + 1) X hX,
        mExpansion_eq_sum (a + 1) (b.1 + 1) N X hX,
        mExpansion_eq_sum (a + 1) (b.1 + 2) (N + 1) X hX]
      let k : ℝ := -((a - b.1) / (b.1 * (b.1 + 1)))
      have hx (n : ℕ) : X * Real.rpow X (-(a + 1 + n)) = Real.rpow X (-(a + n)) := by
        change X * X ^ (-(a + 1 + (n : ℝ))) = X ^ (-(a + n))
        calc
          _ = X ^ 1 * X ^ (-(a + 1 + (n : ℝ))) := by rw [Real.rpow_one]
          _ = X ^ (1 + -(a + 1 + n)) := (Real.rpow_add hX _ _).symm
          _ = _ := by congr 1; ring
      have hm : (k * X) *
          (∑ n ∈ Finset.range (N + 1), expansionCoeff (a + 1) (b.1 + 2) n *
            Real.rpow X (-(a + 1 + n))) =
          ∑ n ∈ Finset.range (N + 1), k * expansionCoeff (a + 1) (b.1 + 2) n *
            Real.rpow X (-(a + n)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        calc
          _ = (k * expansionCoeff (a + 1) (b.1 + 2) n) *
              (X * Real.rpow X (-(a + 1 + n))) := by ring
          _ = _ := by rw [hx]
      change _ = _ + (k * X) * _
      rw [hm]
      have ht (n : ℕ) : expansionCoeff a b.1 (n + 1) *
          Real.rpow X (-(a + (n + 1 : ℕ))) =
          expansionCoeff (a + 1) (b.1 + 1) n * Real.rpow X (-(a + 1 + n)) +
          k * expansionCoeff (a + 1) (b.1 + 2) (n + 1) *
            Real.rpow X (-(a + (n + 1 : ℕ))) := by
        rw [expansionCoeff_contiguous_succ n]
        simp only [Nat.cast_add, Nat.cast_one]
        rw [show a + ((n : ℝ) + 1) = a + 1 + n by ring]
        dsimp [k]
        ring
      have hs := Finset.sum_congr (s₁ := Finset.range N) rfl (fun n _ => ht n)
      rw [Finset.sum_add_distrib] at hs
      simp only [Finset.sum_range_succ', Nat.cast_zero, add_zero]
      rw [expansionCoeff_contiguous_zero]
      change _ + k * _ * _ = _ + (_ + k * _ * _)
      linarith only [hs]
    have ha1 : 0 < a + 1 := by linarith only [ha]
    have hab1 : a + 1 < (next b).1 := by change a + 1 < b.1 + 1; linarith only [hab]
    have hab2 : a + 1 < (next (next b)).1 := by
      change a + 1 < b.1 + 1 + 1
      linarith only [hab]
    have h1 := M_negative_expansion_positive (a + 1) (next b) ha1 hab1 N
    have h2 := M_negative_expansion_positive (a + 1) (next (next b)) ha1 hab2 (N + 1)
    have hb2 : (next (next b)).1 = b.1 + 2 := by dsimp [next]; ring
    rw [hb2] at h2
    have hX : IsBigO atTop (fun X : ℝ => X) (fun X => X ^ (1 : ℝ)) := by
      simpa only [Real.rpow_one] using (isBigO_refl (fun X : ℝ => X) atTop)
    have h2X := hX.mul_atTop_rpow_of_isBigO_rpow 1
      (-(a + 1) - ((N + 1 : ℕ) : ℝ)) (-a - ((N + 1 : ℕ) : ℝ)) h2 (by linarith)
    have h1' : IsBigO atTop
        (fun X => M (a + 1) (next b) (-X) - mExpansion (a + 1) (b.1 + 1) N X)
        (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
      convert h1 using 1
      · rfl
      · ext X
        congr 1
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    have h := h1'.add (h2X.const_mul_left (-((a - b.1) / (b.1 * (b.1 + 1)))))
    apply h.congr'
    · filter_upwards [eventually_gt_atTop 0] with X hXp
      rw [M_contiguous (-X), mExpansion_contiguous X hXp]
      simp only [Pi.mul_apply]
      ring
    · exact Filter.Eventually.of_forall (fun _ => rfl)
  cases N with
  | succ N => exact M_negative_expansion_succ N
  | zero =>
    have h1 := (M_negative_expansion_succ 0).trans
      (rpow_isBigO_of_le (-a - ((0 + 1 : ℕ) : ℝ)) (-a) (by norm_num))
    have h0 : IsBigO atTop (mExpansion a b.1 1) (fun X : ℝ => X ^ (-a)) := by
      have h := (isBigO_refl (fun X : ℝ => X ^ (-a)) atTop)
        |>.const_mul_left (Real.Gamma b.1 / Real.Gamma (b.1 - a))
      convert h using 1
      ext X
      simp [mExpansion]
    have h := h1.add h0
    convert h using 1
    · ext X
      simp only [mExpansion, Finset.range_zero, Finset.sum_empty, mul_zero]
      ring
    · ext X
      simp only [Nat.cast_zero, sub_zero]
      rfl





/-- The expansion error and its first two ordinary derivative jets have exact algebraic orders. -/
theorem M_negative_expansion_jet (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N j : ℕ) (hj : j ≤ 2) :
    IsBigO atTop
      (jet j (fun X => M a b (-X) - mExpansion a b.1 N X))
      (fun X => Real.rpow X (-a - (N : ℝ) - (j : ℝ)))   := by
  have hasDerivAt_M_negative_remainder (a : ℝ) (b : Pos) (X : ℝ) (hX : 0 < X) :
      HasDerivAt (fun Y => M a b (-Y) - mExpansion a b.1 N Y)
      (-(a / b.1) *
        (M (a + 1) (next b) (-X) - mExpansion (a + 1) (next b).1 N X)) X := by
    have hasDerivAt_mExpansion :
        HasDerivAt (mExpansion a b.1 N)
        (-(a / b.1) * mExpansion (a + 1) (b.1 + 1) N X) X := by
      have hd : HasDerivAt
          (fun Y : ℝ => ∑ n ∈ Finset.range N,
            expansionCoeff a b.1 n * Real.rpow Y (-(a + n)))
          (∑ n ∈ Finset.range N, expansionCoeff a b.1 n *
            (-(a + n) * Real.rpow X (-(a + n) - 1))) X := by
        apply HasDerivAt.fun_sum
        intro n _
        exact (Real.hasDerivAt_rpow_const (Or.inl hX.ne')).const_mul _
      have he : (fun Y : ℝ => ∑ n ∈ Finset.range N,
          expansionCoeff a b.1 n * Real.rpow Y (-(a + n))) =ᶠ[nhds X] mExpansion a b.1 N := by
        filter_upwards [eventually_gt_nhds hX] with Y hY
        exact (mExpansion_eq_sum a b.1 N Y hY).symm
      apply (hd.congr_of_eventuallyEq he.symm).congr_deriv
      rw [mExpansion_eq_sum (a + 1) (b.1 + 1) N X hX, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [show -(a + (n : ℝ)) - 1 = -(a + 1 + n) by ring]
      rw [← mul_assoc, mul_comm (expansionCoeff a b.1 n), expansionCoeff_deriv]
      ring
    have hM := (hasDerivAt_M a b (-X)).comp X (hasDerivAt_id X).neg
    have hE := hasDerivAt_mExpansion
    convert hM.sub hE using 1
    · rfl
    · rw [show (next b).1 = b.1 + 1 from rfl]
      ring
  have deriv2_M_negative_remainder (X : ℝ) (hX : 0 < X) :
      deriv (deriv (fun Y => M a b (-Y) - mExpansion a b.1 N Y)) X =
      (-(a / b.1) * -((a + 1) / (next b).1)) *
        (M (a + 1 + 1) (next (next b)) (-X) -
          mExpansion (a + 1 + 1) (next (next b)).1 N X) := by
    have hd := (hasDerivAt_M_negative_remainder (a + 1) (next b) X hX)
      |>.const_mul (-(a / b.1))
    have he : deriv (fun Y => M a b (-Y) - mExpansion a b.1 N Y) =ᶠ[nhds X]
        (fun Y => -(a / b.1) *
          (M (a + 1) (next b) (-Y) - mExpansion (a + 1) (next b).1 N Y)) := by
      filter_upwards [eventually_gt_nhds hX] with Y hY
      exact (hasDerivAt_M_negative_remainder a b Y hY).deriv
    rw [(hd.congr_of_eventuallyEq he).deriv]
    ring
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have hab1 : a + 1 < (next b).1 := by
    change a + 1 < b.1 + 1
    linarith only [hab]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
  · subst j
    simpa only [jet, Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero] using
      M_negative_expansion a b ha hab N
  · subst j
    have h := (M_negative_expansion_positive (a + 1) (next b) ha1 hab1 N)
      |>.const_mul_left (-(a / b.1))
    apply h.congr'
    · filter_upwards [eventually_gt_atTop 0] with X hX
      simpa only [jet, Function.iterate_one, id_eq] using
        (hasDerivAt_M_negative_remainder a b X hX).deriv.symm
    · exact Filter.Eventually.of_forall (fun X => by
        simp only [Nat.cast_one]
        change Real.rpow X (-(a + 1) - (N : ℝ)) =
          Real.rpow X (-a - (N : ℝ) - 1)
        congr 1
        ring)
  · subst j
    have ha2 : 0 < a + 1 + 1 := by linarith only [ha1]
    have hab2 : a + 1 + 1 < (next (next b)).1 := by
      change a + 1 + 1 < b.1 + 1 + 1
      linarith only [hab]
    have h := (M_negative_expansion_positive (a + 1 + 1) (next (next b)) ha2 hab2 N)
      |>.const_mul_left (-(a / b.1) * -((a + 1) / (next b).1))
    apply h.congr'
    · filter_upwards [eventually_gt_atTop 0] with X hX
      simpa only [jet, Function.iterate_succ_apply, Function.iterate_zero, id_eq] using
        (deriv2_M_negative_remainder X hX).symm
    · exact Filter.Eventually.of_forall (fun X => by
        simp only [Nat.cast_ofNat]
        change Real.rpow X (-(a + 1 + 1) - (N : ℝ)) =
          Real.rpow X (-a - (N : ℝ) - 2)
        congr 1
        ring)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

