/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GMC.Moments.WeightedDyadic

/-!
# Dyadic decomposition of the finite-cutoff root kernel

The singular kernel is clipped at a strictly positive circle radius. The innermost piece
is retained as an actual disk, while only dyadic radii above the cutoff contribute to
the shell sum. No atomlessness or independence of spatial masses is used.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]


/-- Dyadic reference radii for the rooted mass decomposition. -/
def gmcDyadicRadius (R : ℝ) (n : ℕ) : ℝ := R / (2 : ℝ) ^ n

/-- Only scales at least as large as the cutoff enter the dyadic sum. -/
def gmcClippedDyadicTerm
    (μ : Measure ℂ) (γ R δ : ℝ) (u : ℂ) (n : ℕ) : ℝ≥0∞ :=
  if δ ≤ gmcDyadicRadius R n then
    ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2)) *
      μ (Metric.ball u (gmcDyadicRadius R n))
  else 0

/-- Spatial indicator for one active dyadic root scale. -/
def gmcClippedDyadicIndicator
    (γ R δ : ℝ) (u : ℂ) (n : ℕ) : ℂ → ℝ≥0∞ :=
  if δ ≤ gmcDyadicRadius R n then
    (Metric.ball u (gmcDyadicRadius R n)).indicator
      (fun _ => ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2)))
  else fun _ => 0





/-- The actual clipped insertion mass is bounded by the inner disk, bounded outer piece,
and active dyadic ball masses. In particular, the cutoff is never silently discarded. -/
theorem gmc_clipped_mass_le_dyadic
    (μ : Measure ℂ) (γ R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ)
    (u : ℂ) (O : Set ℂ) :
    (∫⁻ x in O, ENNReal.ofReal ((max ‖x - u‖ δ) ^ (-γ ^ 2)) ∂μ) ≤
      ENNReal.ofReal (δ ^ (-γ ^ 2)) * μ (Metric.ball u (2 * δ)) +
        ENNReal.ofReal (R ^ (-γ ^ 2)) * μ O +
          ∑' n : ℕ, gmcClippedDyadicTerm μ γ R δ u n := by
  have gmcClippedDyadicTerm_restrict_le (n : ℕ) : gmcClippedDyadicTerm (μ.restrict O) γ R δ u n ≤ gmcClippedDyadicTerm μ γ R δ u n := by
    unfold gmcClippedDyadicTerm
    split_ifs
    · exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    · exact le_rfl
  have lintegral_gmcClippedDyadicIndicator (μ : Measure ℂ) (γ R δ : ℝ) (u : ℂ) (n : ℕ) : (∫⁻ x, gmcClippedDyadicIndicator γ R δ u n x ∂μ) =
        gmcClippedDyadicTerm μ γ R δ u n := by
    unfold gmcClippedDyadicIndicator gmcClippedDyadicTerm
    split_ifs
    · exact lintegral_indicator_const Metric.isOpen_ball.measurableSet _
    · exact lintegral_zero
  have gmc_clipped_kernel_le_dyadic (x : ℂ) : ENNReal.ofReal ((max ‖x - u‖ δ) ^ (-γ ^ 2)) ≤
        (Metric.ball u (2 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2))) x +
          ENNReal.ofReal (R ^ (-γ ^ 2)) +
            ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x := by
    have hpow := neg_nonpos.mpr (sq_nonneg γ)
    by_cases hdδ : ‖x - u‖ ≤ δ
    · have hx : x ∈ Metric.ball u (2 * δ) := by
        rw [Metric.mem_ball, dist_eq_norm]
        linarith
      rw [max_eq_right hdδ, Set.indicator_of_mem hx]
      exact (le_add_of_nonneg_right (zero_le)).trans (le_add_of_nonneg_right (zero_le))
    · have hd : 0 < ‖x - u‖ := hδ.trans (lt_of_not_ge hdδ)
      by_cases hdR : R ≤ ‖x - u‖
      · have hp := Real.rpow_le_rpow_of_nonpos hR (hdR.trans (le_max_left ‖x - u‖ δ)) hpow
        have he := ENNReal.ofReal_le_ofReal hp
        exact he.trans ((le_add_of_nonneg_left (zero_le)).trans
          (le_add_of_nonneg_right (zero_le)))
      · obtain ⟨n, hlo, hhi⟩ := exists_dyadic_shell_index hd (lt_of_not_ge hdR)
        have hactive : δ ≤ gmcDyadicRadius R n :=
          (le_of_not_ge hdδ).trans hhi.le
        have hx : x ∈ Metric.ball u (gmcDyadicRadius R n) := by
          simpa only [Metric.mem_ball, dist_eq_norm, gmcDyadicRadius] using hhi
        have hcoef := Real.rpow_le_rpow_of_nonpos
          (show 0 < R / (2 : ℝ) ^ (n + 1) by positivity)
          (hlo.trans (le_max_left ‖x - u‖ δ)) hpow
        have ht : ENNReal.ofReal ((max ‖x - u‖ δ) ^ (-γ ^ 2)) ≤
            gmcClippedDyadicIndicator γ R δ u n x := by
          rw [gmcClippedDyadicIndicator, ite_eq_left hactive, Set.indicator_of_mem hx]
          exact ENNReal.ofReal_le_ofReal hcoef
        exact (ht.trans (ENNReal.le_tsum (f := fun k : ℕ => gmcClippedDyadicIndicator γ R δ u k x) n)).trans (le_add_of_nonneg_left (zero_le))
  have measurable_gmcClippedDyadicIndicator (n : ℕ) : Measurable (gmcClippedDyadicIndicator γ R δ u n) := by
    unfold gmcClippedDyadicIndicator
    split_ifs
    · exact measurable_const.indicator Metric.isOpen_ball.measurableSet
    · exact measurable_const
  have hinner : Measurable ((Metric.ball u (2 * δ)).indicator
      (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2)))) :=
    measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hs : ∀ n, AEMeasurable (gmcClippedDyadicIndicator γ R δ u n) (μ.restrict O) :=
    fun n => (measurable_gmcClippedDyadicIndicator n).aemeasurable
  calc
    _ ≤ ∫⁻ x in O,
        (Metric.ball u (2 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2))) x +
          ENNReal.ofReal (R ^ (-γ ^ 2)) +
            ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x ∂μ :=
      lintegral_mono (gmc_clipped_kernel_le_dyadic)
    _ = ENNReal.ofReal (δ ^ (-γ ^ 2)) * (μ.restrict O) (Metric.ball u (2 * δ)) +
        ENNReal.ofReal (R ^ (-γ ^ 2)) * μ O +
          ∑' n : ℕ, gmcClippedDyadicTerm (μ.restrict O) γ R δ u n := by
      let f := (Metric.ball u (2 * δ)).indicator
        (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2)))
      let g : ℂ → ℝ≥0∞ := fun _ => ENNReal.ofReal (R ^ (-γ ^ 2))
      let h : ℂ → ℝ≥0∞ := fun x => ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x
      change (∫⁻ x, ((f + g) + h) x ∂(μ.restrict O)) = _
      simp only [Pi.add_apply]
      have hfg : AEMeasurable (fun x => f x + g x) (μ.restrict O) :=
        (hinner.add measurable_const).aemeasurable
      have hf : AEMeasurable f (μ.restrict O) := hinner.aemeasurable
      rw [lintegral_add_left' hfg, lintegral_add_left' hf,
        show f = (Metric.ball u (2 * δ)).indicator
          (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2))) by rfl,
        show g = (fun _ => ENNReal.ofReal (R ^ (-γ ^ 2))) by rfl,
        lintegral_indicator_const Metric.isOpen_ball.measurableSet,
        lintegral_const, Measure.restrict_apply_univ]
      change _ + _ + (∫⁻ x, ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x ∂(μ.restrict O)) = _
      rw [lintegral_tsum hs]
      simp_rw [lintegral_gmcClippedDyadicIndicator]
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)) le_rfl)
      (ENNReal.tsum_le_tsum (gmcClippedDyadicTerm_restrict_le))

section
variable (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
include hX hXc γ

/-- The finite-cutoff starting range needs only the exact first moment, at every cutoff. -/
theorem regularizedGMC_subunit_moment_uniform

 (r q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (O : Set ℂ) (hO : MeasurableSet O) :
    gmcMassMoment P (regularizedGMC P Xc γ r) O q ≤ 1 + gmcReferenceMeasure O := by
  let _ := hX.1
  have hp (v : ℝ≥0∞) : v ^ q ≤ 1 + v := by
    by_cases hv : v ≤ 1
    · have h := ENNReal.rpow_le_rpow hv hq
      rw [ENNReal.one_rpow] at h
      exact h.trans (le_add_of_nonneg_right zero_le)
    · have h := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hv) hq1
      rw [ENNReal.rpow_one] at h
      exact h.trans (le_add_of_nonneg_left zero_le)
  change (∫⁻ ω, (regularizedGMC P Xc γ r ω O) ^ q ∂P) ≤ _
  calc
    _ ≤ ∫⁻ ω, 1 + regularizedGMC P Xc γ r ω O ∂P :=
      lintegral_mono (fun ω => hp _)
    _ = 1 + gmcReferenceMeasure O := by
      rw [lintegral_add_left' (aemeasurable_const : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P),
        lintegral_const, measure_univ, mul_one,
        regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r O hO]

/-- Fine-cutoff ball moments in the starting subunit range carry the exact sharp scaling
exponent. The rescaled cutoff is allowed to be coarse and uses only its proved first moment. -/
theorem regularizedGMC_local_subunit_ball_moment_scale_upper

 (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    {R s t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hs : 0 < s) (hsR : s ≤ R)
    (hcut : Real.exp (-t) ≤ s) (z : ℂ) (hz : ‖z‖ ≤ R) :
    gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball z s) q ≤
      ENNReal.ofReal ((s / R) ^ (2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2)) *
        (1 + gmcReferenceMeasure (Metric.ball 0 R)) := by
  have hbase : R + Real.exp (-t) * (R / s) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hcut (div_nonneg hR.le hs.le)
    have he : s * (R / s) = R := by field_simp
    rw [he] at hm
    linarith
  have htarget : ‖z‖ + s + Real.exp (-t) ≤ 1 := by linarith
  have hscale := regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z hs hsR hR
    (by linarith) (by linarith) hbase htarget q
  rw [hscale]
  exact mul_le_mul' le_rfl (regularizedGMC_subunit_moment_uniform P X hX Xc hXc γ
    (t + Real.log (s / R)) q hq hq1 (Metric.ball 0 R) Metric.isOpen_ball.measurableSet)


end

/-- The dyadic coefficient is an exact geometric progression with exponent `xi-gamma²q`.
This is the scalar cancellation giving the sharp positive-moment threshold. -/
theorem gmc_dyadic_weight_scale_eq_geometric
    (γ q ξ R : ℝ) (hR : 0 < R) (n : ℕ) :
    (gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2 * q) *
        ((gmcDyadicRadius R n) / R) ^ ξ =
      (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) *
        ((2 : ℝ) ^ (-(ξ - γ ^ 2 * q))) ^ n := by
  have hn : 0 < gmcDyadicRadius R n := by unfold gmcDyadicRadius; positivity
  have hn1 : 0 < gmcDyadicRadius R (n + 1) := by unfold gmcDyadicRadius; positivity
  have hlog (k : ℕ) : Real.log (gmcDyadicRadius R k) = Real.log R - k * Real.log 2 := by
    rw [gmcDyadicRadius, Real.log_div hR.ne' (by positivity), Real.log_pow]
  have hlogRatio : Real.log (gmcDyadicRadius R n / R) = -(n : ℝ) * Real.log 2 := by
    rw [Real.log_div hn.ne' hR.ne', hlog]
    ring
  rw [Real.rpow_def_of_pos hn1, Real.rpow_def_of_pos (div_pos hn hR),
    Real.rpow_def_of_pos hR, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(ξ - γ ^ 2 * q))) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    hlog, hlogRatio, Nat.cast_add, Nat.cast_one, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- The actual active dyadic term is measurable on every finite-cutoff source space. -/
theorem measurable_regularizedGMC_clipped_dyadic_term

    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ R t : ℝ) (u : ℂ) (n : ℕ) :
    Measurable (fun ω => gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
      γ R (Real.exp (-t)) u n) := by
  unfold gmcClippedDyadicTerm
  split_ifs
  · exact measurable_const.mul ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
      (regularizedGMC_measurable P X hX Xc hXc γ t))
  · exact measurable_const


/-- The dyadic ratio is strictly below one at precisely the subcritical next order. -/
theorem gmc_clipped_dyadic_ratio_lt_one
    (γ q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2) :
    ENNReal.ofReal ((2 : ℝ) ^ (-((2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) - γ ^ 2 * q))) < 1 := by
  have hc := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hcrit
  have hp : 0 < 2 - γ ^ 2 * (q + 1) / 2 := by nlinarith
  have he : (2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) - γ ^ 2 * q =
      q * (2 - γ ^ 2 * (q + 1) / 2) := by ring
  have hz : -((2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) - γ ^ 2 * q) < 0 := by
    rw [he]
    exact neg_neg_of_pos (mul_pos hq hp)
  exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hz)

section
variable (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
include hX hXc γ hq hq1 t hR hRsmall

/-- The explicit common geometric bound for the sum of active moments. All dependence on
cutoff and root has disappeared, before any limiting GMC argument is used. -/
theorem regularizedGMC_clipped_dyadic_subunit_moment_sum_bound

 (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∑' n : ℕ, ∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
      γ R (Real.exp (-t)) u n) ^ q ∂P) ≤
      ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^
          (-((2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) - γ ^ 2 * q))))⁻¹ *
            (1 + gmcReferenceMeasure (Metric.ball 0 R)) := by
  have regularizedGMC_clipped_dyadic_subunit_moment_bound {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (u : ℂ) (hu : ‖u‖ ≤ R) (n : ℕ) : (∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
        γ R (Real.exp (-t)) u n) ^ q ∂P) ≤
        ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) *
          ENNReal.ofReal ((2 : ℝ) ^ (-((2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) - γ ^ 2 * q))) ^ n *
            (1 + gmcReferenceMeasure (Metric.ball 0 R)) := by
    have regularizedGMC_active_dyadic_ball_subunit_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) {R t : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (u : ℂ) (hu : ‖u‖ ≤ R) (n : ℕ) (hactive : Real.exp (-t) ≤ gmcDyadicRadius R n) : gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball u (gmcDyadicRadius R n)) q ≤
          ENNReal.ofReal (((gmcDyadicRadius R n) / R) ^
            (2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2)) *
              (1 + gmcReferenceMeasure (Metric.ball 0 R)) := by
      have hs : 0 < gmcDyadicRadius R n := by unfold gmcDyadicRadius; positivity
      have hsR : gmcDyadicRadius R n ≤ R := by
        unfold gmcDyadicRadius
        apply (div_le_iff₀ (by positivity)).mpr
        exact ((mul_one R).symm).trans_le (mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le)
      exact regularizedGMC_local_subunit_ball_moment_scale_upper P X hX Xc hXc γ q hq hq1
        hR hRsmall hs hsR hactive u hu
    by_cases ha : Real.exp (-t) ≤ gmcDyadicRadius R n
    · have hn1 : 0 < gmcDyadicRadius R (n + 1) := by unfold gmcDyadicRadius; positivity
      have hc : 0 < (gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2) := Real.rpow_pos_of_pos hn1 _
      have he : (∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
          γ R (Real.exp (-t)) u n) ^ q ∂P) =
          ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2 * q)) *
            gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball u (gmcDyadicRadius R n)) q := by
        simp only [gmcClippedDyadicTerm, ite_eq_left ha, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          ENNReal.ofReal_rpow_of_pos hc, ← Real.rpow_mul hn1.le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
      rw [he]
      have h := mul_le_mul' (le_refl (ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2 * q))))
        (regularizedGMC_active_dyadic_ball_subunit_bound hq.le hq1 hR hRsmall u hu n ha)
      have hecoef := gmc_dyadic_weight_scale_eq_geometric γ q
        (2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) R hR n
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hn1.le _), hecoef,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)] at h
      exact h
    · simp only [gmcClippedDyadicTerm, ite_eq_right ha, ENNReal.zero_rpow_of_pos hq, lintegral_zero]
      exact zero_le
  have h := ENNReal.tsum_le_tsum (fun n =>
    regularizedGMC_clipped_dyadic_subunit_moment_bound
      (t := t) hR hRsmall u hu n)
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric] at h
  exact h

/-- The innermost cutoff disk has the same sharp exponent as the dyadic shells. Its
rescaled cutoff is coarse, but its subunit reference moment is already uniformly bounded. -/
theorem regularizedGMC_inner_clipped_subunit_moment_bound

 (hcut : 2 * Real.exp (-t) ≤ R)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    (∫⁻ ω, (ENNReal.ofReal ((Real.exp (-t)) ^ (-γ ^ 2)) *
      regularizedGMC P Xc γ t ω (Metric.ball u (2 * Real.exp (-t)))) ^ q ∂P) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) *
        R ^ (-(2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2)) *
          (Real.exp (-t)) ^ ((2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2) - γ ^ 2 * q)) *
        (1 + gmcReferenceMeasure (Metric.ball 0 R)) := by
  let δ := Real.exp (-t)
  let ξ := 2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2
  have hδ : 0 < δ := Real.exp_pos _
  have hc : 0 < δ ^ (-γ ^ 2) := Real.rpow_pos_of_pos hδ _
  have he : (∫⁻ ω, (ENNReal.ofReal (δ ^ (-γ ^ 2)) *
      regularizedGMC P Xc γ t ω (Metric.ball u (2 * δ))) ^ q ∂P) =
      ENNReal.ofReal (δ ^ (-γ ^ 2 * q)) *
        gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball u (2 * δ)) q := by
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.ofReal_rpow_of_pos hc,
      ← Real.rpow_mul hδ.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  change _ ≤ ENNReal.ofReal ((2 : ℝ) ^ ξ * R ^ (-ξ) * δ ^ (ξ - γ ^ 2 * q)) * _
  rw [he]
  have hb := regularizedGMC_local_subunit_ball_moment_scale_upper P X hX Xc hXc γ q hq.le hq1
    hR hRsmall (mul_pos (by norm_num) hδ) hcut (by dsimp [δ]; linarith [Real.exp_pos (-t)]) u hu
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (δ ^ (-γ ^ 2 * q)))) hb
  have hecoef : δ ^ (-γ ^ 2 * q) * ((2 * δ) / R) ^ ξ =
      (2 : ℝ) ^ ξ * R ^ (-ξ) * δ ^ (ξ - γ ^ 2 * q) := by
    rw [Real.div_rpow (by positivity) hR.le, Real.mul_rpow (by norm_num) hδ.le,
      div_eq_mul_inv, ← Real.rpow_neg hR.le, sub_eq_add_neg, Real.rpow_add hδ]
    ring_nf
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hecoef] at h
  exact h


end
end DOZZ.Proofs
