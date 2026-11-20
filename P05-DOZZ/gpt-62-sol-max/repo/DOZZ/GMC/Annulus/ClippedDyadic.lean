/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GMC.Moments.WeightedDyadic
public import DOZZ.GMC.Moments.PositiveExponent

/-!
# Dyadic decomposition of the finite-cutoff root kernel

The singular kernel is clipped at a strictly positive circle radius. The innermost piece
is retained as an actual disk, while only dyadic radii above the cutoff contribute to
the shell sum. No atomlessness or independence of spatial masses is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Dyadic reference radii for the rooted mass decomposition. -/
noncomputable def gmcDyadicRadius (R : ℝ) (n : ℕ) : ℝ := R / (2 : ℝ) ^ n

/-- Only scales at least as large as the cutoff enter the dyadic sum. -/
noncomputable def gmcClippedDyadicTerm
    (μ : Measure ℂ) (γ R δ : ℝ) (u : ℂ) (n : ℕ) : ℝ≥0∞ :=
  if δ ≤ gmcDyadicRadius R n then
    ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2)) *
      μ (Metric.ball u (gmcDyadicRadius R n))
  else 0

/-- Spatial indicator for one active dyadic root scale. -/
noncomputable def gmcClippedDyadicIndicator
    (γ R δ : ℝ) (u : ℂ) (n : ℕ) : ℂ → ℝ≥0∞ :=
  if δ ≤ gmcDyadicRadius R n then
    (Metric.ball u (gmcDyadicRadius R n)).indicator
      (fun _ => ENNReal.ofReal ((gmcDyadicRadius R (n + 1)) ^ (-γ ^ 2)))
  else fun _ => 0

/-- Each dyadic indicator is measurable, whether or not its scale is active. -/
theorem measurable_gmcClippedDyadicIndicator (γ R δ : ℝ) (u : ℂ) (n : ℕ) :
    Measurable (gmcClippedDyadicIndicator γ R δ u n) := by
  unfold gmcClippedDyadicIndicator
  split_ifs
  · exact measurable_const.indicator Metric.isOpen_ball.measurableSet
  · exact measurable_const

/-- The clipped singular kernel is covered pointwise by the innermost disk, a bounded outer
piece, and the active dyadic indicators. The inner disk includes the cutoff boundary. -/
theorem gmc_clipped_kernel_le_dyadic
    (γ R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) (u x : ℂ) :
    ENNReal.ofReal ((max ‖x - u‖ δ) ^ (-γ ^ 2)) ≤
      (Metric.ball u (2 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2))) x +
        ENNReal.ofReal (R ^ (-γ ^ 2)) +
          ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x := by
  have hpow : -γ ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg γ)
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

section
variable (μ : Measure ℂ)

/-- Integrating one active indicator gives exactly its actual dyadic ball mass. -/
theorem lintegral_gmcClippedDyadicIndicator (γ R δ : ℝ) (u : ℂ) (n : ℕ) :
    (∫⁻ x, gmcClippedDyadicIndicator γ R δ u n x ∂μ) =
      gmcClippedDyadicTerm μ γ R δ u n := by
  unfold gmcClippedDyadicIndicator gmcClippedDyadicTerm
  split_ifs
  · exact lintegral_indicator_const Metric.isOpen_ball.measurableSet _
  · exact lintegral_zero

/-- Restricting a measure decreases every active dyadic term. -/
theorem gmcClippedDyadicTerm_restrict_le (O : Set ℂ) (γ R δ : ℝ) (u : ℂ) (n : ℕ) :
    gmcClippedDyadicTerm (μ.restrict O) γ R δ u n ≤ gmcClippedDyadicTerm μ γ R δ u n := by
  unfold gmcClippedDyadicTerm
  split_ifs
  · exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
  · exact le_rfl

/-- The actual clipped insertion mass is bounded by the inner disk, bounded outer piece,
and active dyadic ball masses. In particular, the cutoff is never silently discarded. -/
theorem gmc_clipped_mass_le_dyadic (γ R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ)
    (u : ℂ) (O : Set ℂ) :
    (∫⁻ x in O, ENNReal.ofReal ((max ‖x - u‖ δ) ^ (-γ ^ 2)) ∂μ) ≤
      ENNReal.ofReal (δ ^ (-γ ^ 2)) * μ (Metric.ball u (2 * δ)) +
        ENNReal.ofReal (R ^ (-γ ^ 2)) * μ O +
          ∑' n : ℕ, gmcClippedDyadicTerm μ γ R δ u n := by
  have hinner : Measurable ((Metric.ball u (2 * δ)).indicator
      (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2)))) :=
    measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hs : ∀ n, AEMeasurable (gmcClippedDyadicIndicator γ R δ u n) (μ.restrict O) :=
    fun n => (measurable_gmcClippedDyadicIndicator γ R δ u n).aemeasurable
  calc
    _ ≤ ∫⁻ x in O,
        (Metric.ball u (2 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2))) x +
          ENNReal.ofReal (R ^ (-γ ^ 2)) +
            ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x ∂μ :=
      lintegral_mono (gmc_clipped_kernel_le_dyadic γ R δ hR hδ u)
    _ = ENNReal.ofReal (δ ^ (-γ ^ 2)) * (μ.restrict O) (Metric.ball u (2 * δ)) +
        ENNReal.ofReal (R ^ (-γ ^ 2)) * μ O +
          ∑' n : ℕ, gmcClippedDyadicTerm (μ.restrict O) γ R δ u n := by
      let f  := (Metric.ball u (2 * δ)).indicator
        (fun _ => ENNReal.ofReal (δ ^ (-γ ^ 2)))
      let g : ℂ → ℝ≥0∞ := fun _ => ENNReal.ofReal (R ^ (-γ ^ 2))
      let h  := fun x => ∑' n : ℕ, gmcClippedDyadicIndicator γ R δ u n x
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
      (ENNReal.tsum_le_tsum (gmcClippedDyadicTerm_restrict_le μ O γ R δ u))

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include Ω X hX hXc

/-- The finite-cutoff starting range needs only the exact first moment, at every cutoff. -/
theorem regularizedGMC_subunit_moment_uniform
    (γ r q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (O : Set ℂ) (hO : MeasurableSet O) :
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

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include Ω X hX hXc

/-- The actual active dyadic term is measurable on every finite-cutoff source space. -/
theorem measurable_regularizedGMC_clipped_dyadic_term
    (γ R t : ℝ) (u : ℂ) (n : ℕ) :
    Measurable (fun ω => gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
      γ R (Real.exp (-t)) u n) := by
  unfold gmcClippedDyadicTerm
  split_ifs
  · exact measurable_const.mul ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
      (regularizedGMC_measurable P X hX Xc hXc γ t))
  · exact measurable_const

end

/-- The sharp exponent remaining after the singular covariance insertion. -/
noncomputable def gmcRootAnnularExponent (γ q : ℝ) : ℝ := gmcScaleExponent γ q - γ ^ 2 * q

section
variable (γ q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2)
include hγ hq hcrit

/-- The root annular exponent is strictly positive at the next subcritical order. -/
theorem gmcRootAnnularExponent_pos :
    0 < gmcRootAnnularExponent γ q := by
  have hc  := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hcrit
  have hp : 0 < 2 - γ ^ 2 * (q + 1) / 2 := by nlinarith
  have he : gmcRootAnnularExponent γ q = q * (2 - γ ^ 2 * (q + 1) / 2) := by
    unfold gmcRootAnnularExponent gmcScaleExponent
    ring
  rw [he]
  exact mul_pos hq hp

/-- The dyadic ratio is strictly below one at precisely the subcritical next order. -/
theorem gmc_clipped_dyadic_ratio_lt_one :
    ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)) < 1 :=
  ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_neg_of_pos (gmcRootAnnularExponent_pos γ q hγ hq hcrit)))

end

end DOZZ.Proofs
