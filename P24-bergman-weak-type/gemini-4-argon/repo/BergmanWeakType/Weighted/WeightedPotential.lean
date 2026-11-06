/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.Normalizer
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Weighted positive potentials and their normalized circular caps -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real Filter
open scoped Topology ENNReal

namespace BergmanWeakType

def smoothCap (ε c x : ℝ) : ℝ :=
  (x + c - sqrt ((x - c) ^ 2 + ε ^ 2) + ε) / 2

def smoothCapInputDeriv (ε c x : ℝ) : ℝ :=
  (1 - (x - c) / sqrt ((x - c) ^ 2 + ε ^ 2)) / 2

theorem smoothCapInputDeriv_nonneg {ε c x : ℝ} (hε : 0 < ε) :
    0 ≤ smoothCapInputDeriv ε c x := by
  have hp : 0 < sqrt ((x - c) ^ 2 + ε ^ 2) := sqrt_pos.mpr (by positivity)
  have hle : x - c ≤ sqrt ((x - c) ^ 2 + ε ^ 2) :=
    (le_abs_self _).trans <| sqrt_sq_eq_abs (x - c) ▸
      sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  unfold smoothCapInputDeriv
  linarith [(div_le_one hp).mpr hle]

theorem hasDerivAt_smoothCap_input {ε c x : ℝ} (hε : 0 < ε) :
    HasDerivAt (smoothCap ε c) (smoothCapInputDeriv ε c x) x := by
  unfold smoothCap
  have hn : (x - c) ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have hs := (((hasDerivAt_id x).sub_const c).pow 2 |>.add_const (ε ^ 2)).sqrt hn
  convert (((hasDerivAt_id x).add_const c).sub hs |>.add_const ε).div_const 2 using 1 <;>
    dsimp [smoothCap, smoothCapInputDeriv]
  ring

theorem hasDerivAt_smoothCapInputDeriv {ε c x : ℝ} (hε : 0 < ε) :
    HasDerivAt (smoothCapInputDeriv ε c)
      (-(ε ^ 2) / (2 * sqrt ((x - c) ^ 2 + ε ^ 2) ^ 3)) x := by
  have hp : 0 < (x - c) ^ 2 + ε ^ 2 := by positivity
  have hs := (((hasDerivAt_id x).sub_const c).pow 2 |>.add_const (ε ^ 2)).sqrt hp.ne'
  have hr := ((hasDerivAt_id x).sub_const c).div hs (sqrt_pos.mpr hp).ne'
  unfold smoothCapInputDeriv
  convert (hr.const_sub 1).div_const 2 using 1 <;> dsimp
  have heq := sq_sqrt hp.le
  field_simp [(sqrt_pos.mpr hp).ne']
  nlinarith

namespace Weighted

def angularMean (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F r θ

theorem continuousOn_angularMean {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (S ×ˢ univ)) :
    ContinuousOn (angularMean F) S := by
  have hc : Continuous (fun p : S × ℝ ↦ F p.1 p.2) :=
    continuousOn_univ.mp <| hF.comp
      (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd).continuousOn
      fun p _ ↦ ⟨p.1.property, mem_univ _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hc 0 (2 * π)).const_mul _

theorem hasDerivAt_angularMean {F Fr : ℝ → ℝ → ℝ} {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFr : ContinuousOn (fun p : ℝ × ℝ ↦ Fr p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r) :
    HasDerivAt (angularMean F) (angularMean Fr r) r := by
  let S := Icc (r / 2) ((r + 1) / 2)
  have hS : S ∈ nhds r := Icc_mem_nhds (by linarith [hr.1]) (by linarith [hr.2])
  have hsub : S ×ˢ Icc (0 : ℝ) (2 * π) ⊆ Ico 0 1 ×ˢ univ := fun ⟨u, _⟩ ⟨hu, _⟩ ↦
    ⟨⟨by linarith [hu.1, hr.1], by linarith [hu.2, hr.2]⟩, mem_univ _⟩
  have hi := hasDerivAt_integral_mul_of_continuousOn_compact
    (μ := volume.restrict (Icc (0 : ℝ) (2 * π))) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) isCompact_Icc hS
    (integrable_const (1 : ℝ)) (hF.mono hsub) (hFr.mono hsub) fun θ _ u hu ↦
      hd u ⟨by linarith [hu.1, hr.1], by linarith [hu.2, hr.2]⟩ θ
  unfold angularMean
  simpa only [mul_one, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le two_pi_pos.le] using hi.2.const_mul ((2 * π)⁻¹)

theorem angularMean_smoothCap_bounds {F : ℝ → ℝ → ℝ} {r ε c : ℝ}
    (hε : 0 < ε) (hF : Continuous (F r)) :
    angularMean (fun r θ ↦ min (F r θ) c) r ≤
        angularMean (fun r θ ↦ smoothCap ε c (F r θ)) r ∧
      angularMean (fun r θ ↦ smoothCap ε c (F r θ)) r ≤
        angularMean (fun r θ ↦ min (F r θ) c) r + ε / 2 := by
  have hmeq (x : ℝ) : min x c = (x + c - |x - c|) / 2 := by
    rcases le_total x c with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hmin : Continuous (fun θ ↦ min (F r θ) c) := hF.inf continuous_const
  have hcap : Continuous (fun θ ↦ smoothCap ε c (F r θ)) := by unfold smoothCap; fun_prop
  have hlow := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
    (hmin.intervalIntegrable _ _) (hcap.intervalIntegrable _ _) fun θ _ ↦ by
      have hsq : sqrt ((F r θ - c) ^ 2 + ε ^ 2) ≤ |F r θ - c| + ε :=
        sqrt_le_iff.mpr ⟨by positivity,
          by nlinarith [sq_abs (F r θ - c), mul_nonneg (abs_nonneg (F r θ - c)) hε.le]⟩
      dsimp [smoothCap]; linarith [hmeq (F r θ)]
  have hupp := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
    (hcap.intervalIntegrable _ _) ((hmin.add (continuous_const (y := ε / 2))).intervalIntegrable _ _)
    fun θ _ ↦ by
      have hsq : |F r θ - c| ≤ sqrt ((F r θ - c) ^ 2 + ε ^ 2) := by
        rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
      dsimp [smoothCap]; linarith [hmeq (F r θ)]
  dsimp only [Pi.add_def] at hupp
  rw [intervalIntegral.integral_add (hmin.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hupp
  dsimp only [angularMean]
  refine ⟨mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr two_pi_pos.le), ?_⟩
  have h := mul_le_mul_of_nonneg_left hupp (inv_nonneg.mpr two_pi_pos.le)
  rwa [mul_add, ← mul_assoc, inv_mul_cancel₀ two_pi_pos.ne', one_mul] at h

def weightedPotential (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ∫ w, ‖weightedKernel α z w‖ * ‖f w‖ ∂weightedArea α

def weightedNormalizedPotential (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  weightedPotential α f z / normalizer α ‖z‖

def weightedDiskPotential (α : ℝ) (f : ℂ → ℂ) : ℂ → ℝ :=
  disk.indicator (weightedNormalizedPotential α f)

theorem weightedDiskPotential_nonneg (α : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    0 ≤ weightedDiskPotential α f z :=
  indicator_nonneg (fun w _ ↦ div_nonneg
    (integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (normalizer_nonneg α ‖w‖)) z

theorem weightedDiskPotential_eq {α : ℝ} {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ disk) :
    weightedDiskPotential α f z = weightedNormalizedPotential α f z :=
  indicator_of_mem hz _

theorem weightedPotential_eq_toReal {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    weightedPotential α f z = (weightedPositiveProjection α f z).toReal := by
  rw [weightedPotential, weightedPositiveProjection]
  simp only [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [norm_mul] using (integrable_weightedKernel_mul hα hf hz).norm.aestronglyMeasurable

theorem ae_mem_weighted_closedDisk (α : ℝ) :
    ∀ᵐ w ∂weightedArea α, w ∈ Metric.closedBall 0 1 :=
  (ae_mem_disk_weightedArea α).mono fun _ hw ↦ Metric.ball_subset_closedBall hw

theorem measurable_weightedDiskPotential {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) : Measurable (weightedDiskPotential α f) := by
  classical
  refine (ContinuousOn.div (fun z hz ↦ ?_)
    ((continuousOn_normalizer α).comp continuous_norm.continuousOn
      fun z hz ↦ ⟨norm_nonneg z, (mem_disk_iff z).mp hz⟩)
    fun z hz ↦ (normalizer_pos hα (by simpa using (mem_disk_iff z).mp hz)).ne').measurable_piecewise
    continuousOn_const measurableSet_disk
  have hz' := (mem_disk_iff z).mp hz
  let R := (‖z‖ + 1) / 2
  have hR : R < 1 := by dsimp [R]; linarith
  have hc : ContinuousOn (weightedPotential α f) (Metric.closedBall 0 R) := by
    refine continuousOn_integral_mul_of_compact (isCompact_closedBall 0 1)
      (ae_mem_weighted_closedDisk α) (isCompact_closedBall 0 R) hf.norm ?_
    simp_rw [norm_weightedKernel]
    refine (by fun_prop : ContinuousOn (fun p : ℂ × ℂ ↦ ‖1 - p.1 * star p.2‖) _).rpow_const
      fun p hp ↦ Or.inl ?_
    have h1 : ‖p.1‖ < 1 := (by simpa using hp.1 : ‖p.1‖ ≤ R).trans_lt hR
    have h2 : ‖p.2‖ ≤ 1 := by simpa using hp.2
    have h3 := norm_sub_norm_le (1 : ℂ) (p.1 * star p.2)
    rw [norm_one, norm_mul, norm_star] at h3
    linarith [mul_le_of_le_one_right (norm_nonneg p.1) h2]
  exact (hc.continuousAt (Metric.closedBall_mem_nhds_of_mem
    (by simp only [Metric.mem_ball, dist_zero_right, R]; linarith))).continuousWithinAt

/-- Normalizing by the exact circular kernel average makes every capped circular mean
of an admissible weighted potential decrease with radius. -/
theorem antitoneOn_circleAverage_min_weightedDiskPotential {α : ℝ} (hα : -1 < α)
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) (c : ℝ) :
    AntitoneOn (fun r ↦ circleAverage (fun z ↦ min (weightedDiskPotential α f z) c) 0 r)
      (Ico 0 1) := by
  have hK := isCompact_closedBall (0 : ℂ) 1
  have hμ := ae_mem_weighted_closedDisk α
  have hfn := hf.norm
  have ha := Complex.continuous_re
  have hb := Complex.continuous_im
  have hsource : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, w.re ^ 2 + w.im ^ 2 ≤ 1 := fun w hw ↦ by
    have hnorm : ‖w‖ ≤ 1 := by simpa using hw
    have heq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg w]
  have hr2 (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
  let k := α + 2
  let q := -k / 2
  let P (H : ℝ → ℝ → ℝ → ℝ → ℝ) :=
    polarIntegral H Complex.re Complex.im (weightedArea α) (fun w ↦ ‖f w‖)
  let F := P (polarKernel q)
  let Fr := P (polarKernelR q)
  let Frr := P (polarKernelRR q)
  let Ft := P (polarKernelT q)
  let Ftt := P (polarKernelTT q)
  let J := normalizer α
  let Jr := normalizerFirst α
  let Jrr := normalizerSecond α
  let cU (H : ℝ → ℝ → ℝ) := ContinuousOn (fun p : ℝ × ℝ ↦ H p.1 p.2) (Ico 0 1 ×ˢ univ)
  have hP {H : ℝ → ℝ → ℝ → ℝ → ℝ}
      (hH : polarKernelCont (Metric.closedBall 0 1) Complex.re Complex.im H) : cU (P H) :=
    continuousOn_polarIntegral_unit hK hμ hfn hH
  have hF := hP (continuousOn_polarKernel_source ha hb hsource q)
  have hFr := hP (continuousOn_polarKernelR_source ha hb hsource q)
  have hFrr := hP (continuousOn_polarKernelRR_source ha hb hsource q)
  have hFt := hP (continuousOn_polarKernelT_source ha hb hsource q)
  have hFtt := hP (continuousOn_polarKernelTT_source ha hb hsource q)
  have hFd r (hr : r ∈ Ioo (0 : ℝ) 1) :=
    polarIntegral_kernel_hasDerivAt_r hK hμ hfn ha hb hsource q (hr2 r hr)
  have hFrd r (hr : r ∈ Ioo (0 : ℝ) 1) :=
    polarIntegral_kernelR_hasDerivAt_r hK hμ hfn ha hb hsource q (hr2 r hr)
  have hFdt r (hr : r ∈ Ioo (0 : ℝ) 1) :=
    polarIntegral_kernel_hasDerivAt_t hK hμ hfn ha hb hsource q (hr2 r hr)
  have hFtd r (hr : r ∈ Ioo (0 : ℝ) 1) :=
    polarIntegral_kernelT_hasDerivAt_t hK hμ hfn ha hb hsource q (hr2 r hr)
  have hJ := continuousOn_normalizer α
  have hJd r (hr : r ∈ Ioo (0 : ℝ) 1) := normalizer_hasDerivAt α (hr2 r hr)
  have hJrd r (hr : r ∈ Ioo (0 : ℝ) 1) := normalizerFirst_hasDerivAt α (hr2 r hr)
  have hJpos (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) : 0 < J r :=
    normalizer_pos hα (by simpa only [abs_of_nonneg hr.1] using hr.2)
  have hfst {g : ℝ → ℝ} (hg : ContinuousOn g (Ico 0 1)) :
      ContinuousOn (fun p : ℝ × ℝ ↦ g p.1) (Ico 0 1 ×ˢ univ) :=
    hg.comp continuous_fst.continuousOn fun _ hp ↦ hp.1
  have hJ' := hfst hJ
  have hJr' := hfst (continuousOn_normalizerFirst α)
  have hJrr' := hfst (continuousOn_normalizerSecond α)
  have hn : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ (univ : Set ℝ), J p.1 ≠ 0 := fun p hp ↦ (hJpos p.1 hp.1).ne'
  have hpow (n : ℕ) : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ (univ : Set ℝ), J p.1 ^ n ≠ 0 :=
    fun p hp ↦ pow_ne_zero n (hn p hp)
  have hbase : ContinuousOn (fun r : ℝ ↦ (1 - r ^ 2) ^ k) (Ico 0 1) :=
    (by fun_prop : ContinuousOn (fun r : ℝ ↦ 1 - r ^ 2) _).rpow_const fun r hr ↦
      Or.inl (by nlinarith [hr.1, hr.2])
  let Q := fun r θ ↦ F r θ / J r
  let Qr := fun r θ ↦ (Fr r θ * J r - F r θ * Jr r) / J r ^ 2
  let Qrr := fun r θ ↦ Frr r θ / J r - F r θ * Jrr r / J r ^ 2 -
    2 * Fr r θ * Jr r / J r ^ 2 + 2 * F r θ * Jr r ^ 2 / J r ^ 3
  let Qt := fun r θ ↦ Ft r θ / J r
  let Qtt := fun r θ ↦ Ftt r θ / J r
  let w := fun r ↦ (1 - r ^ 2) ^ k * J r ^ 2
  let w' := fun r ↦ w r * (-(2 * k * r / (1 - r ^ 2)) + 2 * Jr r / J r)
  have hQ : cU Q := hF.div hJ' hn
  have hQr : cU Qr := ((hFr.mul hJ').sub (hF.mul hJr')).div (hJ'.pow 2) (hpow 2)
  have hQrr : cU Qrr := (((hFrr.div hJ' hn).sub ((hF.mul hJrr').div (hJ'.pow 2) (hpow 2))).sub
    (((hFr.const_mul 2).mul hJr').div (hJ'.pow 2) (hpow 2))).add
    (((hF.const_mul 2).mul (hJr'.pow 2)).div (hJ'.pow 3) (hpow 3))
  have hQt : cU Qt := hFt.div hJ' hn
  have hQtt : cU Qtt := hFtt.div hJ' hn
  have hQd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) : HasDerivAt (fun u ↦ Q u θ) (Qr r θ) r :=
    (hFd r hr θ).div (hJd r hr) (hJpos r ⟨hr.1.le, hr.2⟩).ne'
  have hQrd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) : HasDerivAt (fun u ↦ Qr u θ) (Qrr r θ) r := by
    have hJ0 := (hJpos r ⟨hr.1.le, hr.2⟩).ne'
    convert (((hFrd r hr θ).mul (hJd r hr)).sub ((hFd r hr θ).mul (hJrd r hr))).div
      ((hJd r hr).pow 2) (pow_ne_zero 2 hJ0) using 1
    dsimp only [Qrr, F, Fr, Frr, P, J, Jr, Jrr, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply] at hJ0 ⊢
    field_simp [hJ0]; ring
  have hw : ContinuousOn w (Ico 0 1) := hbase.mul (hJ.pow 2)
  have hwd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : HasDerivAt w (w' r) r := by
    have ht : 0 < 1 - r ^ 2 := sub_pos.mpr (hr2 r hr)
    have hJ0 := (hJpos r ⟨hr.1.le, hr.2⟩).ne'
    convert ((((hasDerivAt_id r).pow 2).const_sub 1).rpow_const (p := k) (Or.inl ht.ne')).mul
      ((hJd r hr).pow 2) using 1
    · rfl
    · dsimp only [w', w, Pi.pow_apply, id_eq]
      rw [Real.rpow_sub_one ht.ne']; field_simp [hJ0, ht.ne']; ring
  have hwpos (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < w r :=
    mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr (hr2 r hr)) _)
      (sq_pos_of_pos (hJpos r ⟨hr.1.le, hr.2⟩))
  have hineq (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
      r * w r * Qrr r θ + (w r + r * w' r) * Qr r θ + (w r / r) * Qtt r θ ≤ 0 := by
    have hj := hJpos r ⟨hr.1.le, hr.2⟩
    have ht : 0 < 1 - r ^ 2 := sub_pos.mpr (hr2 r hr)
    have hJode := normalizer_ode α (hr2 r hr) hr.1.ne'
    have hFode := polarIntegral_operator_nonpos hK hμ hfn ha hb hsource k
      (hr2 r hr) hr.1.ne' θ (Filter.Eventually.of_forall fun w ↦ norm_nonneg (f w))
    have heq : J r * (Qrr r θ +
        (1 / r - 2 * k * r / (1 - r ^ 2) + 2 * Jr r / J r) *
          Qr r θ + Qtt r θ / r ^ 2) =
      polarOperator Complex.re Complex.im (weightedArea α) (fun w ↦ ‖f w‖) k r θ - (F r θ / J r) *
        (Jrr r + Jr r / r - (2 * k * r / (1 - r ^ 2)) * Jr r -
          (k ^ 2 / (1 - r ^ 2)) * J r) := by
      dsimp only [Qr, Qrr, Qtt, polarOperator, F, Fr, Frr, Ft, Ftt, P, q]
      field_simp [hj.ne', hr.1.ne', ht.ne']; ring
    change Jrr r + Jr r / r - (2 * k * r / (1 - r ^ 2)) * Jr r -
      (k ^ 2 / (1 - r ^ 2)) * J r = 0 at hJode
    rw [hJode, mul_zero, sub_zero] at heq
    have h := nonpos_of_mul_nonpos_right (heq.trans_le hFode) hj
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hr.1.le (mul_nonneg (Real.rpow_nonneg ht.le k) (sq_nonneg (J r)))) h
    convert hm using 1
    dsimp only [w', w]; field_simp [hj.ne', hr.1.ne', ht.ne']; ring
  have hslice {H : ℝ → ℝ → ℝ} (hH : cU H) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) : Continuous (H r) :=
    continuousOn_univ.mp <| hH.comp (continuous_const.prodMk continuous_id).continuousOn
      fun θ _ ↦ ⟨hr, mem_univ θ⟩
  have heq (u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
      circleAverage (fun z ↦ min (weightedDiskPotential α f z) c) 0 u =
      angularMean (fun r θ ↦ min (Q r θ) c) u := by
    rw [Real.circleAverage_def, angularMean]
    simp only [weightedDiskPotential, indicator_of_mem,
      fun θ : ℝ ↦ (mem_disk_iff (circleMap 0 u θ)).mpr (by simp [abs_of_nonneg hu.1, hu.2]),
      weightedNormalizedPotential, norm_circleMap_zero, abs_of_nonneg hu.1,
      weightedPotential, polarIntegral, polarKernel_eq_norm_weightedKernel,
      smul_eq_mul, Q, F, P, J, q, k]
  intro r₀ hr₀ R₀ hR₀ hrR₀
  dsimp only
  rw [heq r₀ hr₀, heq R₀ hR₀]
  apply le_of_forall_pos_le_add
  intro ε hε
  let d₁ := smoothCapInputDeriv ε c
  let d₂ := fun u ↦ -(ε ^ 2) / (2 * sqrt ((u - c) ^ 2 + ε ^ 2) ^ 3)
  have hd₁ : Continuous d₁ := continuous_iff_continuousAt.mpr
    fun _ ↦ (hasDerivAt_smoothCapInputDeriv hε).continuousAt
  have hd₂ : Continuous d₂ := Continuous.div continuous_const (by fun_prop) fun _ ↦
    (mul_pos (by norm_num) (pow_pos (sqrt_pos.mpr (by positivity)) _)).ne'
  have hcap : Continuous (smoothCap ε c) := continuous_iff_continuousAt.mpr
    fun _ ↦ (hasDerivAt_smoothCap_input hε).continuousAt
  let G := fun r θ ↦ smoothCap ε c (Q r θ)
  let Gr := fun r θ ↦ d₁ (Q r θ) * Qr r θ
  let Grr := fun r θ ↦ d₂ (Q r θ) * (Qr r θ) ^ 2 + d₁ (Q r θ) * Qrr r θ
  let Gtt := fun r θ ↦ d₂ (Q r θ) * (Qt r θ) ^ 2 + d₁ (Q r θ) * Qtt r θ
  have hG : cU G := hcap.comp_continuousOn hQ
  have hGr : cU Gr := (hd₁.comp_continuousOn hQ).mul hQr
  have hGrr : cU Grr := ((hd₂.comp_continuousOn hQ).mul (hQr.pow 2)).add ((hd₁.comp_continuousOn hQ).mul hQrr)
  have hGtt : cU Gtt := ((hd₂.comp_continuousOn hQ).mul (hQt.pow 2)).add ((hd₁.comp_continuousOn hQ).mul hQtt)
  have hcomp {x : ℝ} {U U' : ℝ → ℝ} {U'' : ℝ}
      (hU : HasDerivAt U (U' x) x) (hU' : HasDerivAt U' U'' x) :
      HasDerivAt (fun y ↦ d₁ (U y) * U' y) (d₂ (U x) * (U' x) ^ 2 + d₁ (U x) * U'') x := by
    convert ((hasDerivAt_smoothCapInputDeriv (c := c) hε).comp x hU).mul hU' using 1 <;>
      simp only [Function.comp_def, Pi.mul_def, d₁, d₂]
    ring
  have hm : AntitoneOn (angularMean G) (Ico 0 1) := by
    apply antitoneOn_of_radial_flux (w := w)
      (F := fun r ↦ r * w r * angularMean Gr r)
      (F' := fun r ↦ (w r + r * w' r) * angularMean Gr r + r * w r * angularMean Grr r)
      (continuousOn_angularMean hG)
      (fun r hr ↦ hasDerivAt_angularMean hr hG hGr fun r hr θ ↦
        (hasDerivAt_smoothCap_input hε).comp r (hQd r hr θ))
      hwpos ((continuousOn_id.mul hw).mul (continuousOn_angularMean hGr)) (by simp)
    · intro r hr
      convert ((hasDerivAt_id r).mul (hwd r hr)).mul
        (hasDerivAt_angularMean hr hGr hGrr fun r hr θ ↦ hcomp (hQd r hr θ) (hQrd r hr θ)) using 1 <;>
        simp only [one_mul, Pi.mul_def, id_eq]
    · intro r hr
      have hr' : r ∈ Ico (0 : ℝ) 1 := ⟨hr.1.le, hr.2⟩
      have hir := (hslice hGr hr').intervalIntegrable (μ := volume) 0 (2 * π)
      have hirr := (hslice hGrr hr').intervalIntegrable (μ := volume) 0 (2 * π)
      have hitt := (hslice hGtt hr').intervalIntegrable (μ := volume) 0 (2 * π)
      have hz : (∫ θ in (0 : ℝ)..2 * π, Gtt r θ) = 0 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun θ _ ↦ hcomp ((hFdt r hr θ).div_const (J r)) ((hFtd r hr θ).div_const (J r))) hitt]
        simp [polarIntegral, polarKernel, polarKernelT, polarDenominator,
          radialComponent, angularComponent]
      have hpt (θ : ℝ) (_ : θ ∈ Icc 0 (2 * π)) :
          (r * w r * Grr r θ + (w r + r * w' r) * Gr r θ) + (w r / r) * Gtt r θ ≤ 0 := by
        have hd₁_nn : 0 ≤ d₁ (Q r θ) := smoothCapInputDeriv_nonneg hε
        have hd₂_np : d₂ (Q r θ) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg ε)) (by positivity)
        have h1 := mul_nonpos_of_nonneg_of_nonpos hd₁_nn (hineq r hr θ)
        have h2 := mul_nonpos_of_nonpos_of_nonneg hd₂_np
          (show 0 ≤ r * w r * (Qr r θ) ^ 2 + (w r / r) * (Qt r θ) ^ 2 by
            have := hwpos r hr; have := hr.1; positivity)
        dsimp [Gr, Grr, Gtt]; linarith
      have hi := intervalIntegral.integral_mono_on two_pi_pos.le
        (((hirr.const_mul (r * w r)).add (hir.const_mul (w r + r * w' r))).add
          (hitt.const_mul (w r / r))) (intervalIntegrable_const (c := (0 : ℝ))) hpt
      rw [intervalIntegral.integral_add ((hirr.const_mul _).add (hir.const_mul _))
        (hitt.const_mul _), intervalIntegral.integral_const_mul, hz, mul_zero, add_zero,
        intervalIntegral.integral_zero,
        intervalIntegral.integral_add (hirr.const_mul _) (hir.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
      have hm' := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr two_pi_pos.le) hi
      dsimp only [angularMean]; nlinarith
    · exact fun _ _ ↦ rfl
  linarith [(angularMean_smoothCap_bounds (c := c) hε (hslice hQ hR₀)).1,
    (angularMean_smoothCap_bounds (c := c) hε (hslice hQ hr₀)).2, hm hr₀ hR₀ hrR₀]

theorem circleAverage_min_weightedDiskPotential_le_mass {α : ℝ} (hα : -1 < α)
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) (c : ℝ) :
    circleAverage (fun z ↦ min (weightedDiskPotential α f z) c) 0 r ≤
      ∫ w, ‖f w‖ ∂weightedArea α := by
  have h := antitoneOn_circleAverage_min_weightedDiskPotential hα hf c
    (show (0 : ℝ) ∈ Ico 0 1 by simp) hr hr.1
  have h0 : weightedDiskPotential α f 0 = ∫ w, ‖f w‖ ∂weightedArea α := by
    simp [weightedDiskPotential_eq ((mem_disk_iff 0).mpr (by simp)),
      weightedNormalizedPotential, weightedPotential, weightedKernel]
  simp only [circleAverage_zero, h0] at h
  exact h.trans (min_le_left _ _)

end Weighted

end BergmanWeakType
