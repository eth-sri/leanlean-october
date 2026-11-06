/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CirclePotential
public import DOZZ.GFF.LocalSchur
public import DOZZ.GFF.AnnularEnergyConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Annular cancellation for arbitrary circles

Transport the unit-annulus mixed-energy estimate `DOZZ.abs_annularMixedEnergy_le` by a
translation and dilation.
The regular pinning potentials cancel because the annular densities have mass one.
-/

@[expose] public section

open Filter MeasureTheory Set Metric
open scoped Topology

namespace DOZZ.Proofs

/-- The pinned bilinear energy also makes sense for continuous compactly supported densities. -/
noncomputable def densityEnergy (f g : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, f p.1 * gffKernel p.1 p.2 * g p.2

/-- Continuous compactly supported densities have an integrable pinned pairing. -/
theorem integrable_densityEnergy {f g}
    (hf : Continuous f) (hg : Continuous g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    Integrable (fun p : ℂ × ℂ => f p.1 * gffKernel p.1 p.2 * g p.2)
      (volume : Measure (ℂ × ℂ)) := by
  have hfint : Integrable f (volume : Measure ℂ) := hf.integrable_of_hasCompactSupport hsf
  have hgint : Integrable g (volume : Measure ℂ) := hg.integrable_of_hasCompactSupport hsg
  have hfp : Integrable (fun z => f z * Real.log (normPlus z)) :=
    (hf.mul continuous_log_normPlus).integrable_of_hasCompactSupport hsf.mul_right
  have hgp : Integrable (fun z => g z * Real.log (normPlus z)) :=
    (hg.mul continuous_log_normPlus).integrable_of_hasCompactSupport hsg.mul_right
  convert (((DOZZ.integral_complexLogKernelPair_eq_vec f g hf hg hsf hsg).1).add (hfp.mul_prod hgint)).add (hfint.mul_prod hgp) using 1
  ext p
  simp only [gffKernel, Pi.add_apply]
  ring

/-- On smooth tests the extended bilinear energy is exactly the covariance `DOZZ.gffCov`. -/
theorem densityEnergy_testFn (f g : TestFn) : densityEnergy f g = gffCov f g :=
  (DOZZ.gffCov_eq_integral_gffKernel f g).symm

/-- Weighted dominated convergence, with a bound on the density rather than on the kernel. -/
theorem tendsto_integral_weighted {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : ℕ → α → ℝ) (v b k : α → ℝ) M
    (hu : ∀ n, Measurable (u n)) (hk : Measurable k)
    (hbn : ∀ a, 0 ≤ b a) (hb : Integrable (fun a => b a * k a) μ)
    (hbound : ∀ n a, |u n a| ≤ M * b a)
    (hlim : ∀ a, Tendsto (fun n => u n a) atTop (𝓝 (v a))) :
    Tendsto (fun n => ∫ a, u n a * k a ∂μ) atTop (𝓝 (∫ a, v a * k a ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun a => M * |b a * k a|) (fun n => ((hu n).mul hk).aestronglyMeasurable)
    (hb.norm.const_mul M) (fun n => ?_) ?_
  · filter_upwards with a
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      |u n a| * |k a| ≤ (M * b a) * |k a| :=
        mul_le_mul_of_nonneg_right (hbound n a) (abs_nonneg _)
      _ = M * (|b a| * |k a|) := by rw [abs_of_nonneg (hbn a), mul_assoc]
  · filter_upwards with a
    exact (hlim a).mul_const (k a)

/-- A common compact cutoff bounds every function supported in its inner ball. -/
theorem abs_le_bump_of_support {R M} (hR : 0 < R) (hM : 0 ≤ M)
    f (hs : Function.support f ⊆ closedBall (0 : ℂ) R)
    (hf : ∀ z, |f z| ≤ M) z :
    |f z| ≤ M * (⟨R, R + 1, hR, lt_add_one R⟩ : ContDiffBump (0 : ℂ)) z := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  by_cases hz : z ∈ Function.support f
  · rw [b.one_of_mem_closedBall (hs hz), mul_one]
    exact hf z
  · have hz' : f z = 0 := by simpa only [Function.mem_support, not_not] using hz
    rw [hz', abs_zero]
    exact mul_nonneg hM b.nonneg

/-- Pointwise convergence of uniformly bounded densities on a common compact support
implies convergence of their full pinned energies, including the diagonal singularity. -/
theorem tendsto_densityEnergy_of_common_support
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ) {R M} (hR : 0 < R) (hM : 0 ≤ M)
    (hf : ∀ n, Measurable (f n))
    (hs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ n z, |f n z| ≤ M)
    (hl : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n => densityEnergy (f n) (f n)) atTop (𝓝 (densityEnergy g g)) := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  have ht := tendsto_integral_weighted volume
    (fun (n : ℕ) (p : ℂ × ℂ) => f n p.1 * f n p.2)
    (fun p : ℂ × ℂ => g p.1 * g p.2)
    (fun p : ℂ × ℂ => b p.1 * b p.2)
    (fun p : ℂ × ℂ => gffKernel p.1 p.2) (M * M)
    (fun n => ((hf n).comp measurable_fst).mul ((hf n).comp measurable_snd))
    (by fun_prop [gffKernel, normPlus])
    (fun p => mul_nonneg b.nonneg b.nonneg) (by convert (integrable_densityEnergy b.continuous b.continuous b.hasCompactSupport b.hasCompactSupport) using 1; ext p; ring)
    (by
      intro n p
      rw [abs_mul]
      calc
        |f n p.1| * |f n p.2| ≤ (M * b p.1) * (M * b p.2) :=
          mul_le_mul (abs_le_bump_of_support hR hM (f n) (hs n) (hb n) p.1)
            (abs_le_bump_of_support hR hM (f n) (hs n) (hb n) p.2)
            (abs_nonneg _) (mul_nonneg hM b.nonneg)
        _ = (M * M) * (b p.1 * b p.2) := by ring)
    (fun p => (hl p.1).mul (hl p.2))
  convert ht using 1 <;> simp only [densityEnergy, mul_comm, mul_left_comm]

/-- The potential of a nondegenerate circle is continuous, including at points of the circle. -/
theorem continuous_circleKernelPotential x r :
    Continuous (fun z => ∫ w, gffKernel z w ∂circleMeasure x r) := by
  simp_rw [integral_gffKernel_circleMeasure]
  exact (((continuous_const.max (continuous_const.sub continuous_id).norm).log (fun z => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))).neg.add continuous_log_normPlus).add continuous_const

/-- The energy gap extended to continuous compactly supported planar densities. -/
noncomputable def densityCircleGap (x : ℂ) (r : ℝ) (f : ℂ → ℝ) : ℝ :=
  densityEnergy f f - 2 * (∫ z, f z * ∫ w, gffKernel z w ∂circleMeasure x r) +
    circleSelfEnergy x r

/-- The extension agrees with the energy gap `DOZZ.circleEnergyGap` on tests. -/
theorem densityCircleGap_testFn (x : ℂ) (r : ℝ) (f : TestFn) :
    densityCircleGap x r f = circleEnergyGap x r f := by
  rw [densityCircleGap, densityEnergy_testFn]
  rfl

/-- Common-support convergence also controls the mixed circle energy, whose integrated
potential is continuous even though the original logarithmic kernel is singular. -/
theorem tendsto_densityCircleGap_of_common_support
    x r (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ)
    {R M} (hR : 0 < R) (hM : 0 ≤ M)
    (hf : ∀ n, Measurable (f n))
    (hs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ n z, |f n z| ≤ M)
    (hl : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n => densityCircleGap x r (f n)) atTop (𝓝 (densityCircleGap x r g)) := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  have hp := continuous_circleKernelPotential x r
  exact ((tendsto_densityEnergy_of_common_support f g hR hM hf hs hb hl).sub
    ((tendsto_integral_weighted volume f g b (fun z => ∫ w, gffKernel z w ∂circleMeasure x r) M hf hp.measurable (fun _ => b.nonneg) ((b.continuous.mul hp).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right) (fun n z => abs_le_bump_of_support hR hM (f n) (hs n) (hb n) z) hl).const_mul 2)).add_const (circleSelfEnergy x r)

/-- Every continuous compactly supported density can be approximated by smooth tests in
circle energy. The support is enlarged once and then remains fixed throughout the limit. -/
theorem exists_testFn_tendsto_densityCircleGap (x : ℂ) (r : ℝ)
    (g : ℂ → ℝ) (hg : Continuous g) {R : ℝ} (hR : 0 < R)
    (hs : tsupport g ⊆ closedBall (0 : ℂ) R) :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n) ⊆ closedBall (0 : ℂ) (R + 1)) ∧
      (∀ n z, |f n z - g z| < 1 / ((n : ℝ) + 2)) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 (densityCircleGap x r g)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  choose f hf using (fun n => exists_testFn_uniform_approx hg hR hs ((fun n => by dsimp [ε]; positivity : ∀ n, 0 < ε n) n))
  have hcompact : HasCompactSupport g :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hs
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuous hg
  have := (norm_nonneg (g 0)).trans (hM 0)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [ε, Nat.cast_add]
  have hbound n z : |f n z| ≤ M + 1 := by
    have := (hf n).2 z
    have : ε n ≤ 1 := by
      dsimp [ε]
      apply (div_le_one (by positivity)).mpr
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    have : |g z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z
    have : |f n z| ≤ |f n z - g z| + |g z| := by
      simpa only [sub_add_cancel] using (abs_add_le (f n z - g z) (g z))
    linarith
  have hl z : Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hεlim)
      (by simpa using tendsto_const_nhds.add hεlim)
    · intro n
      have := (abs_lt.mp ((hf n).2 z)).1
      linarith
    · intro n
      have := (abs_lt.mp ((hf n).2 z)).2
      linarith
  refine ⟨f, fun n => (hf n).1, fun n z => (hf n).2 z, ?_⟩
  simp_rw [← densityCircleGap_testFn]
  exact tendsto_densityCircleGap_of_common_support x r (fun n => f n) g (R := R + 1) (M := M + 1)
    (by linarith) (by linarith) (fun n => (f n).continuous.measurable)
    (fun n => (subset_tsupport _).trans (hf n).1) hbound hl


/-- Raw logarithmic energy, before the equator pinning potentials are added. -/
noncomputable def rawDensityEnergy (f g : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)

/-- The extended pinned pairing expands bilinearly into the raw logarithmic energy and the two
pinning terms. -/
theorem densityEnergy_eq_raw {f g}
    (hf : Continuous f) (hg : Continuous g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    densityEnergy f g = rawDensityEnergy f g +
      (∫ z, f z * Real.log (normPlus z)) * (∫ z, g z) +
      (∫ z, f z) * (∫ z, g z * Real.log (normPlus z)) := by
  have hr := (DOZZ.integral_complexLogKernelPair_eq_vec f g hf hg hsf hsg).1
  have hgi : Integrable g (volume : Measure ℂ) := hg.integrable_of_hasCompactSupport hsg
  have hfp : Integrable (fun z => f z * Real.log (normPlus z)) :=
    (hf.mul continuous_log_normPlus).integrable_of_hasCompactSupport hsf.mul_right
  have hgp : Integrable (fun z => g z * Real.log (normPlus z)) :=
    (hg.mul continuous_log_normPlus).integrable_of_hasCompactSupport hsg.mul_right
  have heq (p : ℂ × ℂ) : f p.1 * gffKernel p.1 p.2 * g p.2 =
      (f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖) +
        (f p.1 * Real.log (normPlus p.1)) * g p.2) +
          f p.1 * (g p.2 * Real.log (normPlus p.2)) := by
    simp only [gffKernel]
    ring
  unfold densityEnergy rawDensityEnergy
  simp_rw [heq]
  rw [Measure.volume_eq_prod]
  have hsum := integral_add (hr.add (hfp.mul_prod hgi)) ((hf.integrable_of_hasCompactSupport hsf).mul_prod hgp)
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add hr (hfp.mul_prod hgi),
    integral_prod_mul (fun z => f z * Real.log (normPlus z)) g,
    integral_prod_mul f (fun z => g z * Real.log (normPlus z))]

/-- Integration of a transported annular density is integration against the original annulus. -/
theorem integral_circleAnnularDensity_mul x r n (h : ℂ → ℝ) :
    (∫ z, circleAnnularDensity x r n z * h z) =
      ∫ u, DOZZ.annularProbabilityDensity n u * h (Real.exp (-r) • u + x) := by
  let R := Real.exp (-r)
  let H : ℂ → ℝ := fun u => DOZZ.annularProbabilityDensity n u * h (R • u + x)
  have hR : R ≠ 0 := Real.exp_ne_zero _
  have heq z : circleAnnularDensity x r n z * h z =
      R⁻¹ ^ 2 * H (R⁻¹ • (z - x)) := by
    simp only [circleAnnularDensity, H, R, smul_smul, mul_inv_cancel₀ hR, one_smul,
      sub_add_cancel]
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun z => H (R⁻¹ • z)) x,
    Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure ℂ)) H
      (Real.exp_pos (-r)).le, Complex.finrank_real_complex, smul_eq_mul]
  change R⁻¹ ^ 2 * (R ^ 2 * ∫ u, H u) = ∫ u, H u
  field_simp



/-- The self-energy of any circle is its raw self-energy plus twice its pinning potential. -/
theorem circleSelfEnergy_eq x r :
    circleSelfEnergy x r = r + 2 * (∫ z, Real.log (normPlus z) ∂circleMeasure x r) := by
  let _ := circleMeasure_isProbability x r
  unfold circleSelfEnergy
  simp_rw [integral_gffKernel_circleMeasure]
  rw [integral_congr_ae (show (fun z => -Real.log (max (Real.exp (-r)) ‖x - z‖) + Real.log (normPlus z) + (∫ w, Real.log (normPlus w) ∂circleMeasure x r)) =ᵐ[circleMeasure x r] fun z => r + Real.log (normPlus z) + (∫ w, Real.log (normPlus w) ∂circleMeasure x r) by filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz; rw [norm_sub_rev, hz, max_self, Real.log_exp, neg_neg])]
  have hpin := integrable_log_normPlus_circleMeasure x r
  have hfirst := integral_add (integrable_const r) hpin
  have hsecond := integral_add ((integrable_const r).add hpin)
    (integrable_const (∫ w, Real.log (normPlus w) ∂circleMeasure x r))
  simp only [Pi.add_apply] at hfirst hsecond
  rw [hsecond, hfirst, integral_const, integral_const, probReal_univ, one_smul, one_smul]
  ring




/-- The unit-annulus mixed-energy estimate gives an all-center, all-radius gap estimate; its
constant is independent of the center and radius because the mass-one potentials cancel. -/
theorem abs_densityCircleGap_circleAnnular_le x r (n : ℕ) :
    |densityCircleGap x r (circleAnnularDensity x r n)| ≤ 5 / ((n : ℝ) + 2) := by
  have abs_annular_pin_integral_le : |∫ u, DOZZ.annularProbabilityDensity n u * Real.log (normPlus u)| ≤ 1 / ((n : ℝ) + 2) := by
    let δ := 1 / ((n : ℝ) + 2)
    have hi : Integrable (fun u => DOZZ.annularProbabilityDensity n u *
        Real.log (normPlus u)) :=
      ((DOZZ.continuous_annularProbabilityDensity n).mul continuous_log_normPlus).integrable_of_hasCompactSupport (DOZZ.hasCompactSupport_annularProbabilityDensity n).mul_right
    calc
      _ ≤ ∫ u, |DOZZ.annularProbabilityDensity n u * Real.log (normPlus u)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ u, δ * DOZZ.annularProbabilityDensity n u := by
        apply integral_mono_ae hi.norm ((DOZZ.integrable_annularProbabilityDensity n).const_mul δ)
        filter_upwards with u
        by_cases hu : DOZZ.annularProbabilityDensity n u = 0
        · simp [hu]
        · have hb := DOZZ.abs_logPlus_of_annularDensity_ne_zero n u hu
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (DOZZ.annularProbabilityDensity_nonneg n u)]
          exact (mul_le_mul_of_nonneg_left hb (DOZZ.annularProbabilityDensity_nonneg n u)).trans_eq
            (mul_comm _ _)
      _ = δ := by rw [integral_const_mul, DOZZ.integral_annularProbabilityDensity, mul_one]
  have densityCircleGap_circleAnnular_eq x r n : densityCircleGap x r (circleAnnularDensity x r n) = DOZZ.annularMixedEnergy n n + 2 * (∫ u, DOZZ.annularProbabilityDensity n u * Real.log (normPlus u)) := by
    have integral_circleAnnular_logmax x r n : (∫ z, circleAnnularDensity x r n z * Real.log (max (Real.exp (-r)) ‖x - z‖)) = -r + ∫ u, DOZZ.annularProbabilityDensity n u * Real.log (normPlus u) := by
      rw [integral_circleAnnularDensity_mul]
      have heq u : Real.log (max (Real.exp (-r))
          ‖x - (Real.exp (-r) • u + x)‖) = -r + Real.log (normPlus u) := by
        rw [show x - (Real.exp (-r) • u + x) = -(Real.exp (-r) • u) by abel,
          norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [show max (Real.exp (-r)) (Real.exp (-r) * ‖u‖) =
          Real.exp (-r) * max 1 ‖u‖ by rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_one]]
        rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (lt_of_lt_of_le zero_lt_one
          (le_max_left _ _))), Real.log_exp]
        rfl
      simp_rw [heq, mul_add]
      rw [integral_add ((DOZZ.integrable_annularProbabilityDensity n).mul_const (-r)) (((DOZZ.continuous_annularProbabilityDensity n).mul continuous_log_normPlus).integrable_of_hasCompactSupport (DOZZ.hasCompactSupport_annularProbabilityDensity n).mul_right : Integrable (fun u => DOZZ.annularProbabilityDensity n u * Real.log (normPlus u))),
        integral_mul_const, DOZZ.integral_annularProbabilityDensity, one_mul]
    have rawDensityEnergy_circleAnnular x r n k : rawDensityEnergy (circleAnnularDensity x r n) (circleAnnularDensity x r k) = r + DOZZ.annularMixedEnergy n k := by
      have integral_circleAnnularDensity_pair x r n k (h : ℂ × ℂ → ℝ) : (∫ p : ℂ × ℂ, circleAnnularDensity x r n p.1 * circleAnnularDensity x r k p.2 * h p) = ∫ p : ℂ × ℂ, DOZZ.annularProbabilityDensity n p.1 * DOZZ.annularProbabilityDensity k p.2 * h (Real.exp (-r) • p + (x, x)) := by
        let _ : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure := by
          rw [Measure.volume_eq_prod]
          exact Measure.prod.instIsAddHaarMeasure _ _
        let _ : (volume : Measure (ℂ × ℂ)).IsAddRightInvariant := by
          rw [Measure.volume_eq_prod]
          infer_instance
        let R := Real.exp (-r)
        let H : ℂ × ℂ → ℝ := fun p => DOZZ.annularProbabilityDensity n p.1 *
          DOZZ.annularProbabilityDensity k p.2 * h (R • p + (x, x))
        have hR : R ≠ 0 := Real.exp_ne_zero _
        have heq (p : ℂ × ℂ) : circleAnnularDensity x r n p.1 *
            circleAnnularDensity x r k p.2 * h p = R⁻¹ ^ 4 * H (R⁻¹ • (p - (x, x))) := by
          simp only [circleAnnularDensity, H, R, smul_smul, mul_inv_cancel₀ hR, one_smul,
            sub_add_cancel, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub]
          ring
        simp_rw [heq]
        rw [integral_const_mul, integral_sub_right_eq_self
          (fun p => H (R⁻¹ • p)) (x, x),
          Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (ℂ × ℂ))) H
            (Real.exp_pos (-r)).le, Module.finrank_prod, Complex.finrank_real_complex,
            smul_eq_mul]
        change R⁻¹ ^ 4 * (R ^ 4 * ∫ p, H p) = ∫ p, H p
        field_simp
      unfold rawDensityEnergy
      rw [integral_circleAnnularDensity_pair]
      have hae : ∀ᵐ p : ℂ × ℂ ∂volume, p.1 ≠ p.2 := by
        rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae (by measurability)]
        filter_upwards with u
        filter_upwards [Measure.ae_ne (volume : Measure ℂ) u] with v hv
        exact hv.symm
      have heq : (fun p : ℂ × ℂ => DOZZ.annularProbabilityDensity n p.1 *
          DOZZ.annularProbabilityDensity k p.2 *
            (-Real.log ‖(Real.exp (-r) • p + (x, x)).1 -
              (Real.exp (-r) • p + (x, x)).2‖)) =ᵐ[volume]
          fun p => r * (DOZZ.annularProbabilityDensity n p.1 *
            DOZZ.annularProbabilityDensity k p.2) +
              DOZZ.annularProbabilityDensity n p.1 * DOZZ.annularProbabilityDensity k p.2 *
                (-Real.log ‖p.1 - p.2‖) := by
        filter_upwards [hae] with p hp
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), Real.log_mul (Real.exp_ne_zero _)
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)), Real.log_exp]
        ring
      rw [integral_congr_ae heq, Measure.volume_eq_prod, integral_add
        (((DOZZ.integrable_annularProbabilityDensity n).mul_prod
          (DOZZ.integrable_annularProbabilityDensity k)).const_mul r)
        (DOZZ.integrable_annularMixedEnergyIntegrand n k), integral_const_mul,
        integral_prod_mul, DOZZ.integral_annularProbabilityDensity,
        DOZZ.integral_annularProbabilityDensity]
      simp only [mul_one, DOZZ.annularMixedEnergy]
    let ρ := circleAnnularDensity x r n
    let J := ∫ w, Real.log (normPlus w) ∂circleMeasure x r
    have hc := continuous_circleAnnularDensity x r n
    have hs := hasCompactSupport_circleAnnularDensity x r n
    have hm := integral_circleAnnularDensity x r n
    have hlog : Integrable (fun z => ρ z * Real.log (max (Real.exp (-r)) ‖x - z‖)) :=
      (hc.mul ((continuous_const.max (continuous_const.sub continuous_id).norm).log (fun z => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _))))).integrable_of_hasCompactSupport hs.mul_right
    have hpin : Integrable (fun z => ρ z * Real.log (normPlus z)) :=
      (hc.mul continuous_log_normPlus).integrable_of_hasCompactSupport hs.mul_right
    have heq z : ρ z * (∫ w, gffKernel z w ∂circleMeasure x r) =
        (-ρ z * Real.log (max (Real.exp (-r)) ‖x - z‖) +
          ρ z * Real.log (normPlus z)) + ρ z * J := by
      rw [integral_gffKernel_circleMeasure]
      dsimp [J]
      ring
    have hcross : (∫ z, ρ z * ∫ w, gffKernel z w ∂circleMeasure x r) =
        r - (∫ u, DOZZ.annularProbabilityDensity n u * Real.log (normPlus u)) +
          (∫ z, ρ z * Real.log (normPlus z)) + J := by
      simp_rw [heq]
      have hadd := integral_add (hlog.neg.add hpin) ((integrable_circleAnnularDensity x r n).mul_const J)
      have hsub := integral_add hlog.neg hpin
      simp only [Pi.add_apply, Pi.neg_apply] at hadd hsub
      simp only [neg_mul] at ⊢
      rw [hadd, hsub, integral_neg, integral_circleAnnular_logmax,
        integral_mul_const, hm, one_mul]
      ring
    unfold densityCircleGap
    rw [densityEnergy_eq_raw hc hc hs hs, hm, mul_one, one_mul,
      rawDensityEnergy_circleAnnular, hcross, circleSelfEnergy_eq]
    dsimp [J, ρ]
    ring
  rw [densityCircleGap_circleAnnular_eq]
  have hraw := DOZZ.abs_annularMixedEnergy_le n n
  have hpin := abs_annular_pin_integral_le
  have htri := abs_add_le (DOZZ.annularMixedEnergy n n)
    (2 * ∫ u, DOZZ.annularProbabilityDensity n u * Real.log (normPlus u))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  simp only [div_eq_mul_inv] at hraw hpin ⊢
  linarith

/-- The continuous annular densities converge in the exact circle-energy gap. -/
theorem tendsto_densityCircleGap_circleAnnular x r :
    Tendsto (fun n => densityCircleGap x r (circleAnnularDensity x r n)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => 5 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hb.neg) hb
  · intro n
    exact (abs_le.mp (abs_densityCircleGap_circleAnnular_le x r n)).1
  · intro n
    exact (abs_le.mp (abs_densityCircleGap_circleAnnular_le x r n)).2

/-- Actual smooth tests approximate every circle in its logarithmic energy gap.
The construction first uses the annular estimate `abs_densityCircleGap_circleAnnular_le`, then
selects a sufficiently accurate smooth approximation for each annular width using common-support
continuity. -/
theorem exists_testFn_circleEnergyGap_tendsto_zero x r :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n) ⊆ closedBall (0 : ℂ) (‖x‖ + 2 * Real.exp (-r) + 1)) ∧
      (∀ n z, |f n z - circleAnnularDensity x r n z| < 1 / ((n : ℝ) + 2)) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) := by
  choose F hF using (fun n => exists_testFn_tendsto_densityCircleGap x r (circleAnnularDensity x r n) (continuous_circleAnnularDensity x r n) (add_pos_of_nonneg_of_pos (norm_nonneg _) (mul_pos zero_lt_two (Real.exp_pos _))) (tsupport_circleAnnularDensity_subset x r n))
  have hchoose n : ∃ m : ℕ, n ≤ m ∧
      |circleEnergyGap x r (F n m) - densityCircleGap x r (circleAnnularDensity x r n)| <
        1 / ((n : ℝ) + 2) := by
    obtain ⟨N, hN⟩ := ((Metric.tendsto_atTop.mp (hF n).2.2) _ (show 0 < 1 / ((n : ℝ) + 2) by positivity))
    refine ⟨max N n, le_max_right _ _, ?_⟩
    simpa only [Real.dist_eq] using hN (max N n) (le_max_left _ _)
  choose m hm using hchoose
  let f : ℕ → TestFn := fun n => F n (m n)
  have hεlim : Tendsto (fun n : ℕ => 6 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (6 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  have hbound n : |circleEnergyGap x r (f n)| ≤ 6 / ((n : ℝ) + 2) := by
    have he := (hm n).2.le
    have hb := abs_densityCircleGap_circleAnnular_le x r n
    have htri := abs_add_le
      (circleEnergyGap x r (f n) - densityCircleGap x r (circleAnnularDensity x r n))
      (densityCircleGap x r (circleAnnularDensity x r n))
    rw [sub_add_cancel] at htri
    dsimp [f] at *
    simp only [div_eq_mul_inv] at he hb ⊢
    linarith
  refine ⟨f, fun n => (hF n).1 (m n), ?_, ?_⟩
  · intro n z
    exact lt_of_lt_of_le ((hF n).2.1 (m n) z)
      (one_div_le_one_div_of_le (by positivity)
        (add_le_add (Nat.cast_le.mpr (hm n).1) le_rfl))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hεlim.neg) hεlim
    · intro n
      exact (abs_le.mp (hbound n)).1
    · intro n
      exact (abs_le.mp (hbound n)).2

/-- A weighted supremum estimate turns kernel integrability into a quantitative pairing bound. -/
theorem abs_integral_weighted_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u b k : α → ℝ) C
    (hui : Integrable (fun a => u a * k a) μ)
    (hbi : Integrable (fun a => b a * k a) μ)
    (hbn : ∀ a, 0 ≤ b a) (hb : ∀ a, |u a| ≤ C * b a) :
    |∫ a, u a * k a ∂μ| ≤ C * (∫ a, |b a * k a| ∂μ) := by
  calc
    _ ≤ ∫ a, |u a * k a| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ a, C * |b a * k a| ∂μ := by
      apply integral_mono_ae hui.norm (hbi.norm.const_mul C)
      filter_upwards with a
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hbn a)]
      exact (mul_le_mul_of_nonneg_right (hb a) (abs_nonneg _)).trans_eq (mul_assoc _ _ _)
    _ = _ := integral_const_mul _ _






/-- The originally attempted energy-gap lemma, now proved for every common-support test
sequence with the prescribed cubic uniform error. -/
theorem tendsto_circleEnergyGap_of_cubic_approx (x : ℂ) (r : ℝ) (f : ℕ → TestFn)
    (hs : ∀ n, tsupport (f n) ⊆ closedBall (0 : ℂ) (‖x‖ + 2 * Real.exp (-r) + 1))
    (he : ∀ n z, |f n z - circleAnnularDensity x r n z| < 1 / ((n : ℝ) + 2) ^ 3) :
    Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) := by
  have circleAnnularDensity_le_quadratic (n : ℕ) z : |circleAnnularDensity x r n z| ≤ ((Real.exp (-r))⁻¹ ^ 2 * (8 / Real.pi)) * ((n : ℝ) + 2) ^ 2 := by
    have annularProbabilityDensity_le_quadratic z : |DOZZ.annularProbabilityDensity n z| ≤ (8 / Real.pi) * ((n : ℝ) + 2) ^ 2 := by
      have annularProfileMass_lower : Real.pi / (8 * ((n : ℝ) + 2) ^ 2) ≤ DOZZ.annularProfileMass n := by
        let δ : ℝ := 1 / (2 * ((n : ℝ) + 2))
        have hb : ∀ z ∈ ball (1 : ℂ) δ, (1 / 2 : ℝ) ≤ DOZZ.annularProfileOnPlane n z := by
          intro z hz
          have hn := abs_norm_sub_norm_le z (1 : ℂ)
          rw [norm_one] at hn
          have hnear := mul_le_mul_of_nonneg_left (hn.trans (show ‖z - 1‖ < δ by simpa only [mem_ball, dist_eq_norm] using hz).le) (by positivity : 0 ≤ (n : ℝ) + 2)
          rw [(show ((n : ℝ) + 2) * δ = 1 / 2 by dsimp [δ]; field_simp)] at hnear
          unfold DOZZ.annularProfileOnPlane DOZZ.annularProfile
          exact le_trans (by linarith : (1 / 2 : ℝ) ≤ 1 - ((n : ℝ) + 2) * |‖z‖ - 1|)
            (le_max_right _ _)
        have hloc : (volume (ball (1 : ℂ) δ)).toReal * (1 / 2) ≤
            ∫ z in ball (1 : ℂ) δ, DOZZ.annularProfileOnPlane n z := by
          change volume.real (ball (1 : ℂ) δ) • (1 / 2 : ℝ) ≤ _
          rw [← setIntegral_const]
          apply integral_mono_ae (integrableOn_const (μ := volume) (s := ball (1 : ℂ) δ) (C := (1 / 2 : ℝ)) measure_ball_lt_top.ne)
            (DOZZ.integrable_annularProfileOnPlane n).integrableOn
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          exact hb z hz
        have hvol : (volume (ball (1 : ℂ) δ)).toReal * (1 / 2) =
            Real.pi / (8 * ((n : ℝ) + 2) ^ 2) := by
          rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (show 0 < δ by dsimp [δ]; positivity).le, ENNReal.coe_toReal, NNReal.coe_real_pi]
          dsimp [δ]
          field_simp
          ring
        rw [hvol] at hloc
        exact hloc.trans (by apply integral_mono_measure Measure.restrict_le_self ?_ (DOZZ.integrable_annularProfileOnPlane n); filter_upwards with z; exact DOZZ.annularProfile_nonneg n ‖z‖)
      have hp : DOZZ.annularProfile n ‖z‖ ≤ 1 := by
        unfold DOZZ.annularProfile
        apply max_le (by norm_num)
        have : 0 ≤ ((n : ℝ) + 2) * |‖z‖ - 1| := by positivity
        linarith
      rw [abs_of_nonneg (DOZZ.annularProbabilityDensity_nonneg n z)]
      unfold DOZZ.annularProbabilityDensity DOZZ.annularProfileOnPlane
      calc
        _ ≤ (DOZZ.annularProfileMass n)⁻¹ :=
          mul_le_of_le_one_right (inv_nonneg.mpr (DOZZ.annularProfileMass_pos n).le) hp
        _ ≤ (Real.pi / (8 * ((n : ℝ) + 2) ^ 2))⁻¹ :=
          by simpa only [one_div] using (one_div_le_one_div_of_le
            (by positivity : 0 < Real.pi / (8 * ((n : ℝ) + 2) ^ 2)) (annularProfileMass_lower))
        _ = _ := by field_simp
    rw [circleAnnularDensity, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (annularProbabilityDensity_le_quadratic _)
      (sq_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  have abs_densityCircleGap_sub_le {f} {g} {R : ℝ} {M : ℝ} {ε : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hf : Continuous f) (hg : Continuous g) (hsf : Function.support f ⊆ closedBall (0 : ℂ) R) (hsg : Function.support g ⊆ closedBall (0 : ℂ) R) (hbound : ∀ z, |g z| ≤ M) (he : ∀ z, |f z - g z| ≤ ε) : |densityCircleGap x r f - densityCircleGap x r g| ≤ ε * (2 * M + ε) * (∫ p : ℂ × ℂ, |(⟨R, R + 1, hR, lt_add_one R⟩ : ContDiffBump (0 : ℂ)) p.1 * gffKernel p.1 p.2 * (⟨R, R + 1, hR, lt_add_one R⟩ : ContDiffBump (0 : ℂ)) p.2|) + 2 * ε * (∫ z, |(⟨R, R + 1, hR, lt_add_one R⟩ : ContDiffBump (0 : ℂ)) z * (∫ w, gffKernel z w ∂circleMeasure x r)|) := by
    have abs_densityEnergy_sub_le : |densityEnergy f f - densityEnergy g g| ≤ ε * (2 * M + ε) * (∫ p : ℂ × ℂ, |(⟨R, R + 1, hR, lt_add_one R⟩ : ContDiffBump (0 : ℂ)) p.1 * gffKernel p.1 p.2 * (⟨R, R + 1, hR, lt_add_one R⟩ : ContDiffBump (0 : ℂ)) p.2|) := by
      let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
      have hfc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hsf
      have hgc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hsg
      have hfi := integrable_densityEnergy hf hf hfc hfc
      have hgi := integrable_densityEnergy hg hg hgc hgc
      let u : ℂ × ℂ → ℝ := fun p => f p.1 * f p.2 - g p.1 * g p.2
      let k : ℂ × ℂ → ℝ := fun p => gffKernel p.1 p.2
      have hes : Function.support (fun z => f z - g z) ⊆ closedBall (0 : ℂ) R := by
        intro z hz
        by_contra h
        exact hz (by simp [(show f z = 0 by by_contra hne; exact h (hsf hne)), (show g z = 0 by by_contra hne; exact h (hsg hne))])
      have hfbound z : |f z| ≤ M + ε := by
        have htri := abs_add_le (f z - g z) (g z)
        rw [sub_add_cancel] at htri
        linarith [he z, hbound z]
      have hup p : |u p| ≤ (ε * (2 * M + ε)) * (b p.1 * b p.2) := by
        rw [(show u p = (f p.1 - g p.1) * f p.2 + g p.1 * (f p.2 - g p.2) by dsimp [u]; ring)]
        calc
          _ ≤ |(f p.1 - g p.1) * f p.2| + |g p.1 * (f p.2 - g p.2)| := abs_add_le _ _
          _ ≤ (ε * b p.1) * ((M + ε) * b p.2) + (M * b p.1) * (ε * b p.2) := by
            simp only [abs_mul]
            exact add_le_add
              (mul_le_mul (abs_le_bump_of_support hR hε (fun z => f z - g z) hes he p.1) (abs_le_bump_of_support hR (add_nonneg hM hε) f hsf hfbound p.2) (abs_nonneg _) (mul_nonneg hε b.nonneg))
              (mul_le_mul (abs_le_bump_of_support hR hM g hsg hbound p.1) (abs_le_bump_of_support hR hε (fun z => f z - g z) hes he p.2) (abs_nonneg _) (mul_nonneg hM b.nonneg))
          _ = _ := by ring
      have hval : densityEnergy f f - densityEnergy g g = ∫ p, u p * k p := by
        rw [densityEnergy, densityEnergy, ← integral_sub hfi hgi]
        congr 1
        funext p
        dsimp [u, k]
        ring
      rw [hval]
      convert (abs_integral_weighted_le volume u (fun p : ℂ × ℂ => b p.1 * b p.2) k (ε * (2 * M + ε)) (by convert hfi.sub hgi using 1; ext p; simp only [u, k, Pi.sub_apply]; ring) (by convert (integrable_densityEnergy b.continuous b.continuous b.hasCompactSupport b.hasCompactSupport) using 1; ext p; dsimp [k]; ring) (fun _ => mul_nonneg b.nonneg b.nonneg) hup) using 1
      congr 2
      funext p
      congr 1
      dsimp [k]
      ring
    let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
    let k : ℂ → ℝ := fun z => ∫ w, gffKernel z w ∂circleMeasure x r
    have hk := continuous_circleKernelPotential x r
    have hfi : Integrable (fun z => f z * k z) := (hf.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hsf).mul_right
    have hgi : Integrable (fun z => g z * k z) := (hg.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hsg).mul_right
    have hc := abs_integral_weighted_le volume (fun z => f z - g z) b k ε (by convert hfi.sub hgi using 1; ext z; simp only [Pi.sub_apply]; ring) ((b.continuous.mul hk).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right)
      (fun _ => b.nonneg) (fun z => abs_le_bump_of_support hR hε _ (by intro z hz; by_contra h; exact hz (by simp [(show f z = 0 by by_contra hne; exact h (hsf hne)), (show g z = 0 by by_contra hne; exact h (hsg hne))])) he z)
    have hcval : (∫ z, f z * k z) - (∫ z, g z * k z) = ∫ z, (f z - g z) * k z := by
      rw [← integral_sub hfi hgi]
      congr 1
      funext z
      ring
    rw [← hcval] at hc
    have hid : densityCircleGap x r f - densityCircleGap x r g =
        (densityEnergy f f - densityEnergy g g) -
          2 * ((∫ z, f z * k z) - (∫ z, g z * k z)) := by
      unfold densityCircleGap
      dsimp [k]
      ring
    rw [hid]
    have htri := abs_sub (densityEnergy f f - densityEnergy g g)
      (2 * ((∫ z, f z * k z) - (∫ z, g z * k z)))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
    have := abs_densityEnergy_sub_le
    dsimp [k, b] at hc
    linarith
  let R := ‖x‖ + 2 * Real.exp (-r) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let A := ∫ p : ℂ × ℂ, |b p.1 * gffKernel p.1 p.2 * b p.2|
  let B := ∫ z, |b z * (∫ w, gffKernel z w ∂circleMeasure x r)|
  let C := (Real.exp (-r))⁻¹ ^ 2 * (8 / Real.pi)
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let bound : ℕ → ℝ := fun n =>
    5 * δ n + (2 * C * δ n + (δ n) ^ 6) * A + 2 * (δ n) ^ 3 * B
  have hδ : Tendsto δ atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [δ, Nat.cast_add]
  have hlim : Tendsto bound atTop (𝓝 0) := by
    simpa [bound] using (hδ.const_mul 5).add
      (((hδ.const_mul (2 * C)).add (hδ.pow 6)).mul_const A) |>.add
        (((hδ.pow 3).const_mul 2).mul_const B)
  have hbound n : |circleEnergyGap x r (f n)| ≤ bound n := by
    have herror z : |f n z - circleAnnularDensity x r n z| ≤ (δ n) ^ 3 := by
      simpa only [δ, div_pow, one_pow] using (he n z).le
    have hq := abs_densityCircleGap_sub_le hR
      (mul_nonneg (show 0 ≤ C by dsimp [C]; positivity) (sq_nonneg ((n : ℝ) + 2))) (by dsimp [δ]; positivity)
      (f n).continuous (continuous_circleAnnularDensity x r n)
      ((subset_tsupport _).trans (hs n)) ((support_circleAnnularDensity_subset x r n).trans (closedBall_subset_closedBall (le_add_of_nonneg_right zero_le_one)))
      (fun z => circleAnnularDensity_le_quadratic n z) herror
    change |densityCircleGap x r (f n) - densityCircleGap x r (circleAnnularDensity x r n)| ≤
      (δ n) ^ 3 * (2 * (C * ((n : ℝ) + 2) ^ 2) + (δ n) ^ 3) * A +
        2 * (δ n) ^ 3 * B at hq
    rw [(show (δ n) ^ 3 * (2 * (C * ((n : ℝ) + 2) ^ 2) + (δ n) ^ 3) = 2 * C * δ n + (δ n) ^ 6 by dsimp [δ]; field_simp [(show (n : ℝ) + 2 ≠ 0 by positivity)]), densityCircleGap_testFn] at hq
    have hc := abs_densityCircleGap_circleAnnular_le x r n
    have htri := abs_add_le
      (circleEnergyGap x r (f n) - densityCircleGap x r (circleAnnularDensity x r n))
      (densityCircleGap x r (circleAnnularDensity x r n))
    rw [sub_add_cancel] at htri
    dsimp [bound, δ] at *
    simp only [div_eq_mul_inv] at hq hc htri ⊢
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlim.neg) hlim
  · intro n
    exact (abs_le.mp (hbound n)).1
  · intro n
    exact (abs_le.mp (hbound n)).2

end DOZZ.Proofs
