/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.AnnularWeakLimit
public import DOZZ.GFFStructure.CircleCovariance
public import DOZZ.GFFStructure.GaussianClosure

/-!
# Positivity of the circle energy gap

The logarithmic energy gap is a squared distance in the completed covariance space.  We first
prove positivity for continuous densities by smooth approximation, then pass through the
annular approximations of a circle.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology

namespace DOZZ.Proofs

/-- The extended pinned energy is symmetric on compactly supported continuous densities. -/
theorem densityEnergy_comm {f g} (hf : Continuous f) (hg : Continuous g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    densityEnergy f g = densityEnergy g f := by
  have hi := integrable_densityEnergy hf hg hsf hsg
  unfold densityEnergy
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  calc
    (∫ x, ∫ y, f x * gffKernel x y * g y) =
        ∫ y, ∫ x, f x * gffKernel x y * g y := integral_integral_swap hi
    _ = ∫ y, ∫ x, g y * gffKernel y x * f x := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with x
      rw [gffKernel_comm]
      ring
    _ = ∫ p : ℂ × ℂ, g p.1 * gffKernel p.1 p.2 * f p.2 ∂(volume.prod volume) :=
      (integral_prod _ (integrable_densityEnergy hg hf hsg hsf)).symm


/-- Subtraction in the second density slot is compatible with pinned energy. -/
theorem densityEnergy_sub_right {f g h} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (hsf : HasCompactSupport f) (hsg : HasCompactSupport g)
    (hsh : HasCompactSupport h) :
    densityEnergy f (fun z => g z - h z) = densityEnergy f g - densityEnergy f h := by
  unfold densityEnergy
  calc
    (∫ p : ℂ × ℂ, f p.1 * gffKernel p.1 p.2 * (g p.2 - h p.2)) =
        ∫ p : ℂ × ℂ, (f p.1 * gffKernel p.1 p.2 * g p.2 -
          f p.1 * gffKernel p.1 p.2 * h p.2) := by
      congr 1
      funext p
      ring
    _ = _ := integral_sub (integrable_densityEnergy hf hg hsf hsg) (integrable_densityEnergy hf hh hsf hsh)



/-- Every circle energy gap `DOZZ.circleEnergyGap` is nonnegative. -/
theorem circleEnergyGap_nonneg x r f :
    0 ≤ circleEnergyGap x r f := by
  have densityEnergy_self_nonneg {f} (hf : Continuous f) (hsf : HasCompactSupport f) : 0 ≤ densityEnergy f f := by
    obtain ⟨R, hR, hRsup⟩ := hsf.isBounded.exists_pos_norm_le
    let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
    have hε n : 0 < ε n := by dsimp [ε]; positivity
    choose g hgs hge using fun n => exists_testFn_uniform_approx hf hR (by exact closure_minimal (by intro z hz; simpa only [Metric.mem_closedBall, dist_zero_right] using hRsup z (subset_tsupport f hz)) isClosed_closedBall) (hε n)
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 2) using 1
      ext n
      simp [ε, Nat.cast_add]
    obtain ⟨M, hM⟩ := hsf.exists_bound_of_continuous hf
    have := (norm_nonneg (f 0)).trans (hM 0)
    have hbound n z : |g n z| ≤ M + 1 := by
      have : |g n z - f z| < ε n := by simpa only [abs_sub_comm] using hge n z
      have : ε n ≤ 1 := by
        dsimp [ε]
        apply (div_le_one (by positivity)).mpr
        linarith only [Nat.cast_nonneg (α := ℝ) n]
      have : |f z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z
      have : |g n z| ≤ |g n z - f z| + |f z| := by
        simpa only [sub_add_cancel] using (abs_add_le (g n z - f z) (f z))
      linarith
    have hpoint z : Tendsto (fun n => g n z) atTop (𝓝 (f z)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (by simpa using tendsto_const_nhds.sub hεlim)
        (by simpa using tendsto_const_nhds.add hεlim)
      · intro n
        have := (abs_lt.mp (hge n z)).1
        linarith
      · intro n
        have := (abs_lt.mp (hge n z)).2
        linarith
    have hlim := tendsto_densityEnergy_of_common_support (fun n z => g n z) f
      (R := R + 1) (M := M + 1) (by linarith) (by linarith)
      (fun n => (g n).continuous.measurable)
      (fun n => (subset_tsupport _).trans (hgs n)) hbound hpoint
    apply le_of_tendsto_of_tendsto' (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hlim
    exact (fun n => by rw [densityEnergy_testFn]; exact DOZZ.gffCov_self_nonneg (g n))
  have densityEnergy_sub_self_eq {f} {g} (hf : Continuous f) (hg : Continuous g) (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) : densityEnergy (fun z => f z - g z) (fun z => f z - g z) = densityEnergy f f - 2 * densityEnergy f g + densityEnergy g g := by
    have densityEnergy_sub_left {h} (hh : Continuous h) (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) (hsh : HasCompactSupport h) : densityEnergy (fun z => f z - g z) h = densityEnergy f h - densityEnergy g h := by
      unfold densityEnergy
      calc
        (∫ p : ℂ × ℂ, (f p.1 - g p.1) * gffKernel p.1 p.2 * h p.2) =
            ∫ p : ℂ × ℂ, (f p.1 * gffKernel p.1 p.2 * h p.2 -
              g p.1 * gffKernel p.1 p.2 * h p.2) := by
          congr 1
          funext p
          ring
        _ = _ := integral_sub (integrable_densityEnergy hf hh hsf hsh) (integrable_densityEnergy hg hh hsg hsh)
    calc
      densityEnergy (fun z => f z - g z) (fun z => f z - g z) =
          densityEnergy f (fun z => f z - g z) -
            densityEnergy g (fun z => f z - g z) := (densityEnergy_sub_left (hf.sub hg) hsf hsg (hsf.sub hsg))
      _ = (densityEnergy f f - densityEnergy f g) -
            (densityEnergy g f - densityEnergy g g) := by rw [(densityEnergy_sub_right hf hf hg hsf hsf hsg), (densityEnergy_sub_right hg hf hg hsg hsf hsg)]
      _ = densityEnergy f f - 2 * densityEnergy f g + densityEnergy g g := by
        rw [(densityEnergy_comm hf hg hsf hsg)]
        ring
  let a : ℕ → ℂ → ℝ := fun n => circleAnnularDensity x r n
  let kσ : ℂ → ℝ := fun z => ∫ w, gffKernel z w ∂circleMeasure x r
  have hkσ := continuous_circleKernelPotential x r
  have hcrossσ : Tendsto (fun n => ∫ z, a n z * kσ z) atTop
      (𝓝 (circleSelfEnergy x r)) := by
    have htarget : (∫ z, kσ z ∂circleMeasure x r) = circleSelfEnergy x r := rfl
    simpa only [a, kσ, htarget] using (tendsto_integral_circleAnnular_mul x r kσ hkσ)
  have hcrossF : Tendsto (fun n => densityEnergy f (a n)) atTop
      (𝓝 (circleCross x r f)) := by
    have hbase : Tendsto (fun n => densityEnergy (a n) f) atTop
        (𝓝 (circleCross x r f)) := by
      apply (show Tendsto (fun n => ∫ z, a n z * (∫ w, gffKernel z w * f w)) atTop (𝓝 (circleCross x r f)) by simpa only [a, ((circleCross_eq_integral_testKernel x r f).symm)] using (tendsto_integral_circleAnnular_mul x r (fun z => ∫ w, gffKernel z w * f w) (continuous_testKernelPotential f))).congr'
      filter_upwards with n
      rw [densityEnergy, Measure.volume_eq_prod]
      calc
        (∫ z, a n z * (∫ w, gffKernel z w * f w)) =
            ∫ z, ∫ w, a n z * gffKernel z w * f w := by
          congr 1
          funext z
          rw [← integral_const_mul]
          congr 1
          funext w
          ring
        _ = ∫ p : ℂ × ℂ, a n p.1 * gffKernel p.1 p.2 * f p.2
            ∂(volume.prod volume) := (integral_prod _ (integrable_densityEnergy (continuous_circleAnnularDensity x r n) f.continuous (hasCompactSupport_circleAnnularDensity x r n) f.hasCompactSupport)).symm
    apply hbase.congr'
    filter_upwards with n
    exact densityEnergy_comm (continuous_circleAnnularDensity x r n) f.continuous
      (hasCompactSupport_circleAnnularDensity x r n) f.hasCompactSupport
  have hlim : Tendsto
      (fun n => densityEnergy (fun z => f z - a n z) (fun z => f z - a n z)) atTop
      (𝓝 (circleEnergyGap x r f)) := by
    have he n : densityEnergy (fun z => f z - a n z) (fun z => f z - a n z) =
        densityEnergy f f - 2 * densityEnergy f (a n) + densityEnergy (a n) (a n) := by
      rw [densityEnergy_sub_self_eq f.continuous (continuous_circleAnnularDensity x r n)
        f.hasCompactSupport (hasCompactSupport_circleAnnularDensity x r n)]
    rw [← (show densityEnergy f f - 2 * circleCross x r f + circleSelfEnergy x r = circleEnergyGap x r f by rw [densityEnergy_testFn]; rfl)]
    exact ((tendsto_const_nhds.sub (hcrossF.const_mul 2)).add (by convert ((((show Tendsto (fun n => densityCircleGap x r (a n)) atTop (𝓝 0) by simpa only [a] using tendsto_densityCircleGap_circleAnnular x r).add (hcrossσ.const_mul 2)).sub_const (circleSelfEnergy x r)).congr' (Filter.Eventually.of_forall (fun n => by simp only [densityCircleGap, a, kσ]; ring))) using 1; ring_nf)).congr' (Filter.Eventually.of_forall fun n => (he n).symm)
  apply le_of_tendsto_of_tendsto' (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hlim
  exact (fun n => densityEnergy_self_nonneg (f.continuous.sub (continuous_circleAnnularDensity x r n)) (f.hasCompactSupport.sub (hasCompactSupport_circleAnnularDensity x r n)))

/-- Scaling both covariance arguments scales their covariance by the square. -/
theorem gffCov_smul_self a f g :
    gffCov (a • f) (a • g) = a ^ 2 * gffCov f g := by
  rw [← inner_equatorKernelLimitMap_eq_gffCov, ← inner_equatorKernelLimitMap_eq_gffCov, map_smul, map_smul, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  ring_nf

/-- The covariance form expands on sums. -/
theorem gffCov_sub_self f g :
    gffCov (f - g) (f - g) = gffCov f f - 2 * gffCov f g + gffCov g g := by
  rw [show f - g = f + (-g) by
    ext z
    change f z - g z = f z + -g z
    ring, gffCov_add_self]
  rw [(show gffCov f (-g) = -gffCov f g by rw [← inner_equatorKernelLimitMap_eq_gffCov, ← inner_equatorKernelLimitMap_eq_gffCov, map_neg, inner_neg_right]), (show gffCov (-g) (-g) = gffCov g g by rw [← inner_equatorKernelLimitMap_eq_gffCov, ← inner_equatorKernelLimitMap_eq_gffCov, map_neg]; simp)]
  ring

/-- The cross energy is linear in a test. -/
theorem circleCross_add x r f g :
    circleCross x r (f + g) = circleCross x r f + circleCross x r g := by
  let k : ℂ → ℝ := fun z => ∫ w, gffKernel z w ∂circleMeasure x r
  have hk := continuous_circleKernelPotential x r
  have hfi : Integrable (fun z => f z * k z) :=
    (f.continuous.mul hk).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have hgi : Integrable (fun z => g z * k z) :=
    (g.continuous.mul hk).integrable_of_hasCompactSupport g.hasCompactSupport.mul_right
  unfold circleCross
  have heq : (fun z => (f + g) z * (∫ w, gffKernel z w ∂circleMeasure x r)) =
      (fun z => f z * (∫ w, gffKernel z w ∂circleMeasure x r) +
        g z * (∫ w, gffKernel z w ∂circleMeasure x r)) := by
    funext z
    simp
    ring
  rw [heq, integral_add hfi hgi]

/-- The cross energy is homogeneous in a test. -/
theorem circleCross_smul x r a f :
    circleCross x r (a • f) = a * circleCross x r f := by
  let k : ℂ → ℝ := fun z => ∫ w, gffKernel z w ∂circleMeasure x r
  unfold circleCross
  have heq : (fun z => (a • f) z * k z) = fun z => a * (f z * k z) := by
    funext z
    simp
    ring
  rw [heq, integral_const_mul]


/-- The covariance energy of a difference is controlled by the two circle gaps. -/
theorem gffCov_sub_le_circleEnergyGaps x r f g :
    gffCov (f - g) (f - g) ≤
      2 * (circleEnergyGap x r f + circleEnergyGap x r g) := by
  have circleEnergyGap_midpoint x r f g : circleEnergyGap x r ((1 / 2 : ℝ) • (f + g)) = (circleEnergyGap x r f + circleEnergyGap x r g) / 2 - gffCov (f - g) (f - g) / 4 := by
    rw [circleEnergyGap, circleEnergyGap, circleEnergyGap]
    rw [gffCov_smul_self, circleCross_smul, circleCross_add, gffCov_add_self,
      gffCov_sub_self]
    ring_nf
  have h := circleEnergyGap_nonneg x r ((1 / 2 : ℝ) • (f + g))
  rw [circleEnergyGap_midpoint] at h
  nlinarith

/-- The L² covariance energy of two test evaluations is their covariance energy `DOZZ.gffCov`. -/
theorem equatorGFF_testL2_sub_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (f g : TestFn) :
    ‖(equatorGFF_test_memLp X hX f).toLp (fun ω => X ω f) -
      (equatorGFF_test_memLp X hX g).toLp (fun ω => X ω g)‖ ^ 2 =
        gffCov (f - g) (f - g) := by
  let Uf := (equatorGFF_test_memLp X hX f).toLp (fun ω => X ω f)
  let Ug := (equatorGFF_test_memLp X hX g).toLp (fun ω => X ω g)
  have hsubAE := Lp.coeFn_sub Uf Ug
  have hdiff : (fun ω => Uf ω - Ug ω) =ᵐ[P] (fun ω => X ω (f - g)) := by
    filter_upwards [(equatorGFF_test_memLp X hX f).coeFn_toLp,
      (equatorGFF_test_memLp X hX g).coeFn_toLp] with ω hf hg
    rw [(show Uf ω = X ω f by simpa only [Uf] using hf), (show Ug ω = X ω g by simpa only [Ug] using hg)]
    exact (map_sub (X ω) f g).symm
  have hae := hsubAE.trans hdiff
  have hcov : covariance (Uf - Ug) (Uf - Ug) P = gffCov (f - g) (f - g) := by
    calc
      covariance (Uf - Ug) (Uf - Ug) P =
          covariance (fun ω => X ω (f - g)) (fun ω => X ω (f - g)) P :=
        covariance_congr_ae hae hdiff
      _ = variance (fun ω => X ω (f - g)) P := by
        rw [← covariance_self (equatorGFF_test_memLp X hX (f - g)).aemeasurable]
      _ = gffCov (f - g) (f - g) := equatorGFF_test_variance X hX (f - g)
  have hinner := covariance_L2_eq (Uf - Ug) (Uf - Ug)
  rw [(show (∫ ω, (Uf - Ug) ω ∂P) = 0 by rw [integral_congr_ae hae]; exact equatorGFF_test_integral X hX (f - g)), zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hinner
  change ‖Uf - Ug‖ ^ 2 = gffCov (f - g) (f - g)
  calc
    ‖Uf - Ug‖ ^ 2 =
        covariance (fun ω => (Uf - Ug) ω) (fun ω => (Uf - Ug) ω) P := (by simpa only using hinner.symm)
    _ = covariance (Uf - Ug) (fun ω => Uf ω - Ug ω) P := by
      exact covariance_congr_ae
        (U := fun ω => (Uf - Ug) ω) (V := fun ω => (Uf - Ug) ω)
        (U' := fun ω => (Uf - Ug) ω) (V' := fun ω => Uf ω - Ug ω)
        Filter.EventuallyEq.rfl hsubAE
    _ = gffCov (f - g) (f - g) := hcov

/-- Any sequence of smooth tests with vanishing circle gap is Cauchy in the given GFF's L². -/
theorem equatorGFF_testL2_cauchy_of_circleEnergyGap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (x : ℂ) (r : ℝ)
    (f : ℕ → TestFn)
    (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) :
    CauchySeq (fun n => (equatorGFF_test_memLp X hX (f n)).toLp
      (fun ω => X ω (f n))) := by
  let U n := (equatorGFF_test_memLp X hX (f n)).toLp (fun ω => X ω (f n))
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ : ℝ := ε ^ 2 / 8
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hf.eventually (gt_mem_nhds (show 0 < δ by dsimp [δ]; positivity))))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hqm := hN m hm
  have hqn := hN n hn
  have hbound := gffCov_sub_le_circleEnergyGaps x r (f m) (f n)
  have hnonm := circleEnergyGap_nonneg x r (f m)
  have hnon n := circleEnergyGap_nonneg x r (f n)
  have hsquare : ‖U m - U n‖ ^ 2 < ε ^ 2 := by
    dsimp [U, δ] at *
    rw [(equatorGFF_testL2_sub_norm_sq X hX (f m) (f n))]
    nlinarith
  have hnormpos : 0 ≤ ‖U m - U n‖ := norm_nonneg _
  simpa only [dist_eq_norm] using (by nlinarith)

end DOZZ.Proofs
