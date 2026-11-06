module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyGeometry
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound

open private HypoellipticAleksandrov.Parabolic.isProbabilityMeasure_parabolicNormalizedVolumeOn from HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le from HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy


/-!
# Shrinking-box recovery for parabolic Morrey affine projections

This module proves that the physical affine moment projection on arbitrary
literal forward boxes recovers a continuous value when their radii shrink and
their literal closed boxes contain the evaluation point.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped BigOperators ENNReal







variable {d : Nat}

section
variable (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)

include hr in
/-- The parabolic-coordinate diameter of a literal closed unit-height forward
box is at most twice its radius. -/
theorem parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox

    {z w : TimeVelocity d}
    (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (hw : w ∈ parabolicClosedBox 1 r t₀ v₀) :
    parabolicCoordinateDist z w ≤ 2 * r := by
  have hzBox : t₀ ≤ z.1 ∧ z.1 ≤ t₀ + r ^ 2 ∧ z.2 ∈ velocityClosedCube v₀ r := by
    simpa only [one_mul] using (mem_parabolicClosedBox_iff.mp hz)
  have hwBox : t₀ ≤ w.1 ∧ w.1 ≤ t₀ + r ^ 2 ∧ w.2 ∈ velocityClosedCube v₀ r := by
    simpa only [one_mul] using (mem_parabolicClosedBox_iff.mp hw)

  have htime : Real.sqrt |z.1 - w.1| ≤ r := by
    rw [Real.sqrt_le_iff]
    exact ⟨hr.le, (by
        rw [abs_le]
        constructor <;> linarith [hzBox.1, hzBox.2.1, hwBox.1, hwBox.2.1])⟩

  unfold parabolicCoordinateDist
  apply max_le
  · linarith
  · exact (by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [abs_le]


      exact abs_le.mp (calc
        |z.2 i - w.2 i| = |(z.2 i - v₀ i) - (w.2 i - v₀ i)| := by ring_nf
        _ ≤ |z.2 i - v₀ i| + |w.2 i - v₀ i| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (z.2 i - v₀ i) (0 ) (w.2 i - v₀ i))
        _ ≤ r + r := add_le_add ((mem_velocityClosedCube_iff.mp hzBox.2.2) i) ((mem_velocityClosedCube_iff.mp hwBox.2.2) i)
        _ = 2 * r := by ring))

variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀))) (z : TimeVelocity d) (hz : z ∈ parabolicClosedBox 1 r t₀ v₀) (δ : Real) (hbound : ∀ w : TimeVelocity d, w ∈ parabolicClosedBox 1 r t₀ v₀ → |f w| ≤ δ)

include hr hz hbound in
private theorem parabolicLpMeanNormOn_le_of_memLp_of_forall_mem_parabolicClosedBox

     :
    parabolicLpMeanNormOn d f _ hf ≤ δ := by

  let Q  := parabolicBox 1 r t₀ v₀
  let μ  := parabolicNormalizedVolumeOn Q


  letI : IsProbabilityMeasure μ :=
    _root_.HypoellipticAleksandrov.Parabolic.isProbabilityMeasure_parabolicNormalizedVolumeOn (volume_parabolicMorreyBox_pos t₀ v₀ hr) (volume_parabolicMorreyBox_lt_top t₀ v₀ hr)




  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (by
      exact (by
          calc
            eLpNorm f (parabolicExponent d) μ ≤
                μ univ ^ (parabolicExponent d).toReal⁻¹ * ENNReal.ofReal δ :=
              eLpNorm_le_of_ae_bound hf.aestronglyMeasurable (by
                  filter_upwards [(by
                      change ∀ᵐ w ∂((volume Q)⁻¹ • volume.restrict Q), w ∈ Q
                      exact Measure.ae_smul_measure
                        (ae_restrict_mem (measurableSet_parabolicBox 1 r t₀ v₀)) _)] with w hw

                  exact hbound w (by
                      rcases mem_parabolicBox_iff.mp hw with ⟨hwLeft, hwRight, hwv⟩
                      exact mem_parabolicClosedBox_iff.mpr
                        ⟨hwLeft.le, hwRight.le, fun i => (hwv i).le⟩))
            _ = ENNReal.ofReal δ := by simp))
  simpa only [parabolicLpMeanNormOn_eq_toReal, parabolicELpMeanNormOn,
    ENNReal.toReal_ofReal ((abs_nonneg (f z)).trans (hbound z hz))] using hreal

include hr hf hz hbound in
/-- A canonical affine moment projection is bounded at a point of the literal
closed forward box by a uniform closed-box bound on an integrable input. -/
theorem abs_parabolicMorreyBoxAffineProjection_apply_le_of_memLp_of_forall_mem_parabolicClosedBox

     :
    |parabolicMorreyBoxAffineProjection t₀ v₀ r f z| ≤
      (1 + 3 * (d : Real)) * δ := by
  let sharedTerm_89a6fafc5e := (∑ i : Fin d, parabolicMorreyBoxVelocitySlope t₀ v₀ r f i * (z.2 i - v₀ i))
  have hmean := parabolicLpMeanNormOn_le_of_memLp_of_forall_mem_parabolicClosedBox
    t₀ v₀ hr f hf z hz δ hbound
  have hcoeff := parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
    t₀ v₀ hr f hf

  have hsum : |sharedTerm_89a6fafc5e| ≤
      r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| := by
    calc
      |sharedTerm_89a6fafc5e| ≤
          ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i *
            (z.2 i - v₀ i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| *
          |z.2 i - v₀ i| := by simp_rw [abs_mul]
      _ ≤ ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| * r :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left ((mem_velocityClosedCube_iff.mp (mem_parabolicClosedBox_iff.mp hz).2.2) i) (abs_nonneg _)
      _ = r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| := by
        rw [Finset.mul_sum]
        simp_rw [mul_comm r]
  rw [parabolicMorreyBoxAffineProjection]
  calc
    |parabolicMorreyBoxAverage t₀ v₀ r f +
        sharedTerm_89a6fafc5e| ≤
        |parabolicMorreyBoxAverage t₀ v₀ r f| +
          r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| :=
      (abs_add_le _ _).trans (by
        linarith)
    _ ≤ (1 + 3 * (d : Real)) * parabolicLpMeanNormOn d f
        _ hf := hcoeff
    _ ≤ (1 + 3 * (d : Real)) * δ := by
      gcongr
end


section
variable (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : Continuous u)

section
variable (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r) (c : Real)

include hu hr
private theorem normalized_memLp_sub_const_of_continuous

     :
    MemLp (fun w => u w - c) (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)) := ((memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr fun w => u w - c).mpr
  (memLp_parabolicNormalizedVolumeOn_of_memLp
    (ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).left
    (Continuous.memLp_parabolicMorreyUnitBox
      (Continuous.comp (Continuous.sub hu continuous_const) (ContDiff.continuous (contDiff_parabolicAffine t₀ v₀ r))))))

private theorem parabolicMorreyBoxAffineProjection_sub_const_apply_of_continuous

     (z : TimeVelocity d) :
    parabolicMorreyBoxAffineProjection t₀ v₀ r (fun w => u w - c) z =
      parabolicMorreyBoxAffineProjection t₀ v₀ r u z - c := by
  let sharedTerm_f9c902c9a4 := ((fun _ : TimeVelocity d => -c))
  obtain ⟨w, hw⟩ := parabolicAffine_surjective (t₀ := t₀) (v₀ := v₀) hr z
  rw [← hw, parabolicMorreyBoxAffineProjection_parabolicAffine t₀ v₀ hr]
  have hcontU : Continuous (pullbackScalar u t₀ v₀ r) :=
    hu.comp (contDiff_parabolicAffine t₀ v₀ r).continuous
  have hcontC : Continuous sharedTerm_f9c902c9a4 := continuous_const
  letI : Fact (volume (parabolicMorreyUnitBox d) < ∞) :=
    ⟨lt_top_iff_ne_top.mpr (volume_parabolicMorreyUnitBox_ne_top d)⟩




  have hpull : pullbackScalar (fun y => u y - c) t₀ v₀ r =
      pullbackScalar u t₀ v₀ r + fun _ => -c := by
    funext y
    simp only [pullbackScalar_apply, Pi.add_apply]
    ring
  rw [hpull, parabolicMorreyUnitAffineProjection_add _ _ ((Continuous.memLp_parabolicMorreyUnitBox hcontU).integrable (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d)) ((Continuous.memLp_parabolicMorreyUnitBox hcontC).integrable (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d)) (by
      intro i
      exact (Continuous.memLp_parabolicMorreyUnitBox
        (hcontU.mul ((continuous_apply i).comp continuous_snd))).integrable
        (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d)) (by
      intro i
      exact (Continuous.memLp_parabolicMorreyUnitBox
        (hcontC.mul ((continuous_apply i).comp continuous_snd))).integrable
        (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d))]
  have hconstant : parabolicMorreyUnitAffineProjection sharedTerm_f9c902c9a4 w =
      -c := by
    simpa using congrFun
      (parabolicMorreyUnitAffineProjection_reproduces_velocity_affine (-c) 0) w
  rw [parabolicMorreyBoxAffineProjection_parabolicAffine t₀ v₀ hr]
  simp only [Pi.add_apply]
  rw [hconstant]
  ring
end


include hu in
/-- Uniform closed-forward-box oscillation controls the error of the canonical
affine projection at a closed-box point. -/
theorem
  abs_parabolicMorreyBoxAffineProjection_sub_apply_le_of_continuous_of_forall_mem_parabolicClosedBox

    (z : TimeVelocity d) (t₀ : Real) (v₀ : PDE.Vec d) {r : Real}
    (hr : 0 < r) (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (δ : Real)
    (hbound : ∀ w : TimeVelocity d, w ∈ parabolicClosedBox 1 r t₀ v₀ →
      |u w - u z| ≤ δ) :
    |parabolicMorreyBoxAffineProjection t₀ v₀ r u z - u z| ≤
      (1 + 3 * (d : Real)) * δ := by


  have hcore :=
    abs_parabolicMorreyBoxAffineProjection_apply_le_of_memLp_of_forall_mem_parabolicClosedBox
      t₀ v₀ hr (fun w => u w - u z) (normalized_memLp_sub_const_of_continuous u hu t₀ v₀ hr (u z)) z hz δ hbound
  rw [parabolicMorreyBoxAffineProjection_sub_const_apply_of_continuous
    u hu t₀ v₀ hr (u z) z] at hcore
  exact hcore
end


private theorem dist_lt_of_mem_parabolicClosedBox_of_two_mul_radius_lt
     (t₀ : Real) (v₀ : PDE.Vec d) {r η : Real}
    (hr : 0 < r) (hrsmall : r ≤ 1 / 2)
    {z w : TimeVelocity d}
    (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (hw : w ∈ parabolicClosedBox 1 r t₀ v₀)
    (hsmall : 2 * r < η) :
    dist w z < η := by
  have hcoord := parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox
    t₀ v₀ hr hz hw





  rw [Prod.dist_eq]
  apply max_lt
  · exact (show |w.1 - z.1| ≤ 2 * r by
      rw [abs_sub_comm]
      calc
        |z.1 - w.1| ≤ (2 * r) ^ 2 := (by

            have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr ((le_max_left _ _).trans hcoord)
            rwa [Real.sq_sqrt (abs_nonneg _)] at hsquare)
        _ ≤ 2 * r := by nlinarith).trans_lt hsmall
  · exact (show ‖w.2 - z.2‖ ≤ 2 * r by
      rw [norm_sub_rev]
      exact (le_max_right _ _).trans hcoord).trans_lt hsmall

variable (u : HypoellipticAleksandrov.Parabolic.ScalarField d)

/-- Canonical affine moment projections on literal forward boxes shrinking to
a point recover a continuous function at that point. -/
theorem tendsto_parabolicMorreyBoxAffineProjection_apply_of_continuous
      (hu : Continuous u)
    (z : TimeVelocity d) (t : Nat → Real) (v : Nat → PDE.Vec d)
    (r : Nat → Real) (hr : ∀ n : Nat, 0 < r n)
    (hz : ∀ n : Nat, z ∈ parabolicClosedBox 1 (r n) (t n) (v n))
    (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto
      (fun n => parabolicMorreyBoxAffineProjection (t n) (v n) (r n) u z)
      atTop (nhds (u z)) := by
  let sharedTerm_b0f2ec0155 := (1 + 3 * (d : Real))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCpos : 0 < sharedTerm_b0f2ec0155 := by positivity
  obtain ⟨η, hηpos, hη⟩ := (Metric.continuousAt_iff.mp hu.continuousAt)
    (ε / (2 * (sharedTerm_b0f2ec0155))) (div_pos hε (mul_pos (by norm_num) hCpos))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hr0) (min (η / 2) (1 / 2))
    (lt_min (half_pos hηpos) (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  have hnsmall  := hN n hn



  have hprojection :=
  abs_parabolicMorreyBoxAffineProjection_sub_apply_le_of_continuous_of_forall_mem_parabolicClosedBox
      u hu z (t n) (v n) (hr n) (hz n)
      (ε / (2 * (sharedTerm_b0f2ec0155))) (by
          intro w hw
          have hdist := dist_lt_of_mem_parabolicClosedBox_of_two_mul_radius_lt
            (t n) (v n) (hr n) (by
                have : r n < 1 / 2 := by
                  simpa only [Real.dist_eq, sub_zero, abs_of_pos (hr n)] using
                    hnsmall.trans_le (min_le_right _ _)
                exact this.le) (hz n) hw (show 2 * r n < η by
                have hlt : r n < η / 2 := by
                  simpa only [Real.dist_eq, sub_zero, abs_of_pos (hr n)] using
                    hnsmall.trans_le (min_le_left _ _)
                nlinarith [hηpos])

          exact (hη hdist).le)
  rw [Real.dist_eq]
  calc
    |parabolicMorreyBoxAffineProjection (t n) (v n) (r n) u z - u z| ≤
        (sharedTerm_b0f2ec0155) * (ε / (2 * (sharedTerm_b0f2ec0155))) := hprojection
    _ = ε / 2 := by field_simp [hCpos.ne']
    _ < ε := half_lt_self hε

/-- Smooth shrinking-box recovery, as the direct `ContDiff` specialization. -/
theorem tendsto_parabolicMorreyBoxAffineProjection_apply_of_contDiff
      (hu : ContDiff Real 2 u)
    (z : TimeVelocity d) (t : Nat → Real) (v : Nat → PDE.Vec d)
    (r : Nat → Real) (hr : ∀ n : Nat, 0 < r n)
    (hz : ∀ n : Nat, z ∈ parabolicClosedBox 1 (r n) (t n) (v n))
    (hr0 : Tendsto r atTop (nhds 0)) : type_of% (tendsto_parabolicMorreyBoxAffineProjection_apply_of_continuous
    u hu.continuous z t v r hr hz hr0) := tendsto_parabolicMorreyBoxAffineProjection_apply_of_continuous
    u hu.continuous z t v r hr hz hr0

end HypoellipticAleksandrov.Parabolic
