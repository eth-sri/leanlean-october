/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalKernelL2
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# DOZZ.GFF.LocalSchur

The local square-integrability estimate for the pinned kernel yields the Schur bound for its
covariance form on compactly supported functions.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace Topology

namespace DOZZ

/-- The covariance `gffCov` is the product integral against its kernel `gffKernel`. -/
theorem gffCov_eq_integral_gffKernel (f g : TestFn) :
    gffCov f g = ∫ p : ℂ × ℂ, f p.1 * gffKernel p.1 p.2 * g p.2 := by
  let μc : Measure (ℂ × ℂ) := volume.prod volume
  let μv : Measure (GaussianFields.Vec 2 × GaussianFields.Vec 2) :=
    volume.prod
      volume
  let Fv : GaussianFields.Vec 2 × GaussianFields.Vec 2 → ℝ := fun p =>
    testFnVec f p.1 * gffKernelVec p.1 p.2 * testFnVec g p.2
  let Fc : ℂ × ℂ → ℝ := fun p => f p.1 * gffKernel p.1 p.2 * g p.2
  have hcomp : Fc = Fv ∘ complexPairToVecTwo := by
    funext p
    change f p.1 * gffKernel p.1 p.2 * g p.2 =
      Fv (complexToVecTwo p.1, complexToVecTwo p.2)
    simp [Fv, gffKernelVec, testFnVec_complexToVecTwo]
  have hformula : gffCov f g = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
      Fv p ∂μv := by
    calc
      gffCov f g = testFnLogPairing f g + testFnPotential f * testMass g +
          testMass f * testFnPotential g := gffCov_eq_equatorLogEnergy f g
      _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2, Fv p ∂μv := by
        symm
        simpa [Fv, μv] using integral_gffKernelVec_pair f g
  have hchange := volume_preserving_complexPairToVecTwo.integral_comp'
    (f := complexPairToVecTwo) (g := Fv)
  calc
    gffCov f g = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2, Fv p ∂μv := hformula
    _ = ∫ p : ℂ × ℂ, Fv (complexPairToVecTwo p) ∂μc := hchange.symm
    _ = ∫ p : ℂ × ℂ, Fc p ∂μc := by
      simp_all
    _ = ∫ p : ℂ × ℂ, f p.1 * gffKernel p.1 p.2 * g p.2 ∂μc := rfl
section
variable {α : Type*} [MeasurableSpace α]

/-- A square-integrable real function belongs to `L²`. -/
theorem memLp_two_of_integrable_norm_sq {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hsq : Integrable (fun x => ‖f x‖ ^ 2) μ) : MemLp f 2 μ := (integrable_norm_rpow_iff hf (by norm_num) (by simp)).mp (by simp_all)

/-- Cauchy--Schwarz for a product integral, in the exact `L²` form used by the local kernel
operator. -/
theorem abs_integral_mul_le_l2 (μ : Measure α)
    {K F : α → ℝ} (hK : MemLp K 2 μ) (hF : MemLp F 2 μ) :
    |∫ x, K x * F x ∂μ| ≤
      (∫ x, ‖K x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, ‖F x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hK' : MemLp K (ENNReal.ofReal 2) μ := by simp_all
  have hF' : MemLp F (ENNReal.ofReal 2) μ := by simp_all
  calc
    |∫ x, K x * F x ∂μ| = ‖∫ x, K x * F x ∂μ‖ := by rfl
    _ ≤ ∫ x, ‖K x * F x‖ ∂μ :=
      norm_integral_le_integral_norm (fun x => K x * F x)
    _ = ∫ x, ‖K x‖ * ‖F x‖ ∂μ := by
      simp
    _ ≤ _ := by simpa using integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hK' hF'

end
section
variable (R : ℝ)
section
variable (f g : TestFn)

/-- Tensor products of two test functions lie in `L²` on a finite product ball. -/
theorem memLp_testFnTensor_two_on_ball :
    MemLp (fun p : ℂ × ℂ => f p.1 * g p.2) 2
      ((volume : Measure ℂ).restrict (ball (0 : ℂ) R) |>.prod
        ((volume : Measure ℂ).restrict (ball (0 : ℂ) R))) := by
  let B : Set ℂ := ball 0 R
  let μB : Measure ℂ := (volume : Measure ℂ).restrict B
  have hBlt : volume B < ⊤ := by
    exact measure_ball_lt_top
  have : IsFiniteMeasure μB := (MeasureTheory.isFiniteMeasure_restrict).2 hBlt.ne
  have hf4 : MemLp f 4 (volume : Measure ℂ) :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hg4 : MemLp g 4 (volume : Measure ℂ) :=
    g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hfB : MemLp f 4 μB := hf4.mono_measure Measure.restrict_le_self
  have hgB : MemLp g 4 μB := hg4.mono_measure Measure.restrict_le_self
  have htriple : ENNReal.HolderTriple 4 4 2 := by
    have hreal : (4 : ℝ).HolderTriple 4 2 := by
      constructor <;> norm_num
    simpa using hreal.ennrealOfReal
  exact by
    have := htriple
    change MemLp ((fun p => f p.1) * (fun p => g p.2)) 2
      (μB.prod μB)
    exact (hfB.comp_fst μB).mul (hgB.comp_snd μB)

/-- The square `L²` integral of a tensor product factors over the two coordinates. -/
theorem integral_sq_testFnTensor_on_ball :
    ∫ p : ℂ × ℂ, ‖f p.1 * g p.2‖ ^ 2 ∂
        ((volume : Measure ℂ).restrict (ball (0 : ℂ) R) |>.prod
          ((volume : Measure ℂ).restrict (ball (0 : ℂ) R))) =
      (∫ x in ball (0 : ℂ) R, ‖f x‖ ^ 2) *
        (∫ y in ball (0 : ℂ) R, ‖g y‖ ^ 2) := by
  rw [Measure.prod_restrict]
  calc
    ∫ p : ℂ × ℂ, ‖f p.1 * g p.2‖ ^ 2
        ∂(volume.prod volume).restrict
          (ball 0 R ×ˢ ball 0 R) =
        ∫ p : ℂ × ℂ, (‖f p.1‖ ^ 2) * (‖g p.2‖ ^ 2)
          ∂(volume.prod volume).restrict
            (ball 0 R ×ˢ ball 0 R) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [norm_mul, mul_pow]
    _ = _ := setIntegral_prod_mul (fun x : ℂ => ‖f x‖ ^ 2)
        (fun y => ‖g y‖ ^ 2) _ _

end

/-- The pinned covariance on a compactly supported test is bounded by the local `L²` norm, with
the Hilbert--Schmidt constant given by the square-integrable kernel on the ball. -/
theorem abs_gffCov_self_le_localL2 (f : TestFn)
    (hsupp : Function.support f ⊆ ball (0 : ℂ) R) :
    |gffCov f f| ≤
      (∫ p : ℂ × ℂ in ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R,
        ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ x in ball (0 : ℂ) R, ‖f x‖ ^ 2) := by
  let B : Set ℂ := ball 0 R
  let S : Set (ℂ × ℂ) := B ×ˢ B
  let μ : Measure (ℂ × ℂ) := volume.prod volume
  let μB : Measure (ℂ × ℂ) :=
    (volume.restrict B).prod (volume.restrict B)
  let K : ℂ × ℂ → ℝ := fun p => gffKernel p.1 p.2
  let F : ℂ × ℂ → ℝ := fun p => f p.1 * f p.2
  let H : ℂ × ℂ → ℝ := fun p => f p.1 * gffKernel p.1 p.2 * f p.2
  have hS : MeasurableSet S := by measurability
  have hH_eq_indicator : H = S.indicator H := by
    funext p
    by_cases hp : p ∈ S
    · simp_all
    · have hp' : ¬ (p.1 ∈ B ∧ p.2 ∈ B) := by simpa [S] using hp
      by_cases hfirst : p.1 ∈ B
      · have hsecond : p.2 ∉ B := by
          simp_all
        have hzero : f p.2 = 0 := by
          by_contra hne
          apply hsecond
          exact hsupp (by assumption)
        aesop
      · have hzero : f p.1 = 0 := by
          by_contra hne
          apply hfirst
          exact hsupp (by assumption)
        aesop
  have hKsqOn : IntegrableOn (fun p => ‖K p‖ ^ 2) S μ := by
    simpa [K, B, S, μ, Real.norm_eq_abs] using
      (integrable_gffKernel_sq_on_pair_ball R)
  have hKsq : Integrable (fun p => ‖K p‖ ^ 2) μB := by
    change Integrable (fun p => ‖K p‖ ^ 2)
      ((volume.restrict B).prod (volume.restrict B))
    rwa [Measure.prod_restrict]
  have hKmeas : Measurable K := by
    change Measurable (fun p : ℂ × ℂ => gffKernel p.1 p.2)
    fun_prop [gffKernel, normPlus]
  have hK := memLp_two_of_integrable_norm_sq
    hKmeas.aestronglyMeasurable hKsq
  have hF : MemLp F 2 μB := by
    simpa [F, B, μB] using memLp_testFnTensor_two_on_ball R f f
  have hcovlocal : gffCov f f = ∫ p, K p * F p ∂μB := by
    rw [gffCov_eq_integral_gffKernel f f]
    calc
      (∫ p : ℂ × ℂ, f p.1 * gffKernel p.1 p.2 * f p.2 ∂μ) =
          ∫ p, S.indicator H p ∂μ := by
        apply integral_congr_ae
        filter_upwards with p
        exact congrFun hH_eq_indicator p
      _ = ∫ p in S, H p ∂μ := integral_indicator hS
      _ = ∫ p in S, K p * F p ∂μ := by
        apply setIntegral_congr_ae hS
        filter_upwards with p hp
        simp [H, K, F]
        ring
      _ = ∫ p, K p * F p ∂μB := by
        rw [← Measure.prod_restrict]
  let a : ℝ := ∫ x in B, ‖f x‖ ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg fun x => sq_nonneg ‖f x‖
  have hroot : (a * a) ^ (1 / 2 : ℝ) = a := by
    rw [← Real.sqrt_eq_rpow, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  have hfactor' : (∫ p, ‖F p‖ ^ 2 ∂μB) = a * a := by
    simpa [F, B, μB, a] using (integral_sq_testFnTensor_on_ball R f f)
  calc
    |gffCov f f| = |∫ p, K p * F p ∂μB| := by simp_all
    _ ≤ (∫ p, ‖K p‖ ^ 2 ∂μB) ^ (1 / 2) *
          (∫ p, ‖F p‖ ^ 2 ∂μB) ^ (1 / 2) := (abs_integral_mul_le_l2 μB hK hF)
    _ = (∫ p : ℂ × ℂ in B ×ˢ B, ‖gffKernel p.1 p.2‖ ^ 2) ^
          (1 / 2 : ℝ) * a := by
      rw [hfactor', hroot]
      congr 2
      change ∫ p, ‖K p‖ ^ 2 ∂
          ((volume.restrict B).prod ((volume : Measure ℂ).restrict B)) =
        ∫ p in S, ‖gffKernel p.1 p.2‖ ^ 2 ∂μ
      rw [Measure.prod_restrict]
    _ = _ := by rfl

end


end DOZZ

end
