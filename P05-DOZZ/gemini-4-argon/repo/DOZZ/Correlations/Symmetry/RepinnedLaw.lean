/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.RepinnedCovariance
public import DOZZ.Correlations.Symmetry.ReflectionTestCovariance
public import DOZZ.GMC.GaussianInputs
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Distributions
namespace DOZZ.Proofs


/-- Correlated affine re-pinning produces a genuine equator GFF on the same probability space. -/
theorem isEquatorGFF_symmetryRepinnedField
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc) :
    IsEquatorGFF P (symmetryRepinnedField X (fun ω => Xc ω 1 0)) := by
  have reflection_repinned_variance f : variance (fun ω => symmetryRepinnedField X (fun ω' => Xc ω' 1 0) ω f) P = gffCov f f := by
    let : IsProbabilityMeasure P := hX.1
    let L := fun ω => Xc ω 1 0
    let A := fun ω => X ω (symmetryReflectionTest f)
    let m := testMass f
    have hL : MemLp L 2 P := hXc.2.1 1 0
    have hAmean : ∫ ω, A ω ∂P = 0 := equatorGFF_test_integral X hX (symmetryReflectionTest f)
    have hLmean : ∫ ω, L ω ∂P = 0 := (circleAverage_isGaussianProcess P X Xc hX hXc).2 1 0
    have hvarL : variance L P = 2 * symmetryReflectionKappa := by
      rw [variance_eq_integral hL.aemeasurable, hLmean]
      simp only [sub_zero, pow_two]
      exact reflection_normalization_variance P X hX Xc hXc
    have hd : Integrable (fun x => f x * symmetryReflectionPotential x) volume :=
      (f.continuous.mul symmetryReflectionPotential_continuous).integrable_of_hasCompactSupport
        f.hasCompactSupport.mul_right
    have hsplit : (∫ x, f x * (symmetryReflectionPotential x + symmetryReflectionKappa)) =
        (∫ x, f x * symmetryReflectionPotential x) + symmetryReflectionKappa * m := by
      simp_rw [mul_add]
      rw [integral_add hd ((f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).mul_const symmetryReflectionKappa), integral_mul_const]
      dsimp [m, testMass]
      ring
    have heY : (fun ω => symmetryRepinnedField X L ω f) = fun ω => A ω - m * L ω := by
      funext ω
      rw [symmetryRepinnedField_apply]
      dsimp [A, L, m, testMass]
      ring
    change variance (fun ω => symmetryRepinnedField X L ω f) P = _
    rw [heY]
    rw [variance_fun_sub (equatorGFF_test_memLp X hX (symmetryReflectionTest f) : MemLp A 2 P) (hL.const_mul m : MemLp (fun ω => m * L ω) 2 P), equatorGFF_test_variance X hX,
      covariance_const_mul_right, variance_const_mul, hvarL, (show covariance A L P = ∫ x, f x * (symmetryReflectionPotential x + symmetryReflectionKappa) by rw [(show covariance A L P = gaussianCovariance P A L by simp only [covariance, hAmean, hLmean, sub_zero, gaussianCovariance])]; exact reflection_test_normalization_covariance P X hX Xc hXc f), hsplit,
      gffCov_symmetryReflectionTest]
    dsimp [m]
    ring
  let : IsProbabilityMeasure P := hX.1
  have hLm : Measurable (fun ω => Xc ω 1 0) :=
    (hXc.1 0).comp (measurable_id.prodMk measurable_const)
  refine ⟨hX.1, fun f => ?_⟩
  have hmeas := symmetryRepinnedField_eval_measurable P X hX (fun ω => Xc ω 1 0) hLm f
  refine ⟨hmeas, ?_⟩
  have hj := equatorGFF_finite_evaluations_with_L_jointly_gaussian P X hX
    (fun ω => Xc ω 1 0) (reflection_normalization_gaussianL2 P X hX Xc hXc)
    (fun _ : Fin 1 => symmetryReflectionTest f)
  let a : Option (Fin 1) → ℝ := fun i => match i with
    | none => -(∫ x, f x)
    | some _ => 1
  obtain ⟨_hmem, v, hv⟩ := hj.2.2 a
  have he : (fun ω => ∑ i, a i * (match i with
      | none => Xc ω 1 0
      | some _ => X ω (symmetryReflectionTest f))) =
      fun ω => symmetryRepinnedField X (fun ω' => Xc ω' 1 0) ω f := by
    funext ω
    simp only [Fintype.sum_option, a, Fin.sum_univ_one, one_mul, neg_mul,
      symmetryRepinnedField_apply]
    ring
  change P.map (fun ω => ∑ i, a i * (match i with
    | none => Xc ω 1 0
    | some _ => X ω (symmetryReflectionTest f))) = gaussianReal 0 v at hv
  rw [he] at hv
  have hlaw : HasLaw (fun ω => symmetryRepinnedField X (fun ω' => Xc ω' 1 0) ω f)
      (gaussianReal 0 v) P := ⟨hmeas.aemeasurable, hv⟩
  refine ⟨v, ?_, hv⟩
  have hh := hlaw.variance_eq
  rw [variance_id_gaussianReal, reflection_repinned_variance f] at hh
  exact hh.symm
end DOZZ.Proofs
