/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.AnnularEnergyConvergence
public import GaussianFields.LogCorrelated.ABK.TestFunctionAlgebra

/-!
# DOZZ.GFF.EquatorField

The annular finite-energy realization of the equator-pinned Gaussian field.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace DOZZ

/-- The mass functional is linear on compactly supported test functions. -/
theorem testMass_add (f g : TestFn) :
    testMass (f + g) = testMass f + testMass g := by
  have hf : Integrable f (volume : Measure ℂ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable g (volume : Measure ℂ) :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  apply integral_add <;> assumption

theorem testMass_smul (a : ℝ) (f : TestFn) :
    testMass (a • f) = a * testMass f := by
  apply integral_const_mul

/-- The centered annular test as a function on `Vec 2`. -/
theorem annularCenteredTestFn_eq_testFnVec_sub (f : TestFn) (n : ℕ)
    (x : GaussianFields.Vec 2) :
    annularCenteredTestFn f n x =
      testFnVec f x - testMass f * annularProbabilityDensityVec n x := by
  rfl

theorem annularCenteredTestFn_add (f g : TestFn) (n : ℕ) :
    annularCenteredTestFn (f + g) n =
      annularCenteredTestFn f n + annularCenteredTestFn g n := by
  apply GaussianFields.MeanZeroTestFunction.ext
  intro x
  change annularCenteredTestFn (f + g) n x =
    annularCenteredTestFn f n x + annularCenteredTestFn g n x
  rw [annularCenteredTestFn_eq_testFnVec_sub,
    annularCenteredTestFn_eq_testFnVec_sub,
    annularCenteredTestFn_eq_testFnVec_sub]
  simp [testFnVec, testMass_add]
  ring

theorem annularCenteredTestFn_smul (a : ℝ) (f : TestFn) (n : ℕ) :
    annularCenteredTestFn (a • f) n = a • annularCenteredTestFn f n := by
  apply GaussianFields.MeanZeroTestFunction.ext
  intro x
  change annularCenteredTestFn (a • f) n x =
    a * annularCenteredTestFn f n x
  rw [annularCenteredTestFn_eq_testFnVec_sub,
    annularCenteredTestFn_eq_testFnVec_sub]
  simp [testFnVec, testMass_smul]
  ring

/-- The canonical ABK Hilbert kernel of the `n`th centered annular test. -/
noncomputable def annularABKKernel (f : TestFn) (n : ℕ) :
    GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 :=
  let ζ := GaussianFields.abkStandardCutoff 2
  GaussianFields.abkLogKernelLp (GaussianFields.abkNormalization ζ) ζ
    (annularCenteredTestFn f n)
    (GaussianFields.memLp_abkLogKernelProd_canonical (by norm_num) ζ
      (annularCenteredTestFn f n))

/-- The rescaled annular kernel used to approximate the pinned covariance. -/
noncomputable def equatorKernelApprox (f : TestFn) (n : ℕ) :
    GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 :=
  Real.sqrt (2 * Real.pi) • annularABKKernel f n

theorem annularABKKernel_add (f g : TestFn) (n : ℕ) :
    annularABKKernel (f + g) n = annularABKKernel f n + annularABKKernel g n := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hψ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n)
  have hφ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn g n)
  have hsum := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn (f + g) n)
  simpa [annularABKKernel, annularCenteredTestFn_add] using
    (GaussianFields.abkLogKernelLp_add (GaussianFields.abkNormalization ζ) ζ
      (annularCenteredTestFn f n) (annularCenteredTestFn g n) hψ hφ (by
    simpa only [← annularCenteredTestFn_add] using hsum))

theorem annularABKKernel_smul (a : ℝ) (f : TestFn) (n : ℕ) :
    annularABKKernel (a • f) n = a • annularABKKernel f n := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hψ := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n)
  have hsmul := GaussianFields.memLp_abkLogKernelProd_canonical
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn (a • f) n)
  simpa [annularABKKernel, annularCenteredTestFn_smul] using
    (GaussianFields.abkLogKernelLp_smul (GaussianFields.abkNormalization ζ) ζ a
      (annularCenteredTestFn f n) hψ (by
    simpa only [← annularCenteredTestFn_smul] using hsmul))

theorem equatorKernelApprox_add (f g : TestFn) (n : ℕ) :
    equatorKernelApprox (f + g) n =
      equatorKernelApprox f n + equatorKernelApprox g n := by
  rw [equatorKernelApprox, equatorKernelApprox, equatorKernelApprox,
    annularABKKernel_add, smul_add]

theorem equatorKernelApprox_smul (a : ℝ) (f : TestFn) (n : ℕ) :
    equatorKernelApprox (a • f) n = a • equatorKernelApprox f n := by
  rw [equatorKernelApprox, equatorKernelApprox, annularABKKernel_smul]
  simp [smul_smul, mul_comm]

section
variable (f g : TestFn) (n k : ℕ)

theorem inner_annularABKKernel_eq_covarianceConstant_pairing :
    ⟪annularABKKernel f n, annularABKKernel g k⟫_ℝ =
      GaussianFields.abkLGFCovarianceConstant 2 *
        GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn g k) := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hcov := GaussianFields.covariance_abkLogCorrelatedFieldL2Canonical_eq_logCovariancePairing
    (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n) (annularCenteredTestFn g k)
  calc
    _ = cov[
        GaussianFields.scaleSpaceWhiteNoiseL2 2 (annularABKKernel f n),
        GaussianFields.scaleSpaceWhiteNoiseL2 2 (annularABKKernel g k);
        GaussianFields.scaleSpaceWhiteNoiseMeasure 2] := (GaussianFields.covariance_scaleSpaceWhiteNoiseL2
            (annularABKKernel f n) (annularABKKernel g k)).symm
    _ = cov[
        GaussianFields.abkLogCorrelatedFieldL2Canonical
          (by norm_num : 0 < 2) ζ (annularCenteredTestFn f n),
        GaussianFields.abkLogCorrelatedFieldL2Canonical
          (by norm_num : 0 < 2) ζ (annularCenteredTestFn g k);
        GaussianFields.scaleSpaceWhiteNoiseMeasure 2] := by
          rfl
    _ = _ := hcov

theorem inner_equatorKernelApprox_eq_pairing :
    ⟪equatorKernelApprox f n, equatorKernelApprox g k⟫_ℝ =
      GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g k) := by
  have hscale : (Real.sqrt (2 * Real.pi)) ^ 2 *
      GaussianFields.abkLGFCovarianceConstant 2 = 1 := by
    rw [abkLGFCovarianceConstant_two_eq_one_div_two_pi, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    field_simp [ne_of_gt Real.pi_pos]
  rw [equatorKernelApprox, equatorKernelApprox,
    inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [inner_annularABKKernel_eq_covarianceConstant_pairing]
  grind

end

theorem equatorKernelApprox_cauchy (f : TestFn) : CauchySeq (equatorKernelApprox f) := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0, ← prod_atTop_atTop_eq]
  have hd := tendsto_annularCenteredPairing_gffCov f f
  have h := ((hd.comp tendsto_fst).add (hd.comp tendsto_snd)).sub
    ((tendsto_annularCenteredPairing_prod f f).const_mul 2)
  have hs : Tendsto (fun ij : ℕ × ℕ => Real.sqrt
      (⟪equatorKernelApprox f ij.1, equatorKernelApprox f ij.1⟫_ℝ +
       ⟪equatorKernelApprox f ij.2, equatorKernelApprox f ij.2⟫_ℝ -
       2 * ⟪equatorKernelApprox f ij.1, equatorKernelApprox f ij.2⟫_ℝ)) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_def, inner_equatorKernelApprox_eq_pairing, two_mul, sub_self,
      Real.sqrt_zero] using (Real.continuous_sqrt.tendsto _).comp h
  convert hs using 1
  ext ij
  rw [dist_eq_norm, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    add_sub_right_comm, ← norm_sub_sq_real, Real.sqrt_sq (norm_nonneg _)]

/-- The limit of the rescaled annular kernels in the white-noise Hilbert space. -/
noncomputable def equatorKernelLimit (f : TestFn) :
    GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 :=
  limUnder atTop (equatorKernelApprox f)

theorem equatorKernelApprox_tendsto (f : TestFn) :
    Tendsto (equatorKernelApprox f) atTop (𝓝 (equatorKernelLimit f)) := (equatorKernelApprox_cauchy f).tendsto_limUnder

/-- The finite-energy extension of the annular ABK kernel map to all test functions. -/
noncomputable def equatorKernelLimitMap :
    TestFn →ₗ[ℝ] GaussianFields.ScaleSpaceWhiteNoiseHilbert 2 where
  toFun := equatorKernelLimit
  map_add' f g := by
    have hsum := (equatorKernelApprox_tendsto f).add (equatorKernelApprox_tendsto g)
    exact tendsto_nhds_unique (equatorKernelApprox_tendsto (f + g)) (by
      convert hsum using 1
      funext n
      exact equatorKernelApprox_add f g n)
  map_smul' a f := by
    have hsmul := ((continuous_const_smul a).tendsto (equatorKernelLimit f)).comp
      (equatorKernelApprox_tendsto f)
    exact tendsto_nhds_unique (equatorKernelApprox_tendsto (a • f)) (by
      convert hsmul using 1
      funext n
      exact equatorKernelApprox_smul a f n)

/-- The equator-pinned field as an `L²`-valued real-linear map on test functions. -/
noncomputable def equatorFieldL2 :
    TestFn →ₗ[ℝ]
      Lp ℝ 2 (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) :=
  (GaussianFields.scaleSpaceWhiteNoiseL2 2).toLinearMap.comp equatorKernelLimitMap

theorem inner_equatorKernelLimitMap_eq_gffCov (f g : TestFn) :
    ⟪equatorKernelLimitMap f, equatorKernelLimitMap g⟫_ℝ = gffCov f g := by
  have hInner : Tendsto
      (fun n => ⟪equatorKernelApprox f n, equatorKernelApprox g n⟫_ℝ)
      atTop (𝓝 ⟪equatorKernelLimit f, equatorKernelLimit g⟫_ℝ) :=
    (equatorKernelApprox_tendsto f).inner (equatorKernelApprox_tendsto g)
  have hPair : Tendsto
      (fun n => GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g n))
      atTop (𝓝 ⟪equatorKernelLimitMap f, equatorKernelLimitMap g⟫_ℝ) := by
    simpa [equatorKernelLimitMap] using hInner.congr' (Filter.Eventually.of_forall fun n => inner_equatorKernelApprox_eq_pairing f g n n)
  exact tendsto_nhds_unique hPair (tendsto_annularCenteredPairing_gffCov f g)

/-- Every test evaluation is centered Gaussian with variance the diagonal DOZZ covariance. -/
theorem map_equatorFieldL2_eq_gaussianReal (f : TestFn) :
    Measure.map (equatorFieldL2 f) (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal (gffCov f f)) := by
  have hnorm :
      ‖equatorKernelLimitMap f‖ ^ 2 = gffCov f f := by
    calc
      _ = ⟪equatorKernelLimitMap f, equatorKernelLimitMap f⟫_ℝ := by
        symm
        exact inner_self_eq_norm_sq_to_K _
      _ = gffCov f f := inner_equatorKernelLimitMap_eq_gffCov f f
  change Measure.map
      (GaussianFields.scalarWhiteNoiseL2 3 (equatorKernelLimitMap f))
      (GaussianFields.scalarWhiteNoiseMeasure 3) =
    ProbabilityTheory.gaussianReal 0 (Real.toNNReal (gffCov f f))
  rw [GaussianFields.map_scalarWhiteNoiseL2_eq_gaussianReal, hnorm]

end DOZZ

end
