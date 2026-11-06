/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.CovarianceAlgebra
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import GaussianFields

/-!
# DOZZ.GFF.RadialEnergy

Polar integration tools for the radial approximations of the equator measure.
-/

public section

open Real Set MeasureTheory MeasureTheory.Measure
open scoped Interval

namespace DOZZ

/-- A triangular radial profile concentrated in a shrinking annulus about the unit circle. -/
@[expose] noncomputable def annularProfile (n : ℕ) (r : ℝ) : ℝ :=
  max 0 (1 - ((n : ℝ) + 2) * |r - 1|)

theorem continuous_annularProfile n : Continuous (annularProfile n) := by
  unfold annularProfile
  fun_prop

theorem annularProfile_nonneg n r : 0 ≤ annularProfile n r :=
  le_max_left _ _

/-- The unnormalized radial annular density on the plane. -/
@[expose] noncomputable def annularProfileOnPlane (n : ℕ) (z : ℂ) : ℝ :=
  annularProfile n ‖z‖

theorem continuous_annularProfileOnPlane n :
    Continuous (annularProfileOnPlane n) :=
  (continuous_annularProfile n).comp continuous_norm

theorem support_annularProfileOnPlane_subset n :
    Function.support (annularProfileOnPlane n) ⊆ Metric.closedBall (0 : ℂ) 2 := by
  intro z hz
  have : 0 < 1 - ((n : ℝ) + 2) * |‖z‖ - 1| := by
    by_contra h
    exact (ne_of_gt (by exact lt_of_le_of_ne (annularProfile_nonneg n ‖z‖) (Ne.symm (by simpa [annularProfileOnPlane] using hz)))) (by simp [annularProfile, max_eq_left (le_of_not_gt h)])
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hnorm : ‖z‖ ≤ 2 := by
    have habs := abs_le.mp (le_of_lt (show |‖z‖ - 1| < 1 / ((n : ℝ) + 2) by rw [lt_div_iff₀ (show 0 < (n : ℝ) + 2 by positivity)]; nlinarith))
    linarith
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hnorm

theorem hasCompactSupport_annularProfileOnPlane n :
    HasCompactSupport (annularProfileOnPlane n) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 2)
    (support_annularProfileOnPlane_subset n)

/-- The total mass of the unnormalized annular profile. -/
@[expose] noncomputable def annularProfileMass (n : ℕ) : ℝ :=
  ∫ z : ℂ, annularProfileOnPlane n z

theorem integrable_annularProfileOnPlane n :
    Integrable (annularProfileOnPlane n) (volume : Measure ℂ) :=
  (continuous_annularProfileOnPlane n).integrable_of_hasCompactSupport
    (hasCompactSupport_annularProfileOnPlane n)

theorem annularProfileMass_pos n : 0 < annularProfileMass n := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (continuous_annularProfileOnPlane n)
    (integrable_annularProfileOnPlane n)
    (fun z => annularProfile_nonneg n ‖z‖)
    (by rw [(show annularProfileOnPlane n 1 = 1 by simp [annularProfileOnPlane, annularProfile])]; norm_num)

/-- A continuous compactly supported probability density in a shrinking annulus about the
unit circle. -/
@[expose] noncomputable def annularProbabilityDensity (n : ℕ) (z : ℂ) : ℝ :=
  (annularProfileMass n)⁻¹ * annularProfileOnPlane n z

theorem continuous_annularProbabilityDensity n :
    Continuous (annularProbabilityDensity n) := by
  exact continuous_const.mul (continuous_annularProfileOnPlane n)

theorem hasCompactSupport_annularProbabilityDensity n :
    HasCompactSupport (annularProbabilityDensity n) := by
  rw [(show annularProbabilityDensity n = (fun _ : ℂ => (annularProfileMass n)⁻¹) • annularProfileOnPlane n by funext z; simp [annularProbabilityDensity, smul_eq_mul])]
  exact (hasCompactSupport_annularProfileOnPlane n).smul_left
    (f := fun _ : ℂ => (annularProfileMass n)⁻¹)

theorem integrable_annularProbabilityDensity n :
    Integrable (annularProbabilityDensity n) (volume : Measure ℂ) :=
  (continuous_annularProbabilityDensity n).integrable_of_hasCompactSupport
    (hasCompactSupport_annularProbabilityDensity n)

theorem integral_annularProbabilityDensity n :
    ∫ z : ℂ, annularProbabilityDensity n z = 1 := by
  change ∫ z : ℂ, (annularProfileMass n)⁻¹ * annularProfileOnPlane n z = 1
  rw [integral_const_mul, annularProfileMass]
  exact inv_mul_cancel₀ (ne_of_gt (annularProfileMass_pos n))

/-- The normalized radial profile as a function of radius. -/
@[expose] noncomputable def annularProbabilityRadial (n : ℕ) (r : ℝ) : ℝ :=
  (annularProfileMass n)⁻¹ * annularProfile n r

theorem annularProbabilityDensity_eq_radial n z :
    annularProbabilityDensity n z = annularProbabilityRadial n ‖z‖ := rfl

/-- Every point in the support of the annular density has radius close to one. -/
theorem annularProbabilityDensity_radius_bound (n : ℕ) z
    (hz : annularProbabilityDensity n z ≠ 0) :
    |‖z‖ - 1| < 1 / ((n : ℝ) + 2) := by
  have : 0 < 1 - ((n : ℝ) + 2) * |‖z‖ - 1| := by
    by_contra h
    exact (ne_of_gt (lt_of_le_of_ne (annularProfile_nonneg n ‖z‖) (Ne.symm (by intro hzero; apply hz; simp [annularProbabilityDensity, annularProfileOnPlane, hzero])))) (by simp [annularProfile, max_eq_left (le_of_not_gt h)])
  rw [lt_div_iff₀ (show 0 < (n : ℝ) + 2 by positivity)]
  nlinarith

/-- The annular probability density transported to GaussianFields' `Vec 2`. -/
@[expose] noncomputable def annularProbabilityDensityVec (n : ℕ)
    (x : GaussianFields.Vec 2) : ℝ :=
  annularProbabilityDensity n (complexLinearEquivVecTwo.symm x)

theorem continuous_annularProbabilityDensityVec n :
    Continuous (annularProbabilityDensityVec n) :=
  (continuous_annularProbabilityDensity n).comp complexLinearEquivVecTwo.symm.continuous

theorem hasCompactSupport_annularProbabilityDensityVec n :
    HasCompactSupport (annularProbabilityDensityVec n) :=
  (hasCompactSupport_annularProbabilityDensity n).comp_homeomorph
    complexLinearEquivVecTwo.symm.toHomeomorph

theorem integrable_annularProbabilityDensityVec n :
    Integrable (annularProbabilityDensityVec n)
      (volume : Measure (GaussianFields.Vec 2)) :=
  (continuous_annularProbabilityDensityVec n).integrable_of_hasCompactSupport
    (hasCompactSupport_annularProbabilityDensityVec n)

theorem memLp_two_annularProbabilityDensityVec n :
    MemLp (annularProbabilityDensityVec n) 2
      (volume : Measure (GaussianFields.Vec 2)) :=
  (continuous_annularProbabilityDensityVec n).memLp_of_hasCompactSupport
    (hasCompactSupport_annularProbabilityDensityVec n)

theorem integral_annularProbabilityDensityVec n :
    ∫ x : GaussianFields.Vec 2, annularProbabilityDensityVec n x = 1 := by
  calc
    ∫ x : GaussianFields.Vec 2, annularProbabilityDensityVec n x =
        ∫ z : ℂ, annularProbabilityDensityVec n (complexToVecTwo z) := (volume_preserving_complexToVecTwo.integral_comp' (f := complexToVecTwo) (g := annularProbabilityDensityVec n)).symm
    _ = ∫ z : ℂ, annularProbabilityDensity n z := by
      congr 1
      funext z
      simp [annularProbabilityDensityVec, ← complexLinearEquivVecTwo_apply]
    _ = 1 := integral_annularProbabilityDensity n

/-- Center a DOZZ test density by the smooth annular probability density, producing an ABK
mean-zero test function. -/
@[expose] noncomputable def annularCenteredTestFn (f : TestFn) (n : ℕ) :
    GaussianFields.MeanZeroTestFunction 2 := by
  let ρ := annularProbabilityDensityVec n
  have hρc : HasCompactSupport (fun x : GaussianFields.Vec 2 => testMass f * ρ x) := by
    have hfun : (fun x : GaussianFields.Vec 2 => testMass f * ρ x) =
        (fun _ : GaussianFields.Vec 2 => testMass f) • ρ := by
      funext x
      simp [smul_eq_mul]
    rw [hfun]
    exact hasCompactSupport_annularProbabilityDensityVec n |>.smul_left
      (f := fun _ : GaussianFields.Vec 2 => testMass f)
  refine
    { toFun := fun x => testFnVec f x - testMass f * ρ x
      continuous := (continuous_testFnVec f).sub
        ((continuous_annularProbabilityDensityVec n).const_mul (testMass f))
      hasCompactSupport := (hasCompactSupport_testFnVec f).sub hρc
      integrable := (integrable_testFnVec f).sub
        ((integrable_annularProbabilityDensityVec n).const_mul (testMass f))
      memLp_two :=
        ((continuous_testFnVec f).memLp_of_hasCompactSupport (hasCompactSupport_testFnVec f)).sub
          ((memLp_two_annularProbabilityDensityVec n).const_mul (testMass f))
      integral_eq_zero := ?_ }
  dsimp [ρ]
  rw [integral_sub (integrable_testFnVec f)
      ((integrable_annularProbabilityDensityVec n).const_mul (testMass f)),
    integral_testFnVec, integral_const_mul, integral_annularProbabilityDensityVec]
  simp [testMass]

theorem testFnVec_eq_annularCenteredTestFn_add f n
    x :
    testFnVec f x = annularCenteredTestFn f n x +
      testMass f * annularProbabilityDensityVec n x := by
  simp [annularCenteredTestFn]

/-- A compactly supported function on `Vec 2` is supported in some Euclidean ball. -/
theorem exists_ball_of_hasCompactSupport {u : GaussianFields.Vec 2 → ℝ}
    (hu : HasCompactSupport u) :
    ∃ R : ℝ, 0 ≤ R ∧
      Function.support u ⊆ {x : GaussianFields.Vec 2 | GaussianFields.euclideanNorm x ≤ R} := by
  rcases hu.exists_pos_le_norm with ⟨r, hr, hvanish⟩
  refine ⟨2 * r, by positivity, ?_⟩
  intro x hx
  calc
    GaussianFields.euclideanNorm x ≤ (2 : ℝ) * ‖x‖ := by
      simpa using GaussianFields.euclideanNorm_le_card_mul_norm x
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left (by by_contra hnot; exact hx (hvanish x (le_of_not_ge hnot))) (by norm_num)

/-- Mean-zero centering of a continuous compactly supported function by a translated unit-mass
bump. -/
noncomputable def centeredCompactFunctionAt (u : GaussianFields.Vec 2 → ℝ)
    (hu : Continuous u) (huc : HasCompactSupport u) (a : GaussianFields.Vec 2) :
    GaussianFields.MeanZeroTestFunction 2 := by
  let m : ℝ := ∫ x : GaussianFields.Vec 2, u x
  let η := abkUnitMassBumpAt a
  have huI : Integrable u (volume : Measure (GaussianFields.Vec 2)) :=
    hu.integrable_of_hasCompactSupport huc
  have hηc : HasCompactSupport (fun x : GaussianFields.Vec 2 => m * η x) := by
    have hfun : (fun x : GaussianFields.Vec 2 => m * η x) =
        (fun _ : GaussianFields.Vec 2 => m) • η := by
      funext x
      simp [smul_eq_mul]
    rw [hfun]
    exact (hasCompactSupport_abkUnitMassBumpAt a).smul_left
      (f := fun _ : GaussianFields.Vec 2 => m)
  refine
    { toFun := fun x => u x - m * η x
      continuous := hu.sub ((continuous_abkUnitMassBumpAt a).const_mul m)
      hasCompactSupport := huc.sub hηc
      integrable := huI.sub ((integrable_abkUnitMassBumpAt a).const_mul m)
      memLp_two :=
        (hu.memLp_of_hasCompactSupport huc).sub
          ((memLp_two_abkUnitMassBumpAt a).const_mul m)
      integral_eq_zero := ?_ }
  dsimp [m, η]
  rw [integral_sub huI ((integrable_abkUnitMassBumpAt a).const_mul _), integral_const_mul,
    integral_abkUnitMassBumpAt]
  simp

/-- On a region disjoint from the translated centering bump, centered data agrees with the
original compactly supported function. -/
theorem centeredCompactFunctionAt_eq_of_bump_zero
    u (hu : Continuous u) huc
    a x (hη : abkUnitMassBumpAt a x = 0) :
    centeredCompactFunctionAt u hu huc a x = u x := by
  simp [centeredCompactFunctionAt, hη]

/-- The logarithmic kernel is integrable against any two continuous compactly supported
densities. Centering each one outside its support reduces this to the ABK mean-zero theorem. -/
theorem integrable_compactLogKernelPair (u v : GaussianFields.Vec 2 → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v) :
    Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        u p.1 * v p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2)
      ((volume : Measure (GaussianFields.Vec 2)).prod
        (volume : Measure (GaussianFields.Vec 2))) := by
  rcases exists_ball_of_hasCompactSupport huc with ⟨Ru, hRu, huball⟩
  rcases exists_ball_of_hasCompactSupport hvc with ⟨Rv, hRv, hvball⟩
  let R := max Ru Rv
  have hRuR : Ru ≤ R := le_max_left _ _
  have hRvR : Rv ≤ R := le_max_right _ _
  let a := GaussianFields.abkRadialPoint 2 (R + 2)
  have ha_norm : GaussianFields.euclideanNorm a = R + 2 := by
    rw [GaussianFields.euclideanNorm_abkRadialPoint (by norm_num : 0 < 2)]
    exact abs_of_nonneg (by linarith)
  have ha : R + 1 < GaussianFields.euclideanNorm a := by
    rw [ha_norm]
    linarith
  let ψ := centeredCompactFunctionAt u hu huc a
  let φ := centeredCompactFunctionAt v hv hvc a
  let S : Set (GaussianFields.Vec 2 × GaussianFields.Vec 2) :=
    {p | u p.1 ≠ 0 ∧ v p.2 ≠ 0}
  have hψeq {x : GaussianFields.Vec 2} (hx : u x ≠ 0) : ψ x = u x := by
    dsimp [ψ]
    exact centeredCompactFunctionAt_eq_of_bump_zero u hu huc a x
      (abkUnitMassBumpAt_eq_zero_of_norm_le x a ((huball (show x ∈ Function.support u by simpa [Function.mem_support] using hx)).trans hRuR) ha)
  have hφeq {y : GaussianFields.Vec 2} (hy : v y ≠ 0) : φ y = v y := by
    dsimp [φ]
    exact centeredCompactFunctionAt_eq_of_bump_zero v hv hvc a y
      (abkUnitMassBumpAt_eq_zero_of_norm_le y a ((hvball (show y ∈ Function.support v by simpa [Function.mem_support] using hy)).trans hRvR) ha)
  have heq :
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        u p.1 * v p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2) =
      S.indicator (fun p => ψ p.1 * φ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2) := by
    funext p
    by_cases hux : u p.1 ≠ 0
    · by_cases hvx : v p.2 ≠ 0
      · simp [S, hux, hvx, hψeq hux, hφeq hvx]
      · have hv0 : v p.2 = 0 := by simpa using hvx
        simp [S, hux, hv0]
    · have hu0 : u p.1 = 0 := by simpa using hux
      simp [S, hu0]
  rw [heq]
  exact (integrable_abkLogCovarianceKernel_integrand ψ φ).indicator (by change MeasurableSet ({x : GaussianFields.Vec 2 | u x ≠ 0} ×ˢ {x : GaussianFields.Vec 2 | v x ≠ 0}); exact ((MeasurableSet.singleton (0 : ℝ)).compl.preimage hu.measurable).prod ((MeasurableSet.singleton (0 : ℝ)).compl.preimage hv.measurable))



/-- The radial density induced by the planar annular probability density. -/
@[expose] noncomputable def annularRadiusLaw (n : ℕ) (r : ℝ) : ℝ :=
  2 * Real.pi * r * annularProbabilityRadial n r

/-- The radial law of the annular probability density has total mass one. -/
theorem integral_annularRadiusLaw n :
    ∫ r in Ioi (0 : ℝ), annularRadiusLaw n r = 1 := by
  have integral_annularProbabilityRadial (n : ℕ) : ∫ r in Ioi (0 : ℝ), r * annularProbabilityRadial n r = (2 * Real.pi)⁻¹ := by
    have integral_radial_function (h : ℝ → ℝ) : ∫ z : ℂ, h ‖z‖ = 2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * h r := by
      calc
        ∫ z : ℂ, h ‖z‖ =
            ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
              p.1 * h ‖Complex.polarCoord.symm p‖ := by
                calc
                  ∫ z : ℂ, h ‖z‖ =
                      ∫ p in Complex.polarCoord.target,
                        p.1 • h ‖Complex.polarCoord.symm p‖ :=
                      (Complex.integral_comp_polarCoord_symm
                        (fun z : ℂ => h ‖z‖)).symm
                  _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
                        p.1 * h ‖Complex.polarCoord.symm p‖ := by
                      rw [Complex.polarCoord_target]
                      simp only [smul_eq_mul]
        _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, p.1 * h p.1 := by
          apply setIntegral_congr_fun (Complex.polarCoord.open_target.measurableSet)
          intro p hp
          change p.1 * h ‖Complex.polarCoord.symm p‖ = p.1 * h p.1
          simp only [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
        _ = (∫ r in Ioi (0 : ℝ), r * h r) *
              ∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
                rw [← setIntegral_prod_mul, volume_eq_prod]
                simp_rw [mul_one]
        _ = 2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * h r := by
          simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ,
            Set.univ_inter, volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi)
              (by linarith [Real.pi_pos]), sub_neg_eq_add, ← two_mul, smul_eq_mul,
            mul_one, mul_comm]
    have hpolar := integral_radial_function (annularProbabilityRadial n)
    have hmass :
        ∫ z : ℂ, annularProbabilityRadial n ‖z‖ = 1 := by
      calc
        ∫ z : ℂ, annularProbabilityRadial n ‖z‖ =
            ∫ z : ℂ, annularProbabilityDensity n z := by
              apply integral_congr_ae
              filter_upwards with z
              exact (annularProbabilityDensity_eq_radial n z).symm
        _ = 1 := integral_annularProbabilityDensity n
    rw [hmass] at hpolar
    calc
      ∫ r in Ioi (0 : ℝ), r * annularProbabilityRadial n r =
          (2 * Real.pi)⁻¹ *
            (2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * annularProbabilityRadial n r) := by
              field_simp [(show 2 * Real.pi ≠ 0 by positivity)]
      _ = (2 * Real.pi)⁻¹ := by
        rw [← hpolar]
        ring
  calc
    ∫ r in Ioi (0 : ℝ), annularRadiusLaw n r =
        ∫ r in Ioi (0 : ℝ),
          (2 * Real.pi) * (r * annularProbabilityRadial n r) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro r hr
            simp only [annularRadiusLaw]
            ring
    _ = (2 * Real.pi) *
          ∫ r in Ioi (0 : ℝ), r * annularProbabilityRadial n r :=
        integral_const_mul (2 * Real.pi)
          (fun r => r * annularProbabilityRadial n r)
    _ = 1 := by
        rw [integral_annularProbabilityRadial]
        field_simp

/-- Any nonzero value of the triangular annular profile lies in its defining radial window. -/
theorem annularProfile_radius_bound (n : ℕ) r
    (hr : annularProfile n r ≠ 0) :
    |r - 1| < 1 / ((n : ℝ) + 2) := by
  have : 0 < 1 - ((n : ℝ) + 2) * |r - 1| := by
    simpa [annularProfile] using (lt_of_le_of_ne (annularProfile_nonneg n r) (Ne.symm hr))
  rw [lt_div_iff₀ (show 0 < (n : ℝ) + 2 by positivity)]
  nlinarith

/-- The radial law is continuous. -/
theorem continuous_annularRadiusLaw n : Continuous (annularRadiusLaw n) := by
  unfold annularRadiusLaw annularProbabilityRadial annularProfile
  fun_prop

/-- The radial law vanishes outside a fixed compact interval around radius one. -/
theorem support_annularRadiusLaw_subset n :
    Function.support (annularRadiusLaw n) ⊆ Set.Icc (1 / 2 : ℝ) (3 / 2) := by
  intro r hr
  have hradial : annularProbabilityRadial n r ≠ 0 := by
    intro hzero
    apply (by simpa [Function.mem_support] using hr)
    simp [annularRadiusLaw, hzero]
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast Nat.le_add_left 2 n)
  have habs := abs_le.mp (le_of_lt (annularProfile_radius_bound n r (by intro hzero; apply hradial; simp [annularProbabilityRadial, hzero])))
  constructor <;> linarith

/-- The radial law is compactly supported and integrable on the line. -/
theorem hasCompactSupport_annularRadiusLaw n :
    HasCompactSupport (annularRadiusLaw n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_annularRadiusLaw_subset n)

theorem integrable_annularRadiusLaw n :
    Integrable (annularRadiusLaw n) (volume : Measure ℝ) :=
  (continuous_annularRadiusLaw n).integrable_of_hasCompactSupport
    (hasCompactSupport_annularRadiusLaw n)

theorem integrable_annularRadiusLawOn n :
    Integrable (annularRadiusLaw n)
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) :=
  (integrable_annularRadiusLaw n).restrict


/-- The integral of a circle-parametrized function over the polar angle interval is its circle
average multiplied by the angle length. -/
theorem integral_circleAngle_eq_twoPi_mul_circleAverage (f : ℂ → ℝ) r :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      2 * Real.pi * Real.circleAverage f 0 r := by
  let g : ℝ → ℝ := fun θ => f (circleMap 0 r θ)
  have hset : (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
      ∫ θ in -Real.pi..Real.pi, g θ := by
    calc
      ∫ θ in Ioo (-Real.pi) Real.pi, g θ =
          ∫ θ in Ioc (-Real.pi) Real.pi, g θ := by
            apply setIntegral_congr_set
            exact Ioo_ae_eq_Ioc
      _ = ∫ θ in -Real.pi..Real.pi, g θ := by
        symm
        exact intervalIntegral.integral_of_le (by linarith [Real.pi_pos])
  have havg : Real.circleAverage f 0 r =
      (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, g θ := by
    calc
      Real.circleAverage f 0 r =
          (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g (θ + -Real.pi) := by
            rw [Real.circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-Real.pi),
              smul_eq_mul]
      _ = (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, g θ := by rw [(show (∫ θ in (0 : ℝ)..2 * Real.pi, g (θ + -Real.pi)) = ∫ θ in -Real.pi..Real.pi, g θ by rw [intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * Real.pi) (f := g) (-Real.pi)]; congr 1 <;> ring)]
  calc
    ∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ) =
        (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
          ∫ θ in -Real.pi..Real.pi, g θ) := by
            rw [hset]
            field_simp
    _ = 2 * Real.pi * Real.circleAverage f 0 r := by rw [← havg]


/-- The integrand after polar change of variables in the second coordinate. -/
@[expose] noncomputable def polarSecondIntegrand (F : ℂ × ℂ → ℝ)
    (p : ℂ × (ℝ × ℝ)) : ℝ :=
  p.2.1 * F (p.1, Complex.polarCoord.symm p.2)

/-- A product-integrable function remains integrable after polar change of variables in its
second complex coordinate, including the radial Jacobian. -/
theorem integrable_polarSecondIntegrand F
    (hFmeas : Measurable F)
    (hF : Integrable F ((volume : Measure ℂ).prod (volume : Measure ℂ))) :
    Integrable (polarSecondIntegrand F)
      ((volume : Measure ℂ).prod
        ((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)) := by
  have hmeas : Measurable (polarSecondIntegrand F) := by
    change Measurable (fun p : ℂ × (ℝ × ℝ) =>
      p.2.1 * F (p.1, Complex.polarCoord.symm p.2))
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hsection x :
      ∫⁻ p, ‖polarSecondIntegrand F (x, p)‖ₑ
          ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target) =
    ∫⁻ y : ℂ, ‖F (x, y)‖ₑ := by
    calc
      ∫⁻ p in Complex.polarCoord.target,
          ‖polarSecondIntegrand F (x, p)‖ₑ =
        ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * ‖F (x, Complex.polarCoord.symm p)‖ₑ := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem Complex.polarCoord.open_target.measurableSet]
              with p hp
            simp only [polarSecondIntegrand, enorm_mul,
              Real.enorm_eq_ofReal hp.1.le]
      _ = ∫⁻ y : ℂ, ‖F (x, y)‖ₑ := by
        exact Complex.lintegral_comp_polarCoord_symm
          (fun y => ‖F (x, y)‖ₑ)
  have hfinite :
      ∫⁻ q : ℂ × (ℝ × ℝ), ‖polarSecondIntegrand F q‖ₑ ∂((volume : Measure ℂ).prod ((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)) < ⊤ := by
    rw [lintegral_prod _ (hmeas.enorm.aemeasurable)]
    calc
      ∫⁻ x : ℂ, ∫⁻ p : ℝ × ℝ,
          ‖polarSecondIntegrand F (x, p)‖ₑ
            ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)
          ∂(volume : Measure ℂ) =
        ∫⁻ x : ℂ, ∫⁻ y : ℂ, ‖F (x, y)‖ₑ ∂(volume : Measure ℂ)
          ∂(volume : Measure ℂ) := by
            congr 1
            funext x
            exact hsection x
      _ = ∫⁻ q : ℂ × ℂ, ‖F q‖ₑ
            ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
            rw [lintegral_prod _ (hFmeas.enorm.aemeasurable)]
      _ < ⊤ := hF.hasFiniteIntegral
  exact ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).2 hfinite⟩


/-- Integrating a compact density against the logarithmic kernel of an annular radial density
reduces to the one-dimensional logarithmic potential of its radii. -/
theorem integral_logKernel_annular u (hu : Continuous u)
    (huc : HasCompactSupport u) n :
    Integrable (fun x : ℂ => u x *
        (∫ r in Ioi (0 : ℝ),
          annularRadiusLaw n r * Real.log (max r ‖x‖)))
        (volume : Measure ℂ) ∧
      (∫ q : ℂ × ℂ,
      u q.1 * annularProbabilityDensity n q.2 * (-Real.log ‖q.1 - q.2‖)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      -∫ x : ℂ, u x *
        (∫ r in Ioi (0 : ℝ), annularRadiusLaw n r * Real.log (max r ‖x‖))
        ∂(volume : Measure ℂ) := by
  have integral_polarSecondIntegrand F (hFmeas : Measurable F) (hF : Integrable F ((volume : Measure ℂ).prod (volume : Measure ℂ))) : (∫ q : ℂ × (ℝ × ℝ), polarSecondIntegrand F q ∂((volume : Measure ℂ).prod ((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target))) = ∫ q : ℂ × ℂ, F q ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    calc
      _ = ∫ x : ℂ, ∫ p : ℝ × ℝ, polarSecondIntegrand F (x, p)
            ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)
            ∂(volume : Measure ℂ) := integral_prod _ (integrable_polarSecondIntegrand F hFmeas hF)
      _ = ∫ x : ℂ, ∫ y : ℂ, F (x, y) ∂(volume : Measure ℂ)
            ∂(volume : Measure ℂ) := by
        congr 1
        funext x
        change ∫ p in Complex.polarCoord.target,
            p.1 * F (x, Complex.polarCoord.symm p) = _
        convert Complex.integral_comp_polarCoord_symm
          (fun y => F (x, y)) using 1
        simp only [smul_eq_mul]
        rfl
      _ = ∫ q : ℂ × ℂ, F q
            ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
        (integral_prod _ hF).symm
  have integral_polarAngle_log_distance x {r} (hr : 0 < r) : (∫ θ in Ioo (-Real.pi) Real.pi, Real.log ‖x - Complex.polarCoord.symm (r, θ)‖) = 2 * Real.pi * Real.log (max r ‖x‖) := by
    have circleAverage_log_distance_eq_log_max : Real.circleAverage (fun z => Real.log ‖z - x‖) 0 r = Real.log (max r ‖x‖) := by
      rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (ne_of_gt hr), Real.posLog_eq_log_max_one (by positivity : 0 ≤ r⁻¹ * ‖(0 : ℂ) - x‖), (show ‖(0 : ℂ) - x‖ = ‖x‖ by simp), ← Real.log_mul (ne_of_gt hr) (by positivity : max 1 (r⁻¹ * ‖x‖) ≠ 0)]
      congr 1
      rw [mul_max_of_nonneg 1 (r⁻¹ * ‖x‖) hr.le]
      simp only [mul_one]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul]
    have hpolar θ : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
      simp [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
    calc
      ∫ θ in Ioo (-Real.pi) Real.pi,
          Real.log ‖x - Complex.polarCoord.symm (r, θ)‖ =
        ∫ θ in Ioo (-Real.pi) Real.pi, Real.log ‖circleMap 0 r θ - x‖ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          change Real.log ‖x - Complex.polarCoord.symm (r, θ)‖ =
            Real.log ‖circleMap 0 r θ - x‖
          rw [hpolar θ, norm_sub_rev]
      _ = 2 * Real.pi *
            Real.circleAverage (fun z => Real.log ‖z - x‖) 0 r := by
          exact integral_circleAngle_eq_twoPi_mul_circleAverage
            (fun z => Real.log ‖z - x‖) r
      _ = 2 * Real.pi * Real.log (max r ‖x‖) := by
          rw [circleAverage_log_distance_eq_log_max]
  let uVec : GaussianFields.Vec 2 → ℝ := fun x =>
    u (complexLinearEquivVecTwo.symm x)
  let F : ℂ × ℂ → ℝ := fun q =>
    u q.1 * annularProbabilityDensity n q.2 *
      (-Real.log ‖q.1 - q.2‖)
  let FVec : GaussianFields.Vec 2 × GaussianFields.Vec 2 → ℝ := fun q =>
    uVec q.1 * annularProbabilityDensityVec n q.2 *
      GaussianFields.abkLogCovarianceKernel q.1 q.2
  have hnorm z w :
      GaussianFields.euclideanNorm (complexToVecTwo z - complexToVecTwo w) =
        ‖z - w‖ := by
    rw [← complexToVecTwo_sub]
    exact euclideanNorm_complexToVecTwo (z - w)
  have hcomp : F = FVec ∘ complexPairToVecTwo := by
    funext q
    rcases q with ⟨z, w⟩
    change u z * annularProbabilityDensity n w * (-Real.log ‖z - w‖) =
      uVec (complexToVecTwo z) * annularProbabilityDensityVec n (complexToVecTwo w) *
        GaussianFields.abkLogCovarianceKernel (complexToVecTwo z) (complexToVecTwo w)
    rw [show uVec (complexToVecTwo z) = u z by simp [uVec, (show complexLinearEquivVecTwo.symm (complexToVecTwo z) = z by rw [← complexLinearEquivVecTwo_apply]; simp)],
      show annularProbabilityDensityVec n (complexToVecTwo w) =
        annularProbabilityDensity n w by simp [annularProbabilityDensityVec, (show complexLinearEquivVecTwo.symm (complexToVecTwo w) = w by rw [← complexLinearEquivVecTwo_apply]; simp)],
      (show GaussianFields.abkLogCovarianceKernel (complexToVecTwo z) (complexToVecTwo w) = -Real.log ‖z - w‖ by rw [GaussianFields.abkLogCovarianceKernel]; exact congrArg (fun t : ℝ => -Real.log t) (hnorm z w))]
  have hF : Integrable F
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    exact (show Integrable (FVec ∘ complexPairToVecTwo) ((volume : Measure ℂ).prod (volume : Measure ℂ)) by simpa using volume_preserving_complexPairToVecTwo.integrable_comp_of_integrable (integrable_compactLogKernelPair uVec (annularProbabilityDensityVec n) (hu.comp complexLinearEquivVecTwo.symm.continuous) (continuous_annularProbabilityDensityVec n) (huc.comp_homeomorph complexLinearEquivVecTwo.symm.toHomeomorph) (hasCompactSupport_annularProbabilityDensityVec n))).congr (by
      filter_upwards with q
      exact (congrFun hcomp q).symm)
  have hFmeas : Measurable F := by
    have := (continuous_annularProbabilityDensity n).measurable
    change Measurable (fun q : ℂ × ℂ =>
      u q.1 * annularProbabilityDensity n q.2 * (-Real.log ‖q.1 - q.2‖))
    fun_prop
  have hpolar := integrable_polarSecondIntegrand F hFmeas hF
  have hsections := hpolar.prod_right_ae
  have hinner {x}
      (hx : Integrable (fun p => polarSecondIntegrand F (x, p))
        ((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)) :
      (∫ p : ℝ × ℝ, polarSecondIntegrand F (x, p)
        ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)) =
        -u x * ∫ r in Ioi (0 : ℝ),
          annularRadiusLaw n r * Real.log (max r ‖x‖) := by
    rw [(show (volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target = ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)) by rw [Complex.polarCoord_target, Measure.prod_restrict, volume_eq_prod])] at hx ⊢
    rw [integral_prod _ hx]
    calc
      _ = ∫ r in Ioi (0 : ℝ),
            -u x * (2 * Real.pi * r * annularProbabilityRadial n r) *
              Real.log (max r ‖x‖) := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            calc
              _ = ∫ θ in Ioo (-Real.pi) Real.pi,
                    -(u x * (r * annularProbabilityRadial n r)) *
                      Real.log ‖x - Complex.polarCoord.symm (r, θ)‖ := by
                    apply setIntegral_congr_fun measurableSet_Ioo
                    intro θ hθ
                    simp only [polarSecondIntegrand, F, annularProbabilityDensity_eq_radial,
                      Complex.norm_polarCoord_symm, abs_of_pos hr]
                    ring
              _ = -(u x * (r * annularProbabilityRadial n r)) *
                    ∫ θ in Ioo (-Real.pi) Real.pi,
                      Real.log ‖x - Complex.polarCoord.symm (r, θ)‖ := by
                    rw [integral_const_mul]
              _ = -u x * (2 * Real.pi * r * annularProbabilityRadial n r) *
                    Real.log (max r ‖x‖) := by
                    rw [integral_polarAngle_log_distance x hr]
                    ring
      _ = ∫ r in Ioi (0 : ℝ),
            (-u x) * (annularRadiusLaw n r * Real.log (max r ‖x‖)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro r hr
            simp only [annularRadiusLaw]
            ring
      _ = -u x * ∫ r in Ioi (0 : ℝ),
            annularRadiusLaw n r * Real.log (max r ‖x‖) := by
            rw [integral_const_mul]
  have houterEq :
      (fun x => ∫ p : ℝ × ℝ, polarSecondIntegrand F (x, p)
        ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)) =ᵐ[
          (volume : Measure ℂ)]
        (fun x => -(u x *
          ∫ r in Ioi (0 : ℝ),
            annularRadiusLaw n r * Real.log (max r ‖x‖))) := by
    filter_upwards [hsections] with x hx
    calc
      _ = -u x * ∫ r in Ioi (0 : ℝ),
            annularRadiusLaw n r * Real.log (max r ‖x‖) := hinner hx
      _ = -(u x * ∫ r in Ioi (0 : ℝ),
            annularRadiusLaw n r * Real.log (max r ‖x‖)) := by ring
  refine ⟨(by simpa using (hpolar.integral_prod_left.congr houterEq).neg), ?_⟩
  calc
    _ = ∫ q : ℂ × (ℝ × ℝ), polarSecondIntegrand F q
          ∂((volume : Measure ℂ).prod
            ((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)) :=
      (integral_polarSecondIntegrand F hFmeas hF).symm
    _ = ∫ x : ℂ, ∫ p : ℝ × ℝ, polarSecondIntegrand F (x, p)
          ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target)
          ∂(volume : Measure ℂ) := integral_prod _ hpolar
    _ = -∫ x : ℂ, u x *
          (∫ r in Ioi (0 : ℝ),
            annularRadiusLaw n r * Real.log (max r ‖x‖))
          ∂(volume : Measure ℂ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hsections] with x hx
      calc
        _ = -u x * ∫ r in Ioi (0 : ℝ),
              annularRadiusLaw n r * Real.log (max r ‖x‖) := hinner hx
        _ = -(u x * ∫ r in Ioi (0 : ℝ),
              annularRadiusLaw n r * Real.log (max r ‖x‖)) := by ring

end DOZZ

end
