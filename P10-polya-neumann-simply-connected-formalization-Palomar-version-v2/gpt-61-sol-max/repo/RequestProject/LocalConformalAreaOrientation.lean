module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.DiskHarmonicModes
public import RequestProject.LocalConformalH1
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Positive orientation of actual supplied conformal disk coordinates

The real Cauchy--Riemann identity and symmetry of mixed real derivatives
prove that the actual supplied map is harmonic inside the unit disk. A
genuine smooth compact cutoff agrees with that map near the closed disk.
Applying the proved disk Green identity to the cutoff and its conjugate
gives twice the conformal Jacobian integral. Actual change of variables
identifies this integral with the ordinary area of the open-disk image.

The unit-circle conormal is `-i` times the angular derivative, so the real
part of the Green boundary pairing is precisely the signed-area density.
This proves positive orientation without assuming a winding or area
identity. The exact normalized arclength change preserves that integral,
and the resulting curve satisfies all six actual `IsBoundaryParam` fields.
The existence of the initial supplied conformal map remains separate.
-/

public section

open scoped ContDiff



namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology

theorem common_area_dirD_comm 
    (hφ : RealSmooth φ) v w z :
    dirD (dirD φ v) w z = dirD (dirD φ w) v z := by
  have hd  :=
    (hφ.fderiv_right (m := ∞) le_rfl).differentiable (by simp) z
  have hv : fderiv ℝ (dirD φ v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ φ x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hw : fderiv ℝ (dirD φ w) z v = fderiv ℝ (fderiv ℝ φ) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ φ x w) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change fderiv ℝ (dirD φ v) z w = fderiv ℝ (dirD φ w) z v
  rw [hv, hw]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp_all)).eq w v

/-- Differentiating the actual CR identity on an open set and commuting
the mixed derivatives gives the classical Laplacian zero. -/
private theorem area_lap_eq_zero_of_CR  (hU : IsOpen U)
     (hφ : RealSmooth φ)
    (hCR : ∀ z ∈ U, dirD φ Complex.I z = Complex.I * dirD φ 1 z)
     (hz : z ∈ U) : lap φ z = 0 := by
  have heq : dirD φ Complex.I =ᶠ[𝓝 z] fun w => Complex.I * dirD φ 1 w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hCR w hw
  have hd : DifferentiableAt ℝ (dirD φ 1) z :=
    ((hφ.fderiv_right (m := ∞) le_rfl).clm_apply
      contDiff_const).differentiable (by simp) z
  have hD (v : ℂ) :
      dirD (dirD φ Complex.I) v z = Complex.I * dirD (dirD φ 1) v z := by
    simpa  [dirD] using
      congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
        (heq.fderiv_eq.trans (fderiv_const_mul hd Complex.I))
  rw [lap, hD Complex.I, common_area_dirD_comm hφ 1 Complex.I z, hD 1]
  ring_nf; simp only [Complex.I_sq]; ring

private theorem area_cutoff_dirD_disk  hR F
    (hhol : DifferentiableOn ℂ F unitDisk)
     (hz : z ∈ unitDisk) v :
    dirD (smoothDiskCutoff R hR F) v z = deriv F z * v := by
  unfold dirD
  rw [fderiv_smoothDiskCutoff_eq hR F (ball_subset_closedBall hz),
    (hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk)

include R hR F hFs hhol in
theorem localConformal_cutoff_lap_eq_zero
     (hz : z ∈ unitDisk) :
    lap (smoothDiskCutoff R hR F) z = 0 := by
  apply area_lap_eq_zero_of_CR isOpen_ball (contDiff_smoothDiskCutoff hR hFs) _ hz
  grind only [area_cutoff_dirD_disk]

private theorem area_conj_mul_self (a : ℂ) : conj a * a = (‖a‖ ^ 2 : ℝ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

include R hR F hFs hhol in
private theorem area_cutoff_gradient_density
     (hz : z ∈ unitDisk) :
    (∑ i : Coord, dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
      dirD (smoothDiskCutoff R hR F) (coordDir i) z) =
        ((2 * ‖deriv F z‖ ^ 2 : ℝ) : ℂ) := by
  have hφ := contDiff_smoothDiskCutoff hR hFs
  simp  [show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl, dirD_conj (hφ.of_le (by simp))]
  rw [area_conj_mul_self, area_conj_mul_self,
    area_cutoff_dirD_disk hR F hhol hz 1,
    area_cutoff_dirD_disk hR F hhol hz Complex.I]
  simp  
  push_cast
  ring

/-- The ordinary area is exactly the genuine conformal Jacobian integral. -/
theorem localConformal_jacobian_integral_eq_volume (F : PlaneMap)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) :
    (∫ z in unitDisk, ‖deriv F z‖ ^ 2) =
      (volume (F '' unitDisk)).toReal := by
  have hcv := localConformal_integral_image isOpen_ball hhol hinj (fun _ => 1)
  simpa  [measureReal_def] using hcv.symm

section
include R hR F hFs hhol

private theorem area_cutoff_conormal θ :
    fderiv ℝ (smoothDiskCutoff R hR F) (unitCircleMap θ)
        (-(Complex.I * deriv unitCircleMap θ)) =
      -(Complex.I * deriv (physicalCircleTrace F) θ) := by
  have hz := circleMap_mem_closedBall 0 (by norm_num : (0 : ℝ) ≤ 1) θ
  rw [unitCircle_conormalDirection, fderiv_smoothDiskCutoff_eq hR F hz,
    localConformal_fderiv_closedDisk hR F hFs hhol hz,
    localConformal_circleTrace_deriv hR F hFs hhol]
  ring_nf; simp only [Complex.I_sq]; ring

/-- Disk Green applied to the actual compact cutoff gives the complex
boundary energy. All factors use ordinary area and angular measures. -/
theorem localConformal_disk_green_energy
    (hinj : InjOn F unitDisk) :
    doubleLayer unitCircleMap (fun θ => conj (physicalCircleTrace F θ))
      (smoothDiskCutoff R hR F) =
        ((2 * (volume (F '' unitDisk)).toReal : ℝ) : ℂ) := by
  have hφ := smoothDiskCutoff_testFunction hR hFs
  have hV := hφ.conj
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  have htrace : ∀ θ ∈ boundaryInterval,
      conj (smoothDiskCutoff R hR F (unitCircleMap θ)) =
        conj (physicalCircleTrace F θ) := by
    intro θ _
    exact congrArg conj (smoothDiskCutoff_eq_closedDisk hR F
      (circleMap_mem_closedBall 0 (by norm_num) θ))
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1 htrace hφ.1
  calc
    _ = ∫ z in ball 0 1,
        (conj (smoothDiskCutoff R hR F z) * lap (smoothDiskCutoff R hR F) z +
          ∑ i : Coord,
            dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
              dirD (smoothDiskCutoff R hR F) (coordDir i) z) := hgreen
    _ = ∫ z in ball 0 1, ((2 * ‖deriv F z‖ ^ 2 : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      grind only [smoothDiskCutoff, lap, dirD, coordDir, localConformal_cutoff_lap_eq_zero, area_cutoff_gradient_density]
    _ = ((2 * (∫ z in unitDisk, ‖deriv F z‖ ^ 2) : ℝ)) := by
      rw [integral_complex_ofReal, integral_const_mul]
    _ = _ := by simp_all [localConformal_jacobian_integral_eq_volume]

/-- The actual circle trace has the positive physical signed area. -/
theorem localConformal_circleTrace_signedArea
    (hinj : InjOn F unitDisk) :
    (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ).im) =
        2 * (volume (F '' unitDisk)).toReal := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  let G  := fun θ => conj (physicalCircleTrace F θ) *
    (-(Complex.I * deriv (physicalCircleTrace F) θ))
  have hi : IntervalIntegrable G volume 0 circlePeriod :=
    ((Complex.continuous_conj.comp hγ.continuous).mul
      ((continuous_const.mul hγ.continuous_deriv_one).neg)).intervalIntegrable _ _
  have hbd : doubleLayer unitCircleMap (fun θ => conj (physicalCircleTrace F θ))
      (smoothDiskCutoff R hR F) = ∫ θ in (0 : ℝ)..circlePeriod, G θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    grind only [physicalCircleTrace, smoothDiskCutoff, area_cutoff_conormal, PolyaNeumann.physicalCircleTrace]
  have hre : (∫ θ in (0 : ℝ)..circlePeriod, G θ).re =
      ∫ θ in (0 : ℝ)..circlePeriod,
        (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ).im := by
    change Complex.reCLM (∫ θ in (0)..circlePeriod, G θ) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro θ _
    change (conj (physicalCircleTrace F θ) *
      (-(Complex.I * deriv (physicalCircleTrace F) θ))).re = _
    simp_all [physicalCircleTrace, PolyaNeumann.physicalCircleTrace] <;> ring
  have he := congrArg Complex.re (localConformal_disk_green_energy hR F hFs hhol hinj)
  simp_all

end


/-- The exact normalized arclength map preserves the actual signed area. -/
theorem normalizedArcCurve_signedArea  hγ
    hper (hnz : ∀ θ, deriv γ θ ≠ 0) :
    (∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity (normalizedArcCurve hγ hper hnz) θ) =
      ∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity γ θ := by
  obtain ⟨c, hτ, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  obtain ⟨K, hK⟩ := hτ.lipschitz
  let e := normalizedArcOrderIso hγ hper hnz
  have he  := hK
  have hcomp : normalizedArcCurve hγ hper hnz ∘ e = γ :=
    funext fun θ => (normalizedArcCurve_factorization hγ hper hnz θ).symm
  have hchain := ae_deriv_comp (normalizedArcCurve_lipschitz hγ hper hnz) e.monotone he
  rw [hcomp] at hchain
  have hcv := integral_comp_orderIso he (normalizedArcOrderIso_zero hγ hper hnz)
    (normalizedArcOrderIso_endpoint hγ hper hnz)
    (signedAreaDensity (normalizedArcCurve hγ hper hnz))
  rw [hcv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hchain] with θ hθ _
  have hpoint : normalizedArcCurve hγ hper hnz (e θ) = γ θ := congrFun hcomp θ
  simp only [signedAreaDensity]
  rw [hpoint, hθ, mul_left_comm, Complex.im_ofReal_mul]

include R hR F hFs hhol in
/-- The constructed exact arclength curve is now a genuine positively
oriented physical boundary parameter, with all six fields proved. -/
theorem exists_localConformal_isBoundaryParam
    (hinj : InjOn F closedUnitDisk)
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (hL : IsLipschitzDomain (F '' unitDisk)) :
    ∃ (β : ComplexCurve) (c : ℝ),
      IsBoundaryParam (F '' unitDisk) β ∧
      IsC1TraceReparam (normalizedArcReparam (physicalCircleTrace F)) c ∧
      ∀ θ, physicalCircleTrace F θ = β (normalizedArcReparam (physicalCircleTrace F) θ) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  have him := localConformal_circleTrace_image_frontier hR F hFs hinj hL.1.1
  obtain ⟨c, hc, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  refine ⟨normalizedArcCurve hγ hp hv, c, ?_, hc,
    normalizedArcCurve_factorization hγ hp hv⟩
  refine
    { lipschitz := ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩
      periodic := normalizedArcCurve_periodic hγ hp hv
      injOn := normalizedArcCurve_injOn hγ hp hv
        (physicalCircleTrace_injOn_of_closedDisk_inj F hinj)
      image := normalizedArcCurve_image_frontier hγ hp hv him
      const_speed := ⟨arcLen (physicalCircleTrace F) circlePeriod / circlePeriod,
        div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos,
        Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)⟩
      area := ?_ }
  exact (normalizedArcCurve_signedArea hγ hp hv).trans
    (localConformal_circleTrace_signedArea hR F hFs hhol (hinj.mono ball_subset_closedBall))

end


end PolyaNeumann
