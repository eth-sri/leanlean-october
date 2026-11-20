module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.DiskHarmonicModes
public import RequestProject.LocalConformalH1
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import RequestProject.NeumannHardyTraceInjective
public import RequestProject.PlanarNotation

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

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology

/-- Differentiating the actual CR identity on an open set and commuting
the mixed derivatives gives the classical Laplacian zero. -/
private theorem area_lap_eq_zero_of_CR {U : Set ℂ} (hU : IsOpen U)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hCR : ∀ z ∈ U, dirD φ Complex.I z = Complex.I * dirD φ 1 z)
    {z : ℂ} (hz : z ∈ U) : lap φ z = 0 := by
  have heq : dirD φ Complex.I =ᶠ[𝓝 z] fun w => Complex.I * dirD φ 1 w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hCR w hw
  have hd : DifferentiableAt ℝ (dirD φ 1) z :=
    ((hφ.fderiv_right (m := ∞) le_rfl).clm_apply
      contDiff_const).differentiable (by simp) z
  have hD (v : ℂ) :
      dirD (dirD φ Complex.I) v z = Complex.I * dirD (dirD φ 1) v z := by
    simpa only [dirD, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
        (heq.fderiv_eq.trans (fderiv_const_mul hd Complex.I))
  rw [lap, hD Complex.I, hardy_trace_dirD_comm hφ 1 Complex.I z, hD 1]
  ring_nf; simp

private theorem area_cutoff_dirD_disk {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F unitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) (v : ℂ) :
    dirD (smoothDiskCutoff R hR F) v z = deriv F z * v := by
  unfold dirD
  rw [fderiv_smoothDiskCutoff_eq hR F (ball_subset_closedBall hz),
    (hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

section

variable (Φ : SmoothDiskMap) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
    (hinj : InjOn Φ.map unitDisk)

include hhol in
theorem localConformal_cutoff_lap_eq_zero {z : ℂ} (hz : z ∈ unitDisk) :
    lap (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) z = 0 := by
  apply area_lap_eq_zero_of_CR isOpen_ball (contDiff_smoothDiskCutoff Φ.one_lt_radius Φ.smooth) _ hz
  intro w hw
  rw [area_cutoff_dirD_disk Φ.one_lt_radius Φ.map hhol hw Complex.I,
    area_cutoff_dirD_disk Φ.one_lt_radius Φ.map hhol hw 1, mul_one, mul_comm]

private theorem area_conj_mul_self (a : ℂ) : conj a * a = (‖a‖ ^ 2 : ℝ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

include hhol in
private theorem area_cutoff_gradient_density {z : ℂ} (hz : z ∈ unitDisk) :
    (∑ i : Fin 2, dirD (fun w => conj (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map w)) (coordDir i) z *
      dirD (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) (coordDir i) z) =
        ((2 * ‖deriv Φ.map z‖ ^ 2 : ℝ) : ℂ) := by
  have hφ := contDiff_smoothDiskCutoff Φ.one_lt_radius Φ.smooth
  simp only [Fin.sum_univ_two, show coordDir 0 = 1 from rfl,
    show coordDir 1 = Complex.I from rfl,
    dirD_conj (hφ.of_le (by simp))]
  rw [area_conj_mul_self, area_conj_mul_self,
    area_cutoff_dirD_disk Φ.one_lt_radius Φ.map hhol hz 1,
    area_cutoff_dirD_disk Φ.one_lt_radius Φ.map hhol hz Complex.I]
  simp [norm_mul, Complex.norm_I] <;> ring

/-- The ordinary area is exactly the genuine conformal Jacobian integral. -/
theorem localConformal_jacobian_integral_eq_volume (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) :
    (∫ z in unitDisk, ‖deriv F z‖ ^ 2) =
      (volume (F '' unitDisk)).toReal := by
  have hcv := localConformal_integral_image isOpen_ball hhol hinj (fun _ => 1)
  simpa [measureReal_def] using hcv.symm

include hhol in
private theorem area_cutoff_conormal (θ : ℝ) :
    fderiv ℝ (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) (unitCirclePt θ)
        (-(Complex.I * deriv unitCirclePt θ)) =
      -(Complex.I * deriv Φ.boundary θ) := by
  have hz := circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ
  rw [unitCircle_conormalDirection, fderiv_smoothDiskCutoff_eq Φ.one_lt_radius Φ.map hz,
    localConformal_fderiv_closedDisk Φ hhol hz,
    localConformal_circleTrace_deriv Φ hhol]
  ring_nf; simp

include hhol hinj in
/-- Disk Green applied to the actual compact cutoff gives the complex
boundary energy. All factors use ordinary area and angular measures. -/
theorem localConformal_disk_green_energy :
    doubleLayer unitCirclePt (fun θ => conj (Φ.boundary θ))
      (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) =
        ((2 * (volume Φ.domain).toReal : ℝ) : ℂ) := by
  have hφ := smoothDiskCutoff_testFunction Φ.one_lt_radius Φ.smooth
  have hV := hφ.conj
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  have htrace : ∀ θ ∈ angleInterval,
      conj (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map (unitCirclePt θ)) =
        conj (Φ.boundary θ) := by
    intro θ _
    exact congrArg conj (smoothDiskCutoff_eq_closedDisk Φ.one_lt_radius Φ.map
      (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1 htrace hφ.1
  calc
    _ = ∫ z in unitDisk,
        (conj (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map z) * lap (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) z +
          ∑ i : Fin 2,
            dirD (fun w => conj (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map w)) (coordDir i) z *
              dirD (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) (coordDir i) z) := hgreen
    _ = ∫ z in unitDisk, ((2 * ‖deriv Φ.map z‖ ^ 2 : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change conj (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map z) * lap (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) z +
        (∑ i : Fin 2, dirD (fun w => conj (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map w)) (coordDir i) z *
          dirD (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) (coordDir i) z) = ((2 * ‖deriv Φ.map z‖ ^ 2 : ℝ) : ℂ)
      rw [localConformal_cutoff_lap_eq_zero Φ hhol hz, mul_zero, zero_add]
      exact area_cutoff_gradient_density Φ hhol hz
    _ = ((2 * (∫ z in unitDisk, ‖deriv Φ.map z‖ ^ 2) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_const_mul]
    _ = _ := by rw [localConformal_jacobian_integral_eq_volume Φ.map hhol hinj]

include hhol hinj in
/-- The actual circle trace has the positive physical signed area. -/
theorem localConformal_circleTrace_signedArea :
    (∫ₚ θ,
      (conj (Φ.boundary θ) * deriv Φ.boundary θ).im) =
        2 * (volume Φ.domain).toReal := by
  have hγ := Φ.boundaryC1
  let G  := fun θ => conj (Φ.boundary θ) *
    (-(Complex.I * deriv Φ.boundary θ))
  have hi : IntervalIntegrable G volume 0 anglePeriod :=
    ((Complex.continuous_conj.comp hγ.continuous).mul
      ((continuous_const.mul hγ.continuous_deriv_one).neg)).intervalIntegrable _ _
  have hbd : doubleLayer unitCirclePt (fun θ => conj (Φ.boundary θ))
      (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) = ∫ₚ θ, G θ := by
    
    apply intervalIntegral.integral_congr
    intro θ _
    change conj (Φ.boundary θ) *
      fderiv ℝ (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) (unitCirclePt θ)
        (-(Complex.I * deriv unitCirclePt θ)) =
      conj (Φ.boundary θ) * (-(Complex.I * deriv Φ.boundary θ))
    rw [area_cutoff_conormal Φ hhol]
  have hre : (∫ₚ θ, G θ).re =
      ∫ₚ θ,
        (conj (Φ.boundary θ) * deriv Φ.boundary θ).im := by
    change Complex.reCLM (∫ₚ θ, G θ) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro θ _
    change (conj (Φ.boundary θ) *
      (-(Complex.I * deriv Φ.boundary θ))).re = _
    simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im] <;> ring
  have he := congrArg Complex.re (localConformal_disk_green_energy Φ hhol hinj)
  rw [hbd, hre, Complex.ofReal_re] at he
  exact he

/-- The exact normalized arclength map preserves the actual signed area. -/
theorem normalizedArcCurve_signedArea {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ anglePeriod) (hnz : ∀ θ, deriv γ θ ≠ 0) :
    (∫ₚ θ, signedAreaDensity (normalizedArcCurve hγ hper hnz) θ) =
      ∫ₚ θ, signedAreaDensity γ θ := by
  obtain ⟨c, hτ, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  obtain ⟨K, hK⟩ := hτ.lipschitz
  let e := normalizedArcOrderIso hγ hper hnz
  have he  := hK
  have hcomp : normalizedArcCurve hγ hper hnz ∘ e = γ :=
    funext fun θ => (normalizedArcCurve_factorization hγ hper hnz θ).symm
  have hchain := ae_deriv_comp (normalizedArcCurve_lipschitz hγ hper hnz) e.monotone he
  rw [hcomp] at hchain
  
  rw [(integral_comp_orderIso he (normalizedArcOrderIso_zero hγ hper hnz)
    (normalizedArcOrderIso_endpoint hγ hper hnz)
    (signedAreaDensity (normalizedArcCurve hγ hper hnz)))]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hchain] with θ hθ _
  have hpoint : normalizedArcCurve hγ hper hnz (e θ) = γ θ := congrFun hcomp θ
  simp only [signedAreaDensity]
  rw [hpoint, hθ, mul_left_comm, Complex.im_ofReal_mul]

include hhol in
/-- The constructed exact arclength curve is now a genuine positively
oriented physical boundary parameter, with all six fields proved. -/
theorem exists_localConformal_isBoundaryParam (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ diskSphere, fderiv ℝ Φ.map z 1 ≠ 0) (hL : IsLipschitzDomain Φ.domain) :
    ∃ (β : ℝ → ℂ) (c : ℝ),
      IsBoundaryParam Φ.domain β ∧
      IsC1TraceReparam (normalizedArcReparam Φ.boundary) c ∧
      ∀ θ, Φ.boundary θ = β (normalizedArcReparam Φ.boundary θ) := by
  have hγ := Φ.boundaryC1
  have hp := Φ.periodic_boundary
  have hv := localConformal_circleTrace_deriv_ne_zero Φ hhol hnz
  have him := localConformal_circleTrace_image_frontier Φ hinj hL.1.1
  obtain ⟨c, hc, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  refine ⟨normalizedArcCurve hγ hp hv, c, ?_, hc,
    normalizedArcCurve_factorization hγ hp hv⟩
  refine
    { lipschitz := ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩
      periodic := normalizedArcCurve_periodic hγ hp hv
      injOn := normalizedArcCurve_injOn hγ hp hv
        (physicalCircleTrace_injOn_of_closedDisk_inj Φ.map hinj)
      image := normalizedArcCurve_image_frontier hγ hp hv him
      const_speed := ⟨arcLen Φ.boundary anglePeriod / anglePeriod,
        div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos,
        Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)⟩
      area := ?_ }
  exact (normalizedArcCurve_signedArea hγ hp hv).trans
    (localConformal_circleTrace_signedArea Φ hhol (hinj.mono ball_subset_closedBall))

end

end PolyaNeumann

end
