module

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

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology ContDiff

variable {R : ℝ}

/-- Differentiating the actual CR identity on an open set and commuting
the mixed derivatives gives the classical Laplacian zero. -/
private theorem area_lap_eq_zero_of_CR  (hU : IsOpen U)
     (hφ : ContDiff ℝ ∞ φ)
    (hCR : ∀ z ∈ U, dirD φ Complex.I z = Complex.I * dirD φ 1 z)
     (hz : z ∈ U) : lap φ z = 0 := by
  have hd : DifferentiableAt ℝ (dirD φ 1) z :=
    ((hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply
      contDiff_const).differentiable (by simp) z
  have hD v :
      dirD (dirD φ Complex.I) v z = Complex.I * dirD (dirD φ 1) v z := by
    simpa [dirD] using
      congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
        ((show dirD φ Complex.I =ᶠ[𝓝 z] fun w => Complex.I * dirD φ 1 w by
          filter_upwards [hU.mem_nhds hz] with w hw
          exact hCR w hw).fderiv_eq.trans (fderiv_const_mul hd Complex.I))
  rw [lap, hD Complex.I, show dirD (dirD φ 1) Complex.I z = dirD (dirD φ Complex.I) 1 z by
    have hd :=
      (hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiable (by simp) z
    change fderiv ℝ (dirD φ 1) z Complex.I = fderiv ℝ (dirD φ Complex.I) z 1
    rw [(show fderiv ℝ (dirD φ 1) z Complex.I = fderiv ℝ (fderiv ℝ φ) z Complex.I 1 by
      change fderiv ℝ (fun x => fderiv ℝ φ x 1) z Complex.I = _
      rw [fderiv_clm_apply hd (differentiableAt_const _)]
      simp), show fderiv ℝ (dirD φ Complex.I) z 1 = fderiv ℝ (fderiv ℝ φ) z 1 Complex.I by
      change fderiv ℝ (fun x => fderiv ℝ φ x Complex.I) z 1 = _
      rw [fderiv_clm_apply hd (differentiableAt_const _)]
      simp]
    exact (hφ.contDiffAt.isSymmSndFDerivAt (by
      simpa using
        (WithTop.coe_le_coe.mpr le_top))).eq Complex.I 1, hD 1]
  ring_nf; simp only [Complex.I_sq]; ring

local notation "Φ0" => ball 0 1

private theorem area_cutoff_dirD_disk  hR F
    (hhol : DifferentiableOn ℂ F (Φ0))
     (hz : z ∈ Φ0) v :
    dirD (smoothDiskCutoff R hR F) v z = deriv F z * v := by
  unfold dirD
  rw [fderiv_smoothDiskCutoff_eq hR F (ball_subset_closedBall hz),
    (hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

private theorem area_conj_mul_self (a : ℂ) : conj a * a = (‖a‖ ^ 2 : ℝ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

local notation "Φ1" => circleMap 0 1

private theorem area_cutoff_conormal  hR F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (Φ0)) θ :
    fderiv ℝ (smoothDiskCutoff R hR F) (Φ1 θ)
        (-(Complex.I * deriv (Φ1) θ)) =
      -(Complex.I * deriv (physicalCircleTrace F) θ) := by
  have hz := circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ
  rw [unitCircle_conormalDirection, fderiv_smoothDiskCutoff_eq hR F hz,
    localConformal_fderiv_closedDisk hR F hFs hhol hz,
    localConformal_circleTrace_deriv hR F hFs hhol]
  ring_nf; simp only [Complex.I_sq]; ring

/-- The exact normalized arclength map preserves the actual signed area. -/
theorem normalizedArcCurve_signedArea {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    hper hnz :
    (∫ θ in 0..(2 * Real.pi), signedAreaDensity (normalizedArcCurve hγ hper hnz) θ) =
      ∫ θ in 0..(2 * Real.pi), signedAreaDensity γ θ := by
  obtain ⟨c, hτ, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  obtain ⟨K, hK⟩ := hτ.lipschitz
  let e := normalizedArcOrderIso hγ hper hnz
  have he : LipschitzWith K e := hK
  have hcomp : normalizedArcCurve hγ hper hnz ∘ e = γ :=
    funext fun θ => (normalizedArcCurve_factorization hγ hper hnz θ).symm
  have hchain := ae_deriv_comp (normalizedArcCurve_lipschitz hγ hper hnz) e.monotone he
  rw [hcomp] at hchain
  rw [integral_comp_orderIso he (normalizedArcOrderIso_zero hγ hper hnz) (normalizedArcOrderIso_endpoint hγ hper hnz) (signedAreaDensity (normalizedArcCurve hγ hper hnz))]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hchain] with θ hθ _
  have hpoint : normalizedArcCurve hγ hper hnz (e θ) = γ θ := congrFun hcomp θ
  simp only [signedAreaDensity]
  rw [hpoint, hθ, mul_left_comm, Complex.im_ofReal_mul]

/-- The constructed exact arclength curve is now a genuine positively
oriented physical boundary parameter, with all six fields proved. -/
theorem exists_localConformal_isBoundaryParam  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ sphere 0 1, fderiv ℝ F z 1 ≠ 0)
    (hL : IsLipschitzDomain (F '' Φ0)) :
    ∃ β c,
      IsBoundaryParam (F '' Φ0) β ∧
      IsC1TraceReparam (normalizedArcReparam (physicalCircleTrace F)) c ∧
      ∀ θ, physicalCircleTrace F θ = β (normalizedArcReparam (physicalCircleTrace F) θ) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨c, hc, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  refine ⟨normalizedArcCurve hγ hp hv, c, ?_, hc,
    normalizedArcCurve_factorization hγ hp hv⟩
  refine
    { lipschitz := ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩
      periodic := normalizedArcCurve_periodic hγ hp hv
      injOn := normalizedArcCurve_injOn hγ hp hv
        (physicalCircleTrace_injOn_of_closedDisk_inj F hinj)
      image := normalizedArcCurve_image_frontier hγ hp hv (localConformal_circleTrace_image_frontier hR F hFs hinj hL.1.1)
      const_speed := ⟨arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi),
        div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos,
        Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)⟩
      area := ?_ }
  exact (normalizedArcCurve_signedArea hγ hp hv).trans
    (by
      have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
      let G : ℝ → ℂ := fun θ => conj (physicalCircleTrace F θ) *
        (-(Complex.I * deriv (physicalCircleTrace F) θ))
      have hi : IntervalIntegrable G volume 0 (2 * Real.pi) :=
        ((Complex.continuous_conj.comp hγ.continuous).mul
          ((continuous_const.mul hγ.continuous_deriv_one).neg)).intervalIntegrable _ _
      have hre : (∫ θ in 0..(2 * Real.pi), G θ).re =
          ∫ θ in 0..(2 * Real.pi),
            (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ).im := by
        change Complex.reCLM (∫ θ in 0..(2 * Real.pi), G θ) = _
        rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
        apply intervalIntegral.integral_congr
        intro θ _
        change (conj (physicalCircleTrace F θ) *
          (-(Complex.I * deriv (physicalCircleTrace F) θ))).re = _
        rw [show conj (physicalCircleTrace F θ) *
            (-(Complex.I * deriv (physicalCircleTrace F) θ)) =
          -(Complex.I * (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ)) by ring]
        simp
      have he := congrArg Complex.re (show doubleLayer (Φ1) (fun θ => conj (physicalCircleTrace F θ)) (smoothDiskCutoff R hR F) = (2 * (volume (F '' Φ0)).toReal : ℝ) by
        have hφ := smoothDiskCutoff_testFunction hR hFs
        have hV := hφ.conj
        obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
        calc
          _ = _ := (doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam hK hV.2.1 (by
                      intro θ _
                      exact congrArg conj (smoothDiskCutoff_eq_closedDisk hR F
                        (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))) hφ.1)
          _ = _ := by
            apply setIntegral_congr_fun measurableSet_ball
            intro z hz
            change conj (smoothDiskCutoff R hR F z) * lap (smoothDiskCutoff R hR F) z +
              (∑ i : Fin 2, dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
                dirD (smoothDiskCutoff R hR F) (coordDir i) z) = (2 * ‖deriv F z‖ ^ 2 : ℝ)
            rw [show lap (smoothDiskCutoff R hR F) z = 0 by
              apply area_lap_eq_zero_of_CR isOpen_ball (contDiff_smoothDiskCutoff hR hFs) _ hz
              intro w hw
              rw [area_cutoff_dirD_disk hR F hhol hw Complex.I,
                area_cutoff_dirD_disk hR F hhol hw 1, mul_one, mul_comm], mul_zero, zero_add]
            exact (by
              simp [show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl, dirD_conj ((contDiff_smoothDiskCutoff hR hFs).of_le (by simp))]
              rw [area_conj_mul_self, area_conj_mul_self,
                area_cutoff_dirD_disk hR F hhol hz 1,
                area_cutoff_dirD_disk hR F hhol hz Complex.I]
              simp
              push_cast
              ring)
          _ = _ := by
            rw [integral_complex_ofReal, integral_const_mul]
          _ = _ := by rw [show (∫ z in Φ0, ‖deriv F z‖ ^ 2) = (volume (F '' Φ0)).toReal by
            simpa [setIntegral_const, measureReal_def] using (localConformal_integral_image isOpen_ball hhol (hinj.mono ball_subset_closedBall) (fun _ => 1)).symm])
      rw [show doubleLayer (Φ1) (fun θ => conj (physicalCircleTrace F θ)) (smoothDiskCutoff R hR F) = ∫ θ in 0..(2 * Real.pi), G θ by
        unfold doubleLayer
        apply intervalIntegral.integral_congr
        intro θ _
        change conj (physicalCircleTrace F θ) *
          fderiv ℝ (smoothDiskCutoff R hR F) (Φ1 θ)
            (-(Complex.I * deriv (Φ1) θ)) = _
        rw [area_cutoff_conormal hR F hFs hhol], hre, Complex.ofReal_re] at he
      exact he)

end PolyaNeumann

end
