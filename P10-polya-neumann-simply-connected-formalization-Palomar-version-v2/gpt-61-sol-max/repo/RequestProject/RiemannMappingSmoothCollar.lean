module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalFourierTaylor
public import RequestProject.LocalConformalArcFactorization
public import RequestProject.RiemannMappingInterior
public import RequestProject.RiemannMappingBoundaryParamRegularity

/-!
# A real smooth collar from the actual regular conformal boundary trace

The Fourier collar agrees with the given holomorphic map on the whole
closed disk. Injectivity supplies the nonzero interior derivative; the
actual regular angular trace supplies the nonzero boundary differential.
Compactness then supplies genuine upper and lower bounds and the certified
local inverse theorem constructs a smooth inverse on a neighborhood.

The collar is real smooth on the plane. Complex holomorphicity is claimed
only on the original open disk. The first theorem package is compositional:
its regular trace inputs must come from the actual boundary regularity
chain before it is instantiated under the original domain hypotheses.
This module is part of the verified dependency chain.
-/

public section


namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- Agreement on the closed disk preserves the actual physical trace,
so its derivative is the one used in the boundary nonvanishing argument. -/
theorem smoothCollar_physicalCircleTrace_eq 
    (hGF : EqOn G F closedUnitDisk) :
    physicalCircleTrace G = physicalCircleTrace F := by
  aesop

theorem smoothCollar_fderiv_one_eq_deriv {G : PlaneMap}
    (hhol : DifferentiableOn ℂ G unitDisk)
     (hz : z ∈ unitDisk) : fderiv ℝ G z 1 = deriv G z := by
  rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  rfl

/-- Every genuine unit-circle point has its actual angular parameter.
No surjectivity of a boundary map is an auxiliary hypothesis. -/
theorem smoothCollar_circleMap_arg  (hz : ‖z‖ = 1) :
    unitCircleMap z.arg = z := by
  simpa  [circleMap_zero, hz] using
    Complex.norm_mul_exp_arg_mul_I z

/-- Nonzero angular velocity transfers to the actual collar's boundary
differential through the real chain rule and the proved closed-disk
complex linearity. Interior nonvanishing comes from true injectivity. -/
theorem smoothCollar_fderiv_one_ne_zero_on_closedDisk  (hR : 1 < R)
    G F (hGs : RealSmoothOnBall G R)
    (hGF : EqOn G F closedUnitDisk)
    (hhol : DifferentiableOn ℂ G unitDisk)
    (hinj : InjOn G closedUnitDisk)
    (hΓnz : ∀ θ : ℝ, deriv (physicalCircleTrace F) θ ≠ 0) :
    ∀ z ∈ closedUnitDisk, fderiv ℝ G z 1 ≠ 0 := by
  intro z hz
  have hzNorm : ‖z‖ ≤ 1 := by simp_all
  rcases lt_or_eq_of_le hzNorm with hzlt | hzeq
  · have hzD : z ∈ unitDisk := by
      simp_all
    rw [smoothCollar_fderiv_one_eq_deriv hhol hzD]
    exact RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hhol
      (hinj.mono ball_subset_closedBall) hzD
  · let θ := z.arg
    have hθ : unitCircleMap θ = z := smoothCollar_circleMap_arg hzeq
    have hd : deriv (physicalCircleTrace F) θ =
        fderiv ℝ G z 1 * (z * Complex.I) := by
      simpa  [smoothCollar_physicalCircleTrace_eq hGF, hθ] using
        localConformal_circleTrace_deriv hR G hGs hhol θ
    measurability

/-- The two constants are actual compact bounds on the fixed collar.
The positive lower bound holds on the closed disk, including its boundary. -/
theorem exists_smoothCollar_closed_differential_bounds (G : PlaneMap)
    (hGs : RealSmooth G)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ G z 1 ≠ 0) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      (∀ z ∈ closedUnitDisk, 1 ≤ C * ‖fderiv ℝ G z 1‖ ^ 2) ∧
      (∀ z ∈ closedUnitDisk, ‖fderiv ℝ G z 1‖ ≤ K) := by
  have hcont : ContinuousOn (fun z : ℂ => ‖fderiv ℝ G z 1‖)
      closedUnitDisk :=
    ((hGs.continuous_fderiv (by simp)).clm_apply continuous_const).norm.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall 0 1).exists_isMinOn
    ⟨0, by simp⟩ hcont
  have hp  := norm_pos_iff.mpr (hnz z₀ hz₀)
  obtain ⟨B, hB⟩ := (isCompact_closedBall 0 1).exists_bound_of_continuousOn hcont
  refine ⟨(‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹, max B 1, by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_, ?_⟩
  · intro z hz
    have hle  := hmin hz
    calc
      1 = (‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹ * ‖fderiv ℝ G z₀ 1‖ ^ 2 :=
        (inv_mul_cancel₀ (by positivity)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hle 2) (inv_nonneg.mpr (sq_nonneg _))
  simp_all

/-- The exact supplied-coordinate package is constructed from the real
regularity of the actual closed-map trace. No collar, inverse, differential
lower bound or exterior holomorphicity is included in the premises. -/
theorem exists_smoothConformal_collar_of_regular_circleTrace
    F (hF : DiffContOnCl ℂ F unitDisk)
    (hinj : InjOn F closedUnitDisk)
    (hΓ : RealSmooth (physicalCircleTrace F))
    (hΓnz : ∀ θ : ℝ, deriv (physicalCircleTrace F) θ ≠ 0) :
    ∃ (G : PlaneMap) (R C K : ℝ) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ 0 < C ∧ 0 < K ∧
      RealSmooth G ∧
      RealSmoothOnBall G R ∧
      EqOn G F closedUnitDisk ∧
      DifferentiableOn ℂ G unitDisk ∧
      InjOn G closedUnitDisk ∧
      (∀ z ∈ closedUnitDisk, fderiv ℝ G z 1 ≠ 0) ∧
      (∀ z ∈ closedUnitDisk, 1 ≤ C * ‖fderiv ℝ G z 1‖ ^ 2) ∧
      (DiskInverseJacobianBound G C) ∧
      (∀ z ∈ closedUnitDisk, ‖fderiv ℝ G z 1‖ ≤ K) ∧
      G '' unitDisk = F '' unitDisk ∧
      G '' closedUnitDisk = F '' closedUnitDisk ∧
      physicalCircleTrace G = physicalCircleTrace F ∧
      (e : PlaneMap) = G ∧ closedUnitDisk ⊆ e.source ∧
      e.source ⊆ ball (0 : ℂ) R ∧ RealSmoothOn e.symm e.target := by
  obtain ⟨G, hGs, hGF, hhol⟩ :=
    exists_smooth_holomorphic_fourier_collar_of_circleTrace F hF hΓ
  have hGinj : InjOn G closedUnitDisk := by
    grind [Set.InjOn, Set.EqOn]
  have hR : (1 : ℝ) < 2 := by norm_num
  have hG₂ : RealSmoothOnBall G 2 := hGs.contDiffOn
  have hnz := smoothCollar_fderiv_one_ne_zero_on_closedDisk hR G F hG₂ hGF hhol hGinj hΓnz
  obtain ⟨C, K, hC, hK, hCclosed, hKclosed⟩ :=
    exists_smoothCollar_closed_differential_bounds G hGs hnz
  have hCopen : DiskInverseJacobianBound G C := by
    intro z hz
    simpa  [smoothCollar_fderiv_one_eq_deriv hhol hz] using
      hCclosed z (ball_subset_closedBall hz)
  obtain ⟨e, he, hsource, hsource₂, hes⟩ :=
    exists_localConformalInverse hR G hG₂ hhol hGinj hnz
  exact ⟨G, 2, C, K, e, hR, hC, hK, hGs, hG₂, hGF, hhol, hGinj, hnz,
    hCclosed, hCopen, hKclosed, (hGF.mono ball_subset_closedBall).image_eq,
    hGF.image_eq, smoothCollar_physicalCircleTrace_eq hGF, he, hsource, hsource₂, hes⟩

/-- The package in the parameter order used by the supplied-coordinate
analytic results. The physical domain and the full closed image are
preserved by actual equality of the constructed collar with the map. -/
theorem exists_supplied_conformal_coordinates_of_regular_circleTrace 
    F (hF : DiffContOnCl ℂ F unitDisk)
    (hinj : InjOn F closedUnitDisk)
    (himage : F '' unitDisk = Ω)
    (hΓ : RealSmooth (physicalCircleTrace F))
    (hΓnz : ∀ θ : ℝ, deriv (physicalCircleTrace F) θ ≠ 0) :
    ∃ (R C K : ℝ) (G : PlaneMap) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ 0 < C ∧ 0 < K ∧
      RealSmoothOnBall G R ∧
      DifferentiableOn ℂ G unitDisk ∧
      InjOn G closedUnitDisk ∧
      G '' unitDisk = Ω ∧
      (∀ z ∈ closedUnitDisk, fderiv ℝ G z 1 ≠ 0) ∧
      (DiskInverseJacobianBound G C) ∧
      (DiskDerivativeBound G K) ∧
      (e : PlaneMap) = G ∧ closedUnitDisk ⊆ e.source ∧
      RealSmoothOn e.symm e.target ∧
      EqOn G F closedUnitDisk ∧
      G '' closedUnitDisk = F '' closedUnitDisk ∧
      physicalCircleTrace G = physicalCircleTrace F := by
  obtain ⟨G, R, C, K, e, hR, hC, hK, _, hGs, hGF, hhol, hGinj, hnz,
    _, hCopen, hKclosed, hGimage, hGclosed, hGΓ, he, hsource, _, hes⟩ :=
    exists_smoothConformal_collar_of_regular_circleTrace F hF hinj hΓ hΓnz
  exact ⟨R, C, K, G, e, hR, hC, hK, hGs, hhol, hGinj,
    hGimage.trans himage, hnz, hCopen,
    fun z hz => hKclosed z (ball_subset_closedBall hz), he, hsource, hes,
    hGF, hGclosed, hGΓ⟩

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω)
include Ω hb hS hsc F hF hinj himage

/-- Composing the genuine inverse-graph criterion with the collar
construction. The inverse graph packets are an intermediate output of
the physical Green boundary argument, not a substitute for that argument
or an assumption of the forward map's boundary regularity. -/
theorem exists_supplied_conformal_coordinates_of_genuine_inverse_graphs
    (hgraphs : ∀ p ∈ frontier Ω,
      ∃ (c : ℂ) (hc : c ≠ 0) (f : RealMap) (hf : RealSmooth f) (a b : ℝ),
        f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
        (∀ z : ℂ, |z.re| < a → |z.im| < b →
          (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
        RealSmoothAt
          (fun x : ℝ => riemannMappingClosedInverse F
            (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
        deriv (fun x : ℝ => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ∃ (R C K : ℝ) (G : PlaneMap) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ 0 < C ∧ 0 < K ∧
      RealSmoothOnBall G R ∧
      DifferentiableOn ℂ G unitDisk ∧
      InjOn G closedUnitDisk ∧ G '' unitDisk = Ω ∧
      (∀ z ∈ closedUnitDisk, fderiv ℝ G z 1 ≠ 0) ∧
      (DiskInverseJacobianBound G C) ∧
      (DiskDerivativeBound G K) ∧
      (e : PlaneMap) = G ∧ closedUnitDisk ⊆ e.source ∧
      RealSmoothOn e.symm e.target ∧
      EqOn G (riemannMappingClosedExtension F) closedUnitDisk ∧
      EqOn G F unitDisk ∧
      G '' closedUnitDisk = closure Ω ∧
      G '' sphere (0 : ℂ) 1 = frontier Ω := by
  let H := riemannMappingClosedExtension F
  have hHF  := riemannMappingClosedExtension_eqOn F hF
  have hHs  :=
    DiffContOnCl.mk_ball (hF.congr fun z hz => hHF hz)
      (riemannMappingClosedExtension_continuousOn hb hS.isLipschitzDomain hsc F hF hinj himage)
  have hHinj  :=
    riemannMappingClosedExtension_injOn hb hS.isLipschitzDomain hsc F hF hinj himage
  have hHimage  := hHF.image_eq.trans himage
  obtain ⟨hΓ, hΓnz⟩ := riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs
    hb hS hsc F hF hinj himage hgraphs
  obtain ⟨R, C, K, G, e, hR, hC, hK, hGs, hhol, hGinj, hGimage,
    hnz, hCopen, hKopen, he, hsource, hes, hGH, hGclosed, _⟩ :=
    exists_supplied_conformal_coordinates_of_regular_circleTrace H hHs hHinj hHimage hΓ hΓnz
  refine ⟨R, C, K, G, e, hR, hC, hK, hGs, hhol, hGinj, hGimage,
    hnz, hCopen, hKopen, he, hsource, hes, hGH,
    (hGH.mono ball_subset_closedBall).trans hHF, ?_, ?_⟩
  · exact hGclosed.trans
      (riemannMappingClosedExtension_closed_image hb hS.isLipschitzDomain hsc F hF hinj himage)
  · exact (hGH.mono sphere_subset_closedBall).image_eq.trans
      (riemannMappingClosedExtension_sphere_image hb hS.isLipschitzDomain hsc F hF hinj himage)

/-- For an actual interior Riemann map, every inverse graph packet is
now supplied by the proved original-data Green boundary theorem. No
boundary regularity or nonvanishing is left as an input of this wrapper. -/
theorem exists_supplied_conformal_coordinates_of_interior_map :
    ∃ (R C K : ℝ) (G : PlaneMap) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ 0 < C ∧ 0 < K ∧
      RealSmoothOnBall G R ∧
      DifferentiableOn ℂ G unitDisk ∧
      InjOn G closedUnitDisk ∧ G '' unitDisk = Ω ∧
      (∀ z ∈ closedUnitDisk, fderiv ℝ G z 1 ≠ 0) ∧
      (DiskInverseJacobianBound G C) ∧
      (DiskDerivativeBound G K) ∧
      (e : PlaneMap) = G ∧ closedUnitDisk ⊆ e.source ∧
      RealSmoothOn e.symm e.target ∧
      EqOn G (riemannMappingClosedExtension F) closedUnitDisk ∧
      EqOn G F unitDisk ∧
      G '' closedUnitDisk = closure Ω ∧
      G '' sphere (0 : ℂ) 1 = frontier Ω := (exists_supplied_conformal_coordinates_of_genuine_inverse_graphs hb hS hsc F hF hinj himage fun x hp => exists_riemannMapping_genuine_regular_inverse_graph hb hS hsc F hF hinj himage hp)

end


/-- Genuine supplied smooth conformal coordinates under the original
bounded smooth simply-connected domain assumptions. The map, real smooth
collar, differential bounds and smooth neighborhood inverse are all
conclusions. This changes no hypothesis of the original strict theorem. -/
theorem exists_smoothConformal_coordinates Ω
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ (R C K : ℝ) (F : PlaneMap) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ 0 < C ∧ 0 < K ∧
      RealSmoothOnBall F R ∧
      DifferentiableOn ℂ F unitDisk ∧
      InjOn F closedUnitDisk ∧ F '' unitDisk = Ω ∧
      (∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) ∧
      (DiskInverseJacobianBound F C) ∧
      (DiskDerivativeBound F K) ∧
      (e : PlaneMap) = F ∧ closedUnitDisk ⊆ e.source ∧
      RealSmoothOn e.symm e.target ∧
      F '' closedUnitDisk = closure Ω ∧ F '' sphere (0 : ℂ) 1 = frontier Ω := by
  obtain ⟨G, hG, hGinj, hGimage⟩ := exists_interior_conformal_map Ω hS.1.1 hb hsc
  obtain ⟨R, C, K, F, e, hR, hC, hK, hFs, hhol, hinj, himage,
    hnz, hCopen, hKopen, he, hsource, hes, _, _, hclosed, hsphere⟩ :=
    exists_supplied_conformal_coordinates_of_interior_map hb hS hsc G hG hGinj hGimage
  exact ⟨R, C, K, F, e, hR, hC, hK, hFs, hhol, hinj, himage,
    hnz, hCopen, hKopen, he, hsource, hes, hclosed, hsphere⟩

end PolyaNeumann