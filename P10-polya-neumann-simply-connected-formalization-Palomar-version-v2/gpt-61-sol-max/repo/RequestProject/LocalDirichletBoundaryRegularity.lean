module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.RiemannMappingSmoothBoundary
public import RequestProject.ReconBasic
public import RequestProject.ChainRule
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The actual local Dirichlet problem for conformal boundary regularity

The constructed physical Green correction is reduced to zero physical
boundary values by subtracting its genuine smooth boundary datum. The
result is an actual H¹ vector, smooth in the open domain and continuous
on its closure. Its weak Poisson equation and smooth forcing are proved
from interior harmonicity, by localizing each compact test.

The actual smooth-domain graph constructs real smooth bi-Lipschitz
coordinates, preserves genuine H¹ energy, and gives true zero values
on a flat boundary interval. The graph differential gives the actual
elliptic energy form. Fubini and the endpoint FTC then prove that the
mass of a shrinking boundary strip, divided by its squared thickness,
tends to zero. This justifies the energy estimate needed for normal
cutoffs; it is not a boundary second-derivative theorem.

No boundary H² estimate, higher boundary regularity, or smooth conformal
collar is assumed or asserted by these initial construction lemmas.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff

/-- The project's coordinate Laplacian equals the genuine Euclidean
Laplacian at every point of twice continuous differentiability. -/
theorem lap_eq_euclidean_laplacian  
    (hf : ContDiffAt ℝ 2 f z) : lap f z = Laplacian.laplacian f z := by
  have hd  :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (v : ℂ) : dirD (dirD f v) v z = fderiv ℝ (fderiv ℝ f) z v v := by
    change fderiv ℝ (fun w => fderiv ℝ f w v) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp_all
  rw [lap, he, he, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp  [iteratedFDeriv_two_apply]

/-- A local equality transports both actual coordinate second
derivatives. No assumed differential equation is used. -/
theorem eventuallyEq_lap_eq   (hfg : f =ᶠ[𝓝 z] g) :
    lap f z = lap g z := by
  have hd (v : ℂ)  :=
    (hfg.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A v)
  have hdd (v : ℂ)  :=
    congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((hd v).fderiv_eq (𝕜 := ℝ))
  exact congrArg₂ (· + ·) (hdd 1) (hdd Complex.I)

theorem smooth_integral_dirD_mul_test  
    (hG : TestFunction univ G) (hφ : TestFunction U φ) i :
    (∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
  have hu := (hG.dirD (coordDir i)).memLp' 2 (μ := volume.restrict U)
  have hg (j : Coord) := ((hG.dirD (coordDir i)).dirD (coordDir j)).memLp' 2
    (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth (hG.dirD (coordDir i)).1 hu hg φ hφ i
  change (∫ z in U, (hu.toLp _) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hg i).toLp _) z * φ z) at hw
  have hl : (fun z => (hu.toLp _ : L2 U) z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]
  have hr : (fun z => ((hg i).toLp _ : L2 U) z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
    filter_upwards [(hg i).coeFn_toLp] with z hz
    rw [hz]
  rw [integral_congr_ae hl, integral_congr_ae hr] at hw
  exact hw

/-- The true weak Poisson identity for a function smooth only in the
open domain. The compact test is localized before integration by
parts, so no boundary derivatives or global second-derivative energy
are needed. -/
theorem local_smooth_gradient_test_eq_neg_lap  (hU : IsOpen U)
     (hv : RealSmoothOn v U) (hφ : TestFunction U φ) :
    (∫ z in U, ∑ i : Coord, dirD v (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, lap v z * φ z) := by
  obtain ⟨G, hG, hGv⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hv
  have hfirst (i : Coord) :
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) =
        (fun z => dirD v (coordDir i) z * dirD φ (coordDir i) z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD v (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i)) ((hGv z hz).fderiv_eq (𝕜 := ℝ))]
    · simp  [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
  have hsecond : (fun z => lap G z * φ z) = (fun z => lap v z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [eventuallyEq_lap_eq (hGv z hz)]
    · simp  [image_eq_zero_of_notMem_tsupport hz]
  have hint (i : Coord) :
      IntegrableOn (((dirD G (coordDir i) * dirD φ (coordDir i)))) U :=
    ((hG.dirD (coordDir i)).memLp' 2).integrable_mul ((hφ.dirD (coordDir i)).memLp' 2)
  have hxx : IntegrableOn (((dirD (dirD G 1) 1 * φ))) U :=
    (((hG.dirD 1).dirD 1).memLp' 2).integrable_mul (hφ.memLp' 2)
  have hyy : IntegrableOn (((dirD (dirD G Complex.I) Complex.I * φ))) U :=
    (((hG.dirD Complex.I).dirD Complex.I).memLp' 2).integrable_mul (hφ.memLp' 2)
  have hlap :
      (∫ z in U, lap G z * φ z) =
        (∫ z in U, dirD (dirD G 1) 1 z * φ z) +
          ∫ z in U, dirD (dirD G Complex.I) Complex.I z * φ z := by
    simp_rw [lap, add_mul]
    exact integral_add hxx hyy
  calc
    _ = ∫ z in U, ∑ i : Coord, dirD G (coordDir i) z * dirD φ (coordDir i) z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Finset.sum_congr rfl (fun i _ =>
        congrFun (hfirst i).symm z))
    _ = ∑ i : Coord, ∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z :=
      integral_finset_sum _ (fun i _ => hint i)
    _ = -(∫ z in U, lap G z * φ z) := by
      simp_rw [smooth_integral_dirD_mul_test hG hφ]
      simp_all [coordDir]
    _ = _ := by rw [hsecond]

/-- The real projection of a genuine globally smooth boundary datum
is itself a genuine globally smooth compactly supported datum. -/
def smoothTraceRealPart (b : smoothTraceTests) : smoothTraceTests := by
  let L  := Complex.ofRealCLM.comp Complex.reCLM
  refine ⟨fun z => ((b z).re), ?_⟩
  refine ⟨L.contDiff.comp b.property.1, ?_, subset_univ _⟩
  exact b.property.2.1.comp_left (show L 0 = 0 by simp [L])



/-- The actual physical Dirichlet remainder after subtracting the
constructed smooth real boundary datum. -/
def riemannMappingDirichletRemainder F (b : smoothTraceTests) z  :=
  (riemannMappingGreenCorrection F z : ℂ) - b z

theorem lap_sub_of_contDiffAt  
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    lap (fun w => f w - g w) z = lap f z - lap g z := by
  have heq : (fun w => f w - g w) = f + (-1 : ℝ) • g := by
    aesop
  have hadd : Laplacian.laplacian (f + (-1 : ℝ) • g) z =
      Laplacian.laplacian f z + Laplacian.laplacian ((-1 : ℝ) • g) z :=
    hf.laplacian_add (hg.const_smul (-1 : ℝ))
  have hsmul  := laplacian_smul (-1 : ℝ) hg
  rw [lap_eq_euclidean_laplacian (hf.sub hg), heq, hadd, hsmul,
    ← lap_eq_euclidean_laplacian hf, ← lap_eq_euclidean_laplacian hg]
  simp  [sub_eq_add_neg]

/-- The actual zero-boundary H¹ Poisson problem needed for boundary
regularity. Its function, smooth forcing, boundary values, H¹ vector,
and compact-test equation are derived from the constructed Green
correction. No zero-trace or boundary regularity premise is added. -/
theorem exists_riemannMapping_zero_boundary_poisson_problem 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω) :
    ∃ b : smoothTraceTests, ∃ u : NeumannH1 Ω,
      ContinuousOn (riemannMappingDirichletRemainder F b) (closure Ω) ∧
      RealSmoothOn (riemannMappingDirichletRemainder F b) Ω ∧
      (∀ z ∈ frontier Ω, riemannMappingDirichletRemainder F b z = 0) ∧
      (h1Value Ω u : PlaneMap) =ᵐ[volume.restrict Ω] riemannMappingDirichletRemainder F b ∧
      (∀ i : Coord, (h1Gradient Ω i u : PlaneMap) =ᵐ[volume.restrict Ω]
        dirD (riemannMappingDirichletRemainder F b) (coordDir i)) ∧
      (∀ z ∈ Ω, lap (riemannMappingDirichletRemainder F b) z = -lap (b : PlaneMap) z) ∧
      ∀ φ : PlaneMap, TestFunction Ω φ →
        (∫ z in Ω, ∑ i : Coord, dirD (riemannMappingDirichletRemainder F b) (coordDir i) z *
          dirD φ (coordDir i) z) = ∫ z in Ω, lap (b : PlaneMap) z * φ z := by
  obtain ⟨b₀, hbdata⟩ := exists_riemannMappingGreenCorrection_smooth_boundary_data
    hb hS hsc F hF hinj himage
  let b := smoothTraceRealPart b₀
  obtain ⟨u₀, hu₀, hgu₀⟩ := exists_riemannMappingGreenCorrectionH1 hb hS hsc F hF hinj himage
  let h  := fun z => (riemannMappingGreenCorrection F z : ℂ)
  have hharm  :=
    (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
      Complex.ofRealCLM
  have hs  := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hv : RealSmoothOn (riemannMappingDirichletRemainder F b) Ω :=
    hs.sub b.property.1.contDiffOn
  have hΔ (z : ℂ) (hz : z ∈ Ω) :
      lap (riemannMappingDirichletRemainder F b) z = -lap (b : PlaneMap) z := by
    have hh  := (hharm z hz).1
    have hb : ContDiffAt ℝ 2 (b : PlaneMap) z := b.property.1.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
    exact (lap_sub_of_contDiffAt hh hb).trans (by
      rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds]
      simp  )
  refine ⟨b, u₀ - smoothTraceH1 Ω b, ?_, hv, ?_, ?_, ?_, hΔ, ?_⟩
  · exact (Complex.ofRealCLM.continuous.comp_continuousOn
      (riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage)).sub
        b.property.1.continuous.continuousOn
  · intro z hz
    change (riemannMappingGreenCorrection F z) - ((b₀ z).re : ℂ) = 0
    rw [hbdata z hz, sub_self]
  · rw [map_sub]
    filter_upwards [Lp.coeFn_sub (h1Value Ω u₀) (h1Value Ω (smoothTraceH1 Ω b)), hu₀,
      (smoothTraceTests_memLp Ω b).coeFn_toLp] with z hz hu hbz
    rw [hz, Pi.sub_apply, hu, h1Value_smoothTraceH1, hbz]
    rfl
  · intro i
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (h1Gradient Ω i u₀)
      (h1Gradient Ω i (smoothTraceH1 Ω b)), hgu₀ i,
      (smoothTraceTests_memLp_deriv Ω b i).coeFn_toLp,
      ae_restrict_mem hS.1.1.measurableSet] with z hz hu hbz hzΩ
    have hd  :=
      ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn
        (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)
    have hc : fderiv ℝ h z =
        Complex.ofRealCLM.comp (fderiv ℝ (riemannMappingGreenCorrection F) z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) z = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hd,
        ContinuousLinearMap.fderiv]
    have hh : DifferentiableAt ℝ h z :=
      (hs.differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)
    rw [hz, Pi.sub_apply, hu, h1Gradient_smoothTraceH1, hbz]
    change _ = fderiv ℝ (h - (b : PlaneMap)) z (coordDir i)
    rw [fderiv_sub hh ((b.property.1.differentiable (by simp)) z), hc]
    rfl
  · intro φ hφ
    rw [local_smooth_gradient_test_eq_neg_lap hS.1.1 hv hφ]
    have hl : (fun z => lap (riemannMappingDirichletRemainder F b) z * φ z)
        =ᵐ[volume.restrict Ω] (fun z => -(lap (b : PlaneMap) z * φ z)) := by
      filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with z hz
      rw [hΔ z hz, neg_mul]
    rw [integral_congr_ae hl, integral_neg, neg_neg]

/-! ## Actual smooth graph coordinates -/

/-- The genuine graph shear. Its inverse subtracts the same graph
height, because the shear preserves the real coordinate. -/
def smoothDirichletGraphShear (f : RealMap) z  :=
  z + (f z.re : ℂ) * Complex.I

@[simp] theorem smoothDirichletGraphShear_re f z :
    (smoothDirichletGraphShear f z).re = z.re := by
  simp [smoothDirichletGraphShear]

@[simp] theorem smoothDirichletGraphShear_im f z :
    (smoothDirichletGraphShear f z).im = z.im + f z.re := by
  simp [smoothDirichletGraphShear]

/-- This is a global real homeomorphism, built from the supplied
continuous graph, rather than an assumed boundary coordinate map. -/
def smoothDirichletGraphShearHomeomorph (f : RealMap) (hf : Continuous f) : ℂ ≃ₜ ℂ where
  toFun := smoothDirichletGraphShear f
  invFun := fun z => z - (f z.re : ℂ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp 
  right_inv z := by
    apply Complex.ext <;> simp 
  continuous_toFun := continuous_id.add
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)
  continuous_invFun := continuous_id.sub
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)

section
variable (f : RealMap) (hf : Continuous f) (z : ℂ)
include f hf z

@[simp] theorem smoothDirichletGraphShearHomeomorph_symm_apply :
    (smoothDirichletGraphShearHomeomorph f hf).symm z =
      z - (f z.re : ℂ) * Complex.I := rfl

end


theorem smoothDirichletGraphShear_contDiff 
    (hf : RealSmooth f) :
    RealSmooth (smoothDirichletGraphShear f) :=
  contDiff_id.add ((Complex.ofRealCLM.contDiff.comp
    (hf.comp Complex.reCLM.contDiff)).mul contDiff_const)

section
variable {f : RealMap} {K } (hf : LipschitzWith K f)
include f K hf

theorem smoothDirichletGraphShear_lipschitz : LipschitzWith (K + 1) (smoothDirichletGraphShear f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp  [dist_eq_norm]
  have hfw : ‖((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ ≤ (K : ℝ) * ‖z - w‖ := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    have hre : ‖z.re - w.re‖ ≤ ‖z - w‖ := by
      simpa   using Complex.abs_re_le_norm (z - w)
    exact (hf.norm_sub_le z.re w.re).trans
      (mul_le_mul_of_nonneg_left hre K.coe_nonneg)
  calc
    ‖smoothDirichletGraphShear f z - smoothDirichletGraphShear f w‖ =
        ‖(z - w) + ((f z.re - f w.re : ℝ)) * Complex.I‖ := by
      simp  [smoothDirichletGraphShear]
      ring
    _ ≤ ‖z - w‖ + ‖((f z.re - f w.re : ℝ)) * Complex.I‖ := norm_add_le _ _
    _ ≤ ‖z - w‖ + K * ‖z - w‖ := add_le_add le_rfl hfw
    _ = (K + 1) * ‖z - w‖ := by ring

theorem smoothDirichletGraphShearHomeomorph_symm_lipschitz :
    LipschitzWith (K + 1) (smoothDirichletGraphShearHomeomorph f hf.continuous).symm := by
  have heq : (smoothDirichletGraphShearHomeomorph f hf.continuous).symm =
      smoothDirichletGraphShear (fun x => -f x) := by
    funext z
    simp  [smoothDirichletGraphShear, sub_eq_add_neg]
  rw [heq]
  exact smoothDirichletGraphShear_lipschitz hf.neg

end


/-- The graph shear followed by the actual rigid coordinates of the
smooth-domain chart. Only continuity of the supplied graph and a
nonzero rigid factor are required to construct this homeomorphism. -/
def smoothDirichletGraphChart p c hc f hf  :=
  (smoothDirichletGraphShearHomeomorph f hf).trans
    ((Homeomorph.mulRight₀ c hc).symm.trans (Homeomorph.addLeft p))

section
variable (p c : ℂ) (hc : c ≠ 0) (f : RealMap) (hf : Continuous f) (z : ℂ)
include p c hc f hf z

@[simp] theorem smoothDirichletGraphChart_apply :
    smoothDirichletGraphChart p c hc f hf z = p + smoothDirichletGraphShear f z / c := rfl

theorem smoothDirichletGraphChart_rotate :
    c * (smoothDirichletGraphChart p c hc f hf z - p) = smoothDirichletGraphShear f z := by
  grind only [smoothDirichletGraphChart_apply]

end


theorem smoothDirichletGraphChart_contDiff p c hc
     (hf : RealSmooth f) :
    RealSmooth (smoothDirichletGraphChart p c hc f hf.continuous) :=
  contDiff_const.add ((smoothDirichletGraphShear_contDiff hf).div_const c)

section
variable (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1) {f : RealMap} {K } (hf : LipschitzWith K f)
include p c hc hc₁ f K hf

theorem smoothDirichletGraphChart_lipschitz :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have heq : smoothDirichletGraphChart p c hc f hf.continuous z -
      smoothDirichletGraphChart p c hc f hf.continuous w =
      (smoothDirichletGraphShear f z - smoothDirichletGraphShear f w) / c := by
    simp  
    ring
  simpa only [dist_eq_norm, heq, norm_div, hc₁, div_one] using
    (smoothDirichletGraphShear_lipschitz hf).dist_le_mul z w

theorem smoothDirichletGraphChart_symm_lipschitz :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + z) * c))
    ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + w) * c)) ≤ _
  have hs := (smoothDirichletGraphShearHomeomorph_symm_lipschitz hf).dist_le_mul
    ((-p + z) * c) ((-p + w) * c)
  have heq : (-p + z) * c - (-p + w) * c = (z - w) * c := by ring
  simpa  [dist_eq_norm, heq, hc₁] using hs

end


/-- The smooth-domain definition supplies an actual flattened full
rectangle on which physical membership is exactly positive height.
The homeomorphism is built above from that domain's own graph. -/
theorem exists_smoothDomain_flattening_rectangle  (hS : IsSmoothDomain Ω)
     (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : RealMap) (hf : RealSmooth f)
      (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      ∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im) := by
  obtain ⟨c, r, h, K, f, hc₁, hr, hh, hf, hLip, hf₀, _, hchart⟩ := hS.2 p hp
  have hc : c ≠ 0 := by
    measurability
  let a := min r (h / (4 * (K + 1)))
  let b := h / 4
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  have ha  := lt_min hr (div_pos hh hden)
  have hb : 0 < b := div_pos hh (by norm_num)
  refine ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb, ?_⟩
  intro z hzre hzim
  have hzrer  := hzre.trans_le (min_le_left _ _)
  have hscale : 4 * ((K : ℝ) + 1) * |z.re| < h := by
    simpa only [mul_comm] using
      (lt_div_iff₀ hden).mp (hzre.trans_le (min_le_right _ _))
  have hfz : |f z.re| ≤ (K : ℝ) * |z.re| := by
    simpa only [hf₀, sub_zero, Real.norm_eq_abs] using hLip.norm_sub_le z.re 0
  have hfzh : |f z.re| < h / 4 := by
    nlinarith [abs_nonneg z.re]
  have hy : |z.im + f z.re| < h := by
    grind
  grind only [smoothDirichletGraphChart, smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re, smoothDirichletGraphShear_im]

section
variable {Ω } (hΩ : IsOpen Ω) (p c ) (hc ) (f ) (hf ) {a b } (hb : 0 < b) (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
include Ω hΩ p c hc f hf a b hb hchart

/-- The bottom edge in an actual flattening rectangle maps to the
physical frontier. This follows from positive-height approach and
the local membership equivalence; frontier membership is not a new
coordinate premise. -/
theorem smoothDirichletGraphChart_mem_frontier
     (hx : |x| < a) :
    smoothDirichletGraphChart p c hc f hf (x : ℂ) ∈ frontier Ω := by
  let Ψ := smoothDirichletGraphChart p c hc f hf
  have hnot : Ψ (x : ℂ) ∉ Ω := by
    aesop
  have hcurve : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have h : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x : ℂ) + (0 : ℂ) * Complex.I)) :=
      (tendsto_const_nhds.add
        ((Complex.ofRealCLM.continuous.tendsto 0).mul_const Complex.I)).mono_left
          nhdsWithin_le_nhds
    simp_all
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Ψ ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Ω := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
    have ht₀  := ht
    apply (hchart _ (by simpa using hx) (by simpa [abs_of_pos ht₀] using htb)).mpr
    simpa using ht₀
  rw [hΩ.frontier_eq]
  exact ⟨mem_closure_of_tendsto ((Ψ.continuous.tendsto x).comp hcurve) hmem, hnot⟩

/-- True zero boundary values of a physical continuous solution
remain true zero values on the flattened boundary interval. -/
theorem smoothDirichletGraphChart_zero_boundary
    (v : PlaneMap) (hv : ∀ z ∈ frontier Ω, v z = 0)  (hx : |x| < a) :
    v (smoothDirichletGraphChart p c hc f hf (x : ℂ)) = 0 :=
  hv _ (smoothDirichletGraphChart_mem_frontier hΩ p c hc f hf hb hchart hx)

end


/-- An actual pointwise H¹ function remains pointwise H¹ under the
constructed graph coordinates. This uses the proved bi-Lipschitz
L² pullback and actual chain differential, with no assumed pullback
energy or flattened Sobolev regularity. -/
theorem smoothDirichletGraphChart_pullback_memLp 
    (hΩ : IsOpen Ω) (hU : IsOpen U) p c hc (hc₁ : ‖c‖ = 1)
     (hf : RealSmooth f)  (hLip : LipschitzWith K f)
    (himage : smoothDirichletGraphChart p c hc f hf.continuous '' U ⊆ Ω)
     (hv : RealSmoothOn v Ω)
    (hm : MemLp v 2 (volume.restrict Ω))
    (hg : ∀ i : Coord, MemLp (dirD v (coordDir i)) 2 (volume.restrict Ω)) :
    MemLp (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) 2
      (volume.restrict U) ∧
    ∀ i : Coord, MemLp
      (dirD (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) (coordDir i))
      2 (volume.restrict U) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  have hK : 0 < K + 1 := by positivity
  have hΨ : LipschitzOnWith (K + 1) Ψ U :=
    (smoothDirichletGraphChart_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hΨinv : LipschitzOnWith (K + 1) Ψ.symm (Ψ '' U) :=
    (smoothDirichletGraphChart_symm_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hm'  :=
    hm.mono_measure (Measure.restrict_mono_set volume himage)
  have hg' (i : Coord)  :=
    (hg i).mono_measure (Measure.restrict_mono_set volume himage)
  refine ⟨memLp_comp_bilip' hU hK hΨ hΨinv hm', ?_⟩
  intro i
  let G  := fun j => (hg' j).toLp _
  have hmc := memLp_chainGrad hU hK hΨ hΨinv G i
  have hae : ∀ᵐ z ∂(volume.restrict U), ∀ j : Coord,
      G j (Ψ z) = dirD v (coordDir j) (Ψ z) :=
    ae_all_iff.mpr (fun j => (quasiMeasurePreserving_restrict hΨinv).ae (hg' j).coeFn_toLp)
  apply hmc.ae_eq
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with z hz hzU
  have hzΩ  := himage (mem_image_of_mem Ψ hzU)
  have hdv := (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hzΩ)
  have hdΨ := ((smoothDirichletGraphChart_contDiff p c hc hf).differentiable (by simp)) z
  change chainGrad Ψ (fun j => (G j)) i z =
    fderiv ℝ (v ∘ Ψ) z (coordDir i)
  rw [fderiv_comp z hdv hdΨ, ContinuousLinearMap.comp_apply, clm_apply_eq_sum_coordRe]
  simp  [chainGrad, hz, dirD]

def smoothDirichletHalfBox (a b : ℝ) : PlanarSet :=
  {z | |z.re| < a ∧ 0 < z.im ∧ z.im < b}

def smoothDirichletClosedHalfBox (a b : ℝ) : PlanarSet :=
  {z | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b}

theorem isOpen_smoothDirichletHalfBox a b : IsOpen (smoothDirichletHalfBox a b) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-! ## The actual elliptic coefficients of graph flattening -/

/-- The actual differential of the graph shear at graph slope `d`.
It maps `(x,y)` to `(x,y+d*x)`. -/
def smoothDirichletGraphDifferential (d : ℝ)  :=
  ContinuousLinearMap.id ℝ ℂ + (d • Complex.reCLM).smulRight Complex.I

theorem smoothDirichletGraphShear_hasFDerivAt  
    (hf : DifferentiableAt ℝ f z.re) :
    HasFDerivAt (smoothDirichletGraphShear f)
      (smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hd := hf.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have hs := (hasFDerivAt_id z).add (hd.smul_const Complex.I)
  assumption

section
variable (p c : ℂ) (hc : c ≠ 0) {f : RealMap} (hf : RealSmooth f)
local notation "graphChartFixed" => smoothDirichletGraphChart p c hc f

include p c hc f hf

theorem smoothDirichletGraphChart_hasFDerivAt z :
    HasFDerivAt (graphChartFixed hf.continuous)
      (c⁻¹ • smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hd := smoothDirichletGraphShear_hasFDerivAt ((hf.differentiable (by simp)) z.re)
  have hs := (hd.mul_const c⁻¹).const_add p
  assumption

theorem smoothDirichletGraphChart_fderiv_apply z w :
    fderiv ℝ (graphChartFixed hf.continuous) z w =
      c⁻¹ * (w + (deriv f z.re * w.re) • Complex.I) := by
  rw [(smoothDirichletGraphChart_hasFDerivAt p c hc hf z).fderiv]
  rfl

/-- The actual chain rule exposes the inverse-graph energy
components. The physical derivatives occur in the rigid directions
`1/c` and `I/c`; the tangential shear term cancels exactly. -/
theorem smoothDirichletGraphChart_pullback_gradient  
    (hv : DifferentiableAt ℝ v (graphChartFixed hf.continuous z)) :
    (let Ψ := graphChartFixed hf.continuous
     let u := v ∘ Ψ
     dirD u 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD u Complex.I z = fderiv ℝ v (Ψ z) (1 / c)) ∧
    dirD (v ∘ graphChartFixed hf.continuous) Complex.I z =
      fderiv ℝ v (graphChartFixed hf.continuous z) (Complex.I / c) := by
  let Ψ := graphChartFixed hf.continuous
  let T := fderiv ℝ v (Ψ z)
  let d := deriv f z.re
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hchain (w : ℂ) : dirD (v ∘ Ψ) w z = T (c⁻¹ * (w + (d * w.re) • Complex.I)) := by
    change fderiv ℝ (v ∘ Ψ) z w = _
    rw [fderiv_comp z hv hdΨ, ContinuousLinearMap.comp_apply,
      smoothDirichletGraphChart_fderiv_apply p c hc hf z w]
  have hI : dirD (v ∘ Ψ) Complex.I z = T (Complex.I / c) := by
    rw [hchain]
    simp  [div_eq_mul_inv, mul_comm]
  have h1 : dirD (v ∘ Ψ) 1 z = T (1 / c) + d • T (Complex.I / c) := by
    rw [hchain]
    have he : c⁻¹ * ((1 : ℂ) + (d * (1 : ℂ).re) • Complex.I) =
        (1 / c : ℂ) + d • (Complex.I / c) := by
      simp  
      ring
    rw [he, map_add, map_smul]
  measurability

end


/-- The energy form of the inverse graph differential. Its matrix is
`[[1, -d], [-d, 1+d²]]`, with `d = f′(x)`. -/
def smoothDirichletGraphQuadratic (d x y : ℝ)  :=
  x ^ 2 - 2 * d * x * y + (1 + d ^ 2) * y ^ 2

theorem smoothDirichletGraphQuadratic_eq_sq d x y :
    smoothDirichletGraphQuadratic d x y = (x - d * y) ^ 2 + y ^ 2 := by
  unfold smoothDirichletGraphQuadratic
  ring

section
variable {f : RealMap} {K } (hf : LipschitzWith K f)
include f K hf

/-- Genuine ellipticity follows from the actual Lipschitz graph
bound; no elliptic coefficient premise is substituted for it. -/
theorem smoothDirichletGraphQuadratic_bounds t x y :
    (x ^ 2 + y ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      smoothDirichletGraphQuadratic (deriv f t) x y ∧
    smoothDirichletGraphQuadratic (deriv f t) x y ≤
      2 * (1 + (K : ℝ) ^ 2) * (x ^ 2 + y ^ 2) := by
  let d := deriv f t
  have hd : |d| ≤ (K : ℝ) := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hf (x₀ := t)
  have hd₂ : d ^ 2 ≤ (K : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg d) K.coe_nonneg).mpr hd
    simpa only [sq_abs] using hs
  have hq : 0 ≤ (x - d * y) ^ 2 + y ^ 2 := by positivity
  have hden : 0 < 2 * (1 + (K : ℝ) ^ 2) := by positivity
  have hlow : x ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * ((x - d * y) ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * d * y), sq_nonneg y,
      mul_nonneg (sq_nonneg d) (sq_nonneg (x - d * y))]
  have hupp : (x - d * y) ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x + d * y),
      mul_nonneg (sq_nonneg d) (sq_nonneg x), sq_nonneg y]
  change (x ^ 2 + y ^ 2) / (2 * (1 + K ^ 2)) ≤
      smoothDirichletGraphQuadratic d x y ∧
    smoothDirichletGraphQuadratic d x y ≤ 2 * (1 + K ^ 2) * (x ^ 2 + y ^ 2)
  rw [smoothDirichletGraphQuadratic_eq_sq]
  constructor
  · apply (div_le_iff₀ hden).mpr
    nlinarith
  nlinarith

/-- The same genuine elliptic bounds hold for complex-valued
solutions, by applying the real coefficient form to the actual real
and imaginary components. -/
theorem smoothDirichletGraph_complex_energy_bounds (t : ℝ) (x y : ℂ) :
    (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ∧
    ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ≤
      2 * (1 + (K : ℝ) ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hr₁, hr₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.re y.re
  obtain ⟨hi₁, hi₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.im y.im
  have heq : ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 =
      smoothDirichletGraphQuadratic (deriv f t) x.re y.re +
        smoothDirichletGraphQuadratic (deriv f t) x.im y.im := by
    simp  [Complex.sq_norm, Complex.normSq_apply, smoothDirichletGraphQuadratic]
    ring
  rw [heq]
  constructor
  · have h := add_le_add hr₁ hi₁
    convert h using 1
    simp  [Complex.sq_norm, Complex.normSq_apply]
    ring
  · have h := add_le_add hr₂ hi₂
    convert h using 1
    simp  [Complex.sq_norm, Complex.normSq_apply]
    ring

end


/-! ## The genuine one-dimensional zero-boundary energy step -/

section
variable {b } {v dv : ComplexCurve} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0) (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t) (hm : MemLp dv 2 (volume.restrict (Ioc 0 b)))
include b v dv hv hv₀ hd hm

/-- An actual continuous zero endpoint and an integrable interior
derivative give the primitive identity up to the endpoint. No
derivative or smooth extension is required at that endpoint. -/
theorem dirichlet_zero_endpoint_primitive  (ht : t ∈ Ioc 0 b) :
    v t = ∫ s in (0 : ℝ)..t, dv s := by
  have hvc  := hv.mono
    (Icc_subset_Icc le_rfl ht.2)
  have hleft : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (v 0)) := by
    have h := hvc 0 ⟨le_rfl, ht.1.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ht.1] at h
    exact h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hright : Tendsto v (𝓝[<] t) (𝓝 (v t)) := by
    have h := hvc t ⟨ht.1.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE ht.1] at h
    exact h.mono_left (nhdsWithin_mono t Iio_subset_Iic_self)
  have hm'  :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have hi : IntervalIntegrable dv volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
    exact hm'.integrable (by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
    (fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩) hi hleft hright
  rw [hv₀, sub_zero] at h
  exact h.symm

/-- Actual L² derivative energy controls the value next to a zero
endpoint. This is the estimate needed to remove a thin boundary
strip when closing Dirichlet tests in H¹. -/
theorem dirichlet_zero_endpoint_norm_sq_le  (ht : t ∈ Ioc 0 b) :
    ‖v t‖ ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
  let μ := volume.restrict (Ioc 0 t)
  have hm'  :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2 μ := memLp_const 1
  have hi : (∫ s in (0 : ℝ)..t, dv s) = inner ℂ (h1.toLp _) (hm'.toLp _) := by
    rw [intervalIntegral.integral_of_le ht.1.le, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, hm'.coeFn_toLp] with s hs₁ hs₂
    simp_all
  have hnorm : ‖∫ s in (0 : ℝ)..t, dv s‖ ≤ ‖h1.toLp _‖ * ‖hm'.toLp _‖ := by
    rw [hi]
    exact norm_inner_le_norm _ _
  have hnormsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  have hn₁ : ‖h1.toLp _‖ ^ 2 = t := by
    rw [norm_sq_toLp_eq_integral]
    simp  
    simp [μ, Measure.real, ht.1.le]
  have hn₂ : ‖hm'.toLp _‖ ^ 2 = ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
    rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le ht.1.le]
  rw [mul_pow, hn₁, hn₂] at hnormsq
  rw [dirichlet_zero_endpoint_primitive hv hv₀ hd hm ht]
  exact hnormsq

/-- The actual zero endpoint controls the mass of a thin boundary
strip by the derivative energy in that same strip. The crude
constant `1` is sufficient to close Dirichlet cutoff tests. -/
theorem dirichlet_zero_endpoint_strip_mass_le  (hε : ε ∈ Ioc 0 b) :
    (∫ t in (0 : ℝ)..ε, ‖v t‖ ^ 2) / ε ^ 2 ≤
      ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2 := by
  have hmi : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioc 0 b) :=
    hm.integrable_norm_pow (by norm_num)
  have hI : IntervalIntegrable (fun t => ‖dv t‖ ^ 2) volume 0 ε := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε.1.le]
    exact hmi.mono_set (Ioc_subset_Ioc le_rfl hε.2)
  have hV : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 ε :=
    ((hv.mono (Icc_subset_Icc le_rfl hε.2)).norm.pow 2).intervalIntegrable_of_Icc hε.1.le
  have hE : 0 ≤ ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hε.1.le]
    positivity
  have hbnd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      ‖v t‖ ^ 2 ≤ ε * ∫ s in (0 : ℝ)..ε, ‖dv s‖ ^ 2 := by
    have hpt := dirichlet_zero_endpoint_norm_sq_le hv hv₀ hd hm
      ((⟨ht.1, ht.2.le.trans hε.2⟩))
    have hmono  :=
      intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
        (Eventually.of_forall fun _ => sq_nonneg _) hI
    exact hpt.trans ((mul_le_mul_of_nonneg_left hmono ht.1.le).trans
      (mul_le_mul_of_nonneg_right ht.2.le hE))
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hε.1.le hV
    (intervalIntegrable_const (c := ε * ∫ s in (0)..ε, ‖dv s‖ ^ 2)) hbnd
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hε.1)).mpr
  nlinarith

end


section
variable {a b : ℝ}
local notation "halfBoxFixed" => smoothDirichletHalfBox a b

include a b

/-- Genuine L² normal derivative energy gives L² energy on almost
every vertical slice, by the actual Lebesgue coordinate map. -/
theorem dirichlet_halfBox_vertical_memLp 
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict halfBoxFixed)) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
        (volume.restrict (Ioc (0 : ℝ) b)) := by
  let e  := Complex.measurableEquivRealProd.symm
  have hp  := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' halfBoxFixed = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt]
  have henergy := hg.integrable_norm_pow (by norm_num)
  have hprod := (hp.integrableOn_comp_preimage e.measurableEmbedding).mpr henergy
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖dirD v Complex.I (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) at hprod
  have hslice := hprod.prod_right_ae
  simp only [he] at hslice
  filter_upwards [hslice] with x hx
  have hLc : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := continuous_const.add
    (Complex.ofRealCLM.continuous.mul continuous_const)
  have hmeas  :=
    (measurable_fderiv_apply_const ℝ v Complex.I).comp hLc.measurable
  have hmL  :=
    (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr hx
  rw [restrict_Ioo_eq_restrict_Ioc] at hmL
  exact hmL

theorem dirichlet_halfBox_vertical_hasDerivAt 
    (hs : RealSmoothOn v halfBoxFixed)
     (hx : |x| < a) (hy : y ∈ Ioo 0 b) :
    HasDerivAt (fun s : ℝ => v ((x : ℂ) + (s : ℂ) * Complex.I))
      (dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) y := by
  have hyV : (x : ℂ) + (y : ℂ) * Complex.I ∈ halfBoxFixed := by
    simp_all [smoothDirichletHalfBox]
  have hdv := (hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hyV)
  have hL : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) Complex.I y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)
  exact hdv.hasFDerivAt.comp_hasDerivAt y hL

/-- Actual half-rectangle L² energy in real product coordinates.
This is precisely the product measure of its two coordinate
intervals, with the physical Lebesgue normalization preserved. -/
theorem dirichlet_halfBox_sq_integrable_real_prod {g : PlaneMap}
    (hg : MemLp g 2 (volume.restrict halfBoxFixed)) :
    Integrable (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2)
      ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo (0 : ℝ) b))) := by
  let e  := Complex.measurableEquivRealProd.symm
  have hp  := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' halfBoxFixed = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt]
  have henergy := hg.integrable_norm_pow (by norm_num)
  have hprod := (hp.integrableOn_comp_preimage e.measurableEmbedding).mpr henergy
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖g (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) at hprod
  simpa only [he] using hprod

/-- The true boundary-strip estimate after integration over the
tangential variable. Both sides are actual two-dimensional energies,
expressed by Fubini with the ordinary Lebesgue measure. -/
theorem dirichlet_halfBox_strip_mass_le
     (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : RealSmoothOn v halfBoxFixed)
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict halfBoxFixed))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict halfBoxFixed))
     (hε : ε ∈ Ioc 0 b) :
    (∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2 ≤
    ∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hsub : smoothDirichletHalfBox a ε ⊆ halfBoxFixed :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hε.2⟩
  have hvm := hm.mono_measure (Measure.restrict_mono_set volume hsub)
  have hgm := hg.mono_measure (Measure.restrict_mono_set volume hsub)
  have hVi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hvm).integral_prod_left
  have hGi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hgm).integral_prod_left
  have hbound :
      (fun x : ℝ => (∫ t in (0 : ℝ)..ε, ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
        ≤ᵐ[volume.restrict (Ioo (-a) a)]
      (fun x : ℝ => ∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg, ae_restrict_mem measurableSet_Ioo]
      with x hmL hxI
    have hx  := abs_lt.mpr hxI
    let L : ComplexCurve := fun t => x + t * Complex.I
    have hLc : Continuous L := continuous_const.add
      (Complex.ofRealCLM.continuous.mul continuous_const)
    have hmap : MapsTo L (Icc 0 b) (smoothDirichletClosedHalfBox a b) := by
      intro t ht
      simpa [L, smoothDirichletClosedHalfBox] using
        ((⟨hx.le, ht.1, ht.2⟩))
    have hvL := hv.comp hLc.continuousOn hmap
    have hzero : (v ∘ L) 0 = 0 := by simpa [L] using hz x hx
    exact dirichlet_zero_endpoint_strip_mass_le hvL hzero
      (fun t ht => dirichlet_halfBox_vertical_hasDerivAt hs hx ht) hmL hε
  have hi := integral_mono_ae (hVi.div_const (ε ^ 2)) hGi hbound
  simpa only [div_eq_mul_inv, integral_mul_const] using hi

end


theorem dirichlet_slice_energy_tendsto_zero  (hb : 0 < b) {dv : ComplexCurve}
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) :
    Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi  :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
      (hm.integrable_norm_pow (by norm_num))
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have h := hc 0 left_mem_uIcc
  rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb] at h
  simpa   using
    h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- The actual normal energy in a shrinking boundary strip tends
to zero after tangential integration. The majorant is the genuine
full-rectangle L² normal energy obtained from Fubini. -/
theorem dirichlet_halfBox_normal_strip_energy_tendsto_zero  (hb : 0 < b)
    
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let B : RealMap := fun x => ∫ t in (0)..b,
    ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2
  have hB : Integrable B (volume.restrict (Ioo (-a) a)) := by
    simpa only [B, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hg).integral_prod_left
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
      fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hεb⟩
    have hgm := hg.mono_measure (Measure.restrict_mono_set volume hsub)
    have hi := (dirichlet_halfBox_sq_integrable_real_prod hgm).integral_prod_left
    have hc : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        (volume.restrict (Ioo (-a) a)) := by
      simpa  [intervalIntegral.integral_of_le hε.le,
        integral_Ioc_eq_integral_Ioo] using hi
    exact hc.aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      ‖∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ B x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
    have hε₀  := hε
    have hi  :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
        (hx.integrable_norm_pow (by norm_num))
    have hnon : 0 ≤ ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hε₀.le]
      positivity
    rw [Real.norm_of_nonneg hnon]
    exact intervalIntegral.integral_mono_interval le_rfl hε₀.le hεb.le
      (Eventually.of_forall fun _ => sq_nonneg _) hi
  have hlim : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a), Tendsto
      (fun ε : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
    exact dirichlet_slice_energy_tendsto_zero hb hx
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (f := fun _ : ℝ => 0) B hmeas hbound hB hlim
  simpa only [integral_zero] using h

section
variable {a b } (hb : 0 < b) {v } (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b)) (hs : RealSmoothOn v (smoothDirichletHalfBox a b)) (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0) (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))

include a b hb v hv hs hz hm hg in
/-- The derivative-scale boundary-strip mass tends to zero in the
actual full half rectangle. This is the genuine estimate needed for
normal cutoffs when extending the weak equation to zero-boundary H¹
tests. It still does not assert a boundary second-derivative gain. -/
theorem dirichlet_halfBox_strip_mass_tendsto_zero :
    Tendsto (fun ε : ℝ =>
      (∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (dirichlet_halfBox_normal_strip_energy_tendsto_zero hb hg)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε₀  := hε
    apply div_nonneg _ (sq_nonneg _)
    apply integral_nonneg
    intro x
    change 0 ≤ ∫ t in (0)..ε, ‖v (x + t * Complex.I)‖ ^ 2
    rw [intervalIntegral.integral_of_le hε₀.le]
    positivity
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    grind [dirichlet_halfBox_strip_mass_le]

/-! ### Genuine smooth normal cutoffs -/

/-- The derivative of the actual smooth transition is zero off its
transition interval, including its two endpoints. The endpoint assertion
uses genuine differentiability at the global minimum or maximum. -/
theorem dirichlet_smoothTransition_deriv_eq_zero 
    (ht : t ≤ 0 ∨ 1 ≤ t) : deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have hmin : IsLocalMin Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition t ≤ Real.smoothTransition s
      rw [Real.smoothTransition.zero_of_nonpos ht]
      exact Eventually.of_forall Real.smoothTransition.nonneg
    exact hmin.deriv_eq_zero
  · have hmax : IsLocalMax Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition s ≤ Real.smoothTransition t
      rw [Real.smoothTransition.one_of_one_le ht]
      exact Eventually.of_forall Real.smoothTransition.le_one
    exact hmax.deriv_eq_zero

theorem exists_dirichlet_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C := by
  have hc  :=
    (show ContDiff ℝ 2 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv
      (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc 0 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have htz : t ≤ 0 ∨ 1 ≤ t := by
      grind
    simp_all [dirichlet_smoothTransition_deriv_eq_zero]

/-- A genuine smooth cutoff of the normal coordinate: it is zero below
height `ε` and one above height `2 * ε`. -/
def dirichletNormalCutoff ε (z : ℂ)  :=
  (Real.smoothTransition (z.im / ε - 1) : ℂ)

theorem dirichletNormalCutoff_contDiff ε :
    RealSmooth (dirichletNormalCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((Complex.imCLM.contDiff.div_const ε).sub contDiff_const))

theorem norm_dirichletNormalCutoff_le ε z :
    ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
  rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg
    (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

section
variable {ε : ℝ} (hε : 0 < ε) {z : ℂ}

section
include ε hε z

theorem dirichletNormalCutoff_eq_zero
    (hz : z.im ≤ ε) : dirichletNormalCutoff ε z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 := by
    have := (div_le_one hε).mpr hz
    linarith
  simp_all [dirichletNormalCutoff]

theorem dirichletNormalCutoff_eq_one
    (hz : 2 * ε ≤ z.im) : dirichletNormalCutoff ε z = 1 := by
  have ht : 1 ≤ z.im / ε - 1 := by
    have := (le_div_iff₀ hε).mpr hz
    linarith
  simp_all [dirichletNormalCutoff]

end


theorem dirichletNormalCutoff_fderiv ε z w :
    fderiv ℝ (dirichletNormalCutoff ε) z w =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε * w.im : ℝ) : ℂ) := by
  have hi : HasFDerivAt (fun u : ℂ => u.im / ε - 1)
      (ε⁻¹ • Complex.imCLM) z := by
    have h_simpa := ((Complex.imCLM.hasFDerivAt (x := z)).mul_const ε⁻¹).sub_const 1
    assumption
  have ht := (((show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable
      (by norm_num))) (z.im / ε - 1)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (ht.hasDerivAt.comp_hasFDerivAt z hi)
  have hd' : HasFDerivAt (dirichletNormalCutoff ε)
      (Complex.ofRealCLM.comp
        (deriv Real.smoothTransition (z.im / ε - 1) • (ε⁻¹ • Complex.imCLM))) z := hd
  rw [hd'.fderiv]
  simp  [div_eq_mul_inv, mul_assoc]

@[simp] theorem dirD_dirichletNormalCutoff_one ε z :
    dirD (dirichletNormalCutoff ε) 1 z = 0 := by
  simp_all [dirD, dirichletNormalCutoff_fderiv]

theorem dirD_dirichletNormalCutoff_I ε z :
    dirD (dirichletNormalCutoff ε) Complex.I z =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε : ℝ) : ℂ) := by
  simp_all [dirD, dirichletNormalCutoff_fderiv]

include ε hε z in
theorem dirD_dirichletNormalCutoff_I_eq_zero
    (hz : z.im ≤ ε ∨ 2 * ε ≤ z.im) :
    dirD (dirichletNormalCutoff ε) Complex.I z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 ∨ 1 ≤ z.im / ε - 1 := by
    rcases hz with hz | hz
    · have := (div_le_one hε).mpr hz
      exact Or.inl (by linarith)
    · have := (le_div_iff₀ hε).mpr hz
      exact Or.inr (by linarith)
  simp_all [dirD_dirichletNormalCutoff_I, dirichlet_smoothTransition_deriv_eq_zero]

end


theorem norm_dirD_dirichletNormalCutoff_I_le  (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) z :
    ‖dirD (dirichletNormalCutoff ε) Complex.I z‖ ≤ C / ε := by
  rw [dirD_dirichletNormalCutoff_I, Complex.norm_real, norm_div,
    Real.norm_of_nonneg hε.le]
  bound

/-- The actual additional gradient term created by a normal cutoff. -/
def dirichletNormalCutoffError ε (v : PlaneMap) z  :=
  dirD (dirichletNormalCutoff ε) Complex.I z * v z

theorem dirichletNormalCutoffError_memLp  (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) 
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletNormalCutoffError ε v) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hd : Continuous (dirD (dirichletNormalCutoff ε) Complex.I) :=
    ((dirichletNormalCutoff_contDiff ε).fderiv_right
      (m := ∞) le_rfl).continuous.clm_apply continuous_const
  apply hm.of_le_mul (c := C / ε) (hd.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖dirD (dirichletNormalCutoff ε) Complex.I z * v z‖ ≤ (C / ε) * ‖v z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_dirD_dirichletNormalCutoff_I_le hε hC z)
      (norm_nonneg _)

theorem dirichletNormalCutoffError_slice_eq_strip  (hε : 0 < ε)
    (hεb : 2 * ε ≤ b) v (x : ℝ) :
    (∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
    ∫ t in (0 : ℝ)..(2 * ε),
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by positivity)]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc le_rfl hεb)
  intro t ht
  have ht' : 2 * ε ≤ t := by
    grind
  have hzero : dirD (dirichletNormalCutoff ε) Complex.I
      ((x : ℂ) + (t : ℂ) * Complex.I) = 0 :=
    dirD_dirichletNormalCutoff_I_eq_zero hε (Or.inr (by simpa using ht'))
  simp_all [dirichletNormalCutoffError]

/-- The full additional-gradient energy is bounded by the genuine
derivative-scale strip mass. No boundary derivative or target H² gain
is used in this cutoff estimate. -/
theorem dirichletNormalCutoffError_energy_le 
    (hε : 0 < ε) (hεb : 2 * ε ≤ b) (hC₀ : 0 ≤ C)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) 
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
    (C ^ 2 / ε ^ 2) *
      (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hb  := (by positivity : 0 < 2 * ε).trans_le hεb
  have hE := dirichletNormalCutoffError_memLp hε hC hm
  have hEi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hE).integral_prod_left
  have hsub : smoothDirichletHalfBox a (2 * ε) ⊆ smoothDirichletHalfBox a b :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hεb⟩
  have hmi := hm.mono_measure (Measure.restrict_mono_set volume hsub)
  have hVi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..(2 * ε),
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε),
      integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hmi).integral_prod_left
  have hpoint : (fun x : ℝ => ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ᵐ[volume.restrict (Ioo (-a) a)]
      (fun x : ℝ => (C ^ 2 / ε ^ 2) * ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxabs  := abs_lt.mpr hx
    let L : ComplexCurve := fun t => x + t * Complex.I
    have hLc : Continuous L := continuous_const.add
      (Complex.ofRealCLM.continuous.mul continuous_const)
    have hmap : MapsTo L (Icc 0 (2 * ε)) (smoothDirichletClosedHalfBox a b) := by
      intro t ht
      simpa [L, smoothDirichletClosedHalfBox] using
        ((⟨hxabs.le, ht.1, ht.2.trans hεb⟩))
    have hvL := hv.comp hLc.continuousOn hmap
    have hdL : Continuous (fun t =>
        dirD (dirichletNormalCutoff ε) Complex.I (L t)) :=
      (((dirichletNormalCutoff_contDiff ε).fderiv_right
        (m := ∞) le_rfl).continuous.clm_apply continuous_const).comp hLc
    have hVL : IntervalIntegrable (fun t => ‖v (L t)‖ ^ 2) volume 0 (2 * ε) :=
      (hvL.norm.pow 2).intervalIntegrable_of_Icc (by positivity)
    have hEL : IntervalIntegrable (fun t =>
        ‖dirichletNormalCutoffError ε v (L t)‖ ^ 2) volume 0 (2 * ε) :=
      (((hdL.continuousOn.mul hvL).norm).pow 2).intervalIntegrable_of_Icc (by positivity)
    have hle : ∀ t ∈ Ioo 0 (2 * ε),
        ‖dirichletNormalCutoffError ε v (L t)‖ ^ 2 ≤
          (C ^ 2 / ε ^ 2) * ‖v (L t)‖ ^ 2 := by
      intro t _
      dsimp only [dirichletNormalCutoffError]
      rw [norm_mul, mul_pow]
      have hn := (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hC₀ hε.le)).mpr (norm_dirD_dirichletNormalCutoff_I_le hε hC (L t))
      simpa only [div_pow] using mul_le_mul_of_nonneg_right hn (sq_nonneg _)
    rw [dirichletNormalCutoffError_slice_eq_strip hε hεb]
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (by positivity)
      hEL (hVL.const_mul (C ^ 2 / ε ^ 2)) hle
    measurability
  simpa only [integral_const_mul] using
    integral_mono_ae hEi (hVi.const_mul (C ^ 2 / ε ^ 2)) hpoint

include a b hb v hv hs hz hm hg in
/-- The genuine normal cutoff's additional gradient tends to zero
in the full two-dimensional energy. This is derived from actual
zero boundary values and H¹ energy, not from an asserted density
or boundary regularity principle. -/
theorem dirichletNormalCutoffError_energy_tendsto_zero :
    Tendsto (fun ε : ℝ => ∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC₀, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  have hscale : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝 (2 * 0)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp_all
  have hstrip := (dirichlet_halfBox_strip_mass_tendsto_zero hb hv hs hz hm hg).comp hscale
  have hupper : Tendsto (fun ε : ℝ => (C ^ 2 / ε ^ 2) *
      (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (4 * C ^ 2) *
        ((∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
          ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 ((4 * C ^ 2) * 0)) :=
      tendsto_const_nhds.mul hstrip
    grind
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun ε => integral_nonneg fun x =>
      intervalIntegral.integral_nonneg_of_forall hb.le (fun _ => sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (half_pos hb)).filter_mono nhdsWithin_le_nhds]
      with ε hε hεb
    exact dirichletNormalCutoffError_energy_le hε (by linarith) hC₀ hC hv hm

/-- Fubini identifies the actual physical squared norm with its two
real coordinate integrals. The coordinate transformation has Jacobian
one, so no scale factor is introduced. -/
theorem dirichlet_halfBox_sq_integral_eq_real_prod  (hb : 0 < b)
    {g : PlaneMap} (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
        ‖g ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  let e := Complex.measurableEquivRealProd.symm
  have hp  := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt]
  have hmeas  :=
    (isOpen_smoothDirichletHalfBox a b).measurableSet
  have hind : (fun p => (smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2) (e p)) =
      (e ⁻¹' smoothDirichletHalfBox a b).indicator (fun p => ‖g (e p)‖ ^ 2) := by
    rfl
  have hi := hp.integral_comp e.measurableEmbedding
    ((smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2))
  rw [hind, integral_indicator (hmeas.preimage e.measurable),
    integral_indicator hmeas, hpre, Measure.volume_eq_prod,
    ← Measure.prod_restrict] at hi
  rw [← hi]
  have hprod := dirichlet_halfBox_sq_integrable_real_prod hg
  simpa  [he, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
    using integral_prod
      (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * Complex.I)‖ ^ 2) hprod

include a b hb v hv hs hz hm hg in
theorem dirichletNormalCutoffError_physical_energy_tendsto_zero :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirichletNormalCutoffError ε v z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  apply (dirichletNormalCutoffError_energy_tendsto_zero hb hv hs hz hm hg).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dirichlet_halfBox_sq_integral_eq_real_prod hb
    (dirichletNormalCutoffError_memLp hε hC hm)).symm

theorem dirichletNormalCutoff_tendsto_one  (hz : 0 < z.im) :
    Tendsto (fun ε : ℝ => dirichletNormalCutoff ε z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (half_pos hz)).filter_mono nhdsWithin_le_nhds]
    with ε hε hεz
  grind [dirichletNormalCutoff_eq_one, PolyaNeumann.dirichletNormalCutoff]

/-- Multiplication by the actual cutoff tends to the identity in L².
The majorant is four times the original squared norm. -/
theorem dirichletNormalCutoff_weight_error_energy_tendsto_zero  
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let B  := fun z => 4 * ‖g z‖ ^ 2
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun z => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) μ := by
    intro ε
    exact ((((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const).aestronglyMeasurable.mul
      hg.aestronglyMeasurable).norm).pow 2
  have hbound : ∀ ε : ℝ, ∀ᵐ z ∂μ,
      ‖‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2‖ ≤ B z := by
    intro ε
    exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hnorm : ‖dirichletNormalCutoff ε z - 1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by
          rw [norm_one]
          linarith [norm_dirichletNormalCutoff_le ε z])
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hnorm
      nlinarith
  have hB  :=
    (hg.integrable_norm_pow (by norm_num)).const_mul 4
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun ε : ℝ => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    have h : Tendsto (fun ε : ℝ => (dirichletNormalCutoff ε z - 1) * g z)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - 1 : ℂ) * g z)) :=
      ((dirichletNormalCutoff_tendsto_one hz.2.1).sub
        tendsto_const_nhds).mul tendsto_const_nhds
    simpa   using h.norm.pow 2
  simpa   using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hB hlim

/-- Localization may reach the bottom edge. Its actual smooth normal
cutoff is nevertheless a genuine compact interior test, because it
vanishes on a whole neighborhood of that edge. -/
theorem dirichletNormalCutoff_testFunction  (hε : 0 < ε)
    (η : smoothTraceTests)
    (hη : tsupport (η : PlaneMap) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
     (hs : RealSmoothOn v (smoothDirichletHalfBox a b)) :
    TestFunction (smoothDirichletHalfBox a b)
      (fun z => η z * dirichletNormalCutoff ε z * v z) := by
  let w  := fun z => η z * dirichletNormalCutoff ε z * v z
  have hws : RealSmooth w := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ smoothDirichletHalfBox a b
    · exact (η.property.1.contDiffAt.mul
        (dirichletNormalCutoff_contDiff ε).contDiffAt).mul
        (hs.contDiffAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))
    · apply (contDiff_const : RealSmooth (fun _ : ℂ => (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
      by_cases hzε : z.im < ε
      · have hn  :=
          (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzε
        filter_upwards [hn] with u hu
        grind only [dirichletNormalCutoff_eq_zero]
      · have hzη : z ∉ tsupport (η : PlaneMap) := by
          intro hzη
          obtain ⟨hx, hy⟩ := hη hzη
          exact hz ⟨hx, hε.trans_le (le_of_not_gt hzε), hy⟩
        have hn := (isClosed_tsupport η).isOpen_compl.mem_nhds hzη
        filter_upwards [hn] with u hu
        simp  [w, image_eq_zero_of_notMem_tsupport hu]
  have hwc : HasCompactSupport w := η.property.2.1.mul_right.mul_right
  have hwη : tsupport w ⊆ tsupport (η : PlaneMap) :=
    tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hheight : tsupport w ⊆ {z : ℂ | ε ≤ z.im} := by
    apply closure_minimal _ (isClosed_le continuous_const Complex.continuous_im)
    intro z hz
    by_contra h
    have hcut := dirichletNormalCutoff_eq_zero hε (le_of_not_ge h)
    measurability
  grind [PolyaNeumann.TestFunction, PolyaNeumann.smoothDirichletHalfBox, PolyaNeumann.smoothTraceTests, PolyaNeumann.dirichletNormalCutoff]

theorem dirichletNormalCutoff_weight_error_memLp  ε 
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (fun z => (dirichletNormalCutoff ε z - 1) * g z) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply hg.of_le_mul (c := 2) ((((dirichletNormalCutoff_contDiff ε).continuous.sub
    continuous_const).aestronglyMeasurable).mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖(dirichletNormalCutoff ε z - 1) * g z‖ ≤ 2 * ‖g z‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith [norm_dirichletNormalCutoff_le ε z])

/-- The cutoff product rule is proved at every actual interior point. -/
theorem dirichletNormalCutoff_product_dirD  ε 
    (hs : RealSmoothOn v (smoothDirichletHalfBox a b))
     (hz : z ∈ smoothDirichletHalfBox a b) w :
    dirD (fun u => dirichletNormalCutoff ε u * v u) w z =
      dirichletNormalCutoff ε z * dirD v w z +
        dirD (dirichletNormalCutoff ε) w z * v z := by
  have hc := (dirichletNormalCutoff_contDiff ε).differentiable (by simp)
  have hv := (hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz)
  simp  [dirD]
  change (fderiv ℝ (dirichletNormalCutoff ε * v) z) w = _
  rw [fderiv_mul (hc z) hv]
  simp  
  ring

include a b hb v hv hs hz hm hg in
/-- The actual normal gradient of the cutoff product converges in
L² to the actual normal gradient of the original zero-boundary H¹
function. Both terms in the product rule are controlled separately. -/
theorem dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
        dirD v Complex.I z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let A  := fun ε z =>
    (dirichletNormalCutoff ε z - 1) * dirD v Complex.I z
  let B  := fun ε z => dirichletNormalCutoffError ε v z
  have hA := dirichletNormalCutoff_weight_error_energy_tendsto_zero hg
  have hB := dirichletNormalCutoffError_physical_energy_tendsto_zero hb hv hs hz hm hg
  have hup : Tendsto (fun ε : ℝ => 2 * (∫ z, ‖A ε z‖ ^ 2 ∂μ) +
      2 * (∫ z, ‖B ε z‖ ^ 2 ∂μ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.mul hA).add (tendsto_const_nhds.mul hB)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall fun ε => integral_nonneg fun z => sq_nonneg _
  · obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAm : MemLp (A ε) 2 μ := dirichletNormalCutoff_weight_error_memLp ε hg
    have hBm  := dirichletNormalCutoffError_memLp hε hC hm
    have hsum : (fun z => A ε z + B ε z) =ᵐ[μ]
        (fun z => dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z) := by
      filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
        with z hzV
      grind only [dirichletNormalCutoff_product_dirD, dirichletNormalCutoffError]
    have hDm := (hAm.add hBm).ae_eq hsum
    have hAi := hAm.integrable_norm_pow (by norm_num)
    have hBi := hBm.integrable_norm_pow (by norm_num)
    have hDi := hDm.integrable_norm_pow (by norm_num)
    have hbound : (fun z =>
        ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z‖ ^ 2) ≤ᵐ[μ]
        (fun z => 2 * ‖A ε z‖ ^ 2 + 2 * ‖B ε z‖ ^ 2) := by
      filter_upwards [hsum] with z hzsum
      rw [← hzsum]
      have hn := norm_add_le (A ε z) (B ε z)
      have hn' := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      nlinarith [sq_nonneg (‖A ε z‖ - ‖B ε z‖)]
    have hi := integral_mono_ae hDi ((hAi.const_mul 2).add (hBi.const_mul 2)) hbound
    simpa only [Pi.add_apply, integral_add (hAi.const_mul 2) (hBi.const_mul 2), integral_const_mul]
      using hi

end


theorem dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero 
    
    (hs : RealSmoothOn v (smoothDirichletHalfBox a b))
    (hg : MemLp (dirD v 1) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) 1 z -
        dirD v 1 z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (dirichletNormalCutoff_weight_error_energy_tendsto_zero hg).congr'
  exact Eventually.of_forall fun ε => by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    grind only [dirichletNormalCutoff_product_dirD, dirD_dirichletNormalCutoff_one]

end PolyaNeumann

end
