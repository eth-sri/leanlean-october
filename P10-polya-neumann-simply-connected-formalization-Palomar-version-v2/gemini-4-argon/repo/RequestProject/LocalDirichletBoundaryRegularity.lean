module

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

variable {ε : ℝ} {g : ℂ → ℂ}

/-- The project's coordinate Laplacian equals the genuine Euclidean
Laplacian at every point of twice continuous differentiability. -/
theorem lap_eq_euclidean_laplacian  
    (hf : ContDiffAt ℝ 2 f z) : lap f z = Laplacian.laplacian f z := by
  have he v : dirD (dirD f v) v z = fderiv ℝ (fderiv ℝ f) z v v := by
    change fderiv ℝ (fun w => fderiv ℝ f w v) z v = _
    rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) (differentiableAt_const v)]
    simp [fderiv_const_apply]
  rw [lap, he, he, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]

/-- A local equality transports both actual coordinate second
derivatives. No assumed differential equation is used. -/
theorem eventuallyEq_lap_eq   (hfg : f =ᶠ[𝓝 z] g) :
    lap f z = lap g z := by
  have hd v : dirD f v =ᶠ[𝓝 z] dirD g v :=
    (hfg.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A v)
  have hdd v : dirD (dirD f v) v z = dirD (dirD g v) v z :=
    congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((hd v).fderiv_eq (𝕜 := ℝ))
  exact congrArg₂ (· + ·) (hdd 1) (hdd Complex.I)

theorem smooth_integral_dirD_mul_test  
    (hG : TestFunction univ G) (hφ : TestFunction U φ) i :
    (∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
  have hu := (hG.dirD (coordDir i)).memLp' 2 (μ := volume.restrict U)
  have hg j := ((hG.dirD (coordDir i)).dirD (coordDir j)).memLp' 2
    (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth (hG.dirD (coordDir i)).1 hu hg φ hφ i
  change (∫ z in U, (hu.toLp _) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hg i).toLp _) z * φ z) at hw
  rw [integral_congr_ae (by
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]), integral_congr_ae (show (fun z => ((hg i).toLp _) z * φ z) =ᵐ[volume.restrict U] (fun z => dirD (dirD G (coordDir i)) (coordDir i) z * φ z) by
    filter_upwards [(hg i).coeFn_toLp] with z hz
    rw [hz])] at hw
  exact hw

/-- The true weak Poisson identity for a function smooth only in the
open domain. The compact test is localized before integration by
parts, so no boundary derivatives or global second-derivative energy
are needed. -/
theorem local_smooth_gradient_test_eq_neg_lap  (hU : IsOpen U)
     (hv : ContDiffOn ℝ ∞ v U) (hφ : TestFunction U φ) :
    (∫ z in U, ∑ i : Fin 2, dirD v (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, lap v z * φ z) := by
  obtain ⟨G, hG, hGv⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hv
  have hfirst i :
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) =
        (fun z => dirD v (coordDir i) z * dirD φ (coordDir i) z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD v (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i)) ((hGv z hz).fderiv_eq (𝕜 := ℝ))]
    · simp [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
  have hint i :
      IntegrableOn (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) U :=
    ((hG.dirD (coordDir i)).memLp' 2).integrable_mul ((hφ.dirD (coordDir i)).memLp' 2)
  calc
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Finset.sum_congr rfl (fun i _ =>
        congrFun (hfirst i).symm z))
    _ = _ :=
      integral_finset_sum _ (fun i _ => hint i)
    _ = -(∫ z in U, lap G z * φ z) := by
      simp_rw [smooth_integral_dirD_mul_test hG hφ]
      rw [Fin.sum_univ_two, show (∫ z in U, lap G z * φ z) = (∫ z in U, dirD (dirD G 1) 1 z * φ z) + ∫ z in U, dirD (dirD G Complex.I) Complex.I z * φ z by
        simp_rw [lap, add_mul]
        exact integral_add ((((hG.dirD 1).dirD 1).memLp' 2).integrable_mul (hφ.memLp' 2)) ((((hG.dirD Complex.I).dirD Complex.I).memLp' 2).integrable_mul (hφ.memLp' 2))]
      simp [coordDir]
      ring
    _ = _ := by rw [show (fun z => lap G z * φ z) = (fun z => lap v z * φ z) by
      funext z
      by_cases hz : z ∈ tsupport φ
      · rw [eventuallyEq_lap_eq (hGv z hz)]
      · simp [image_eq_zero_of_notMem_tsupport hz]]

/-- The actual physical Dirichlet remainder after subtracting the
constructed smooth real boundary datum. -/
def riemannMappingDirichletRemainder (F : ℂ → ℂ) (b : smoothTraceTests) (z : ℂ) : ℂ :=
  (riemannMappingGreenCorrection F z : ℂ) - b z

theorem lap_sub_of_contDiffAt  
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    lap (fun w => f w - g w) z = lap f z - lap g z := by
  have heq : (fun w => f w - g w) = f + (-1 : ℝ) • g := by
    funext w
    change f w - g w = f w + (-1 : ℝ) • g w
    rw [neg_one_smul, sub_eq_add_neg]
  rw [lap_eq_euclidean_laplacian (hf.sub hg), heq, (hf.laplacian_add (hg.const_smul (-1 : ℝ)) : Laplacian.laplacian (f + (-1 : ℝ) • g) z = Laplacian.laplacian f z + Laplacian.laplacian ((-1 : ℝ) • g) z), (laplacian_smul (-1 : ℝ) hg : Laplacian.laplacian ((-1 : ℝ) • g) z = (-1 : ℝ) • Laplacian.laplacian g z),
    ← lap_eq_euclidean_laplacian hf, ← lap_eq_euclidean_laplacian hg]
  simp [sub_eq_add_neg]

/-- The actual zero-boundary H¹ Poisson problem needed for boundary
regularity. Its function, smooth forcing, boundary values, H¹ vector,
and compact-test equation are derived from the constructed Green
correction. No zero-trace or boundary regularity premise is added. -/
theorem exists_riemannMapping_zero_boundary_poisson_problem 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    ∃ b : smoothTraceTests, ∃ u : NeumannH1 Ω,
      ContinuousOn (riemannMappingDirichletRemainder F b) (closure Ω) ∧
      ContDiffOn ℝ ∞ (riemannMappingDirichletRemainder F b) Ω ∧
      (∀ z ∈ frontier Ω, riemannMappingDirichletRemainder F b z = 0) ∧
      (h1Value Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] riemannMappingDirichletRemainder F b ∧
      (∀ i : Fin 2, (h1Gradient Ω i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
        dirD (riemannMappingDirichletRemainder F b) (coordDir i)) ∧
      (∀ z ∈ Ω, lap (riemannMappingDirichletRemainder F b) z = -lap (b : ℂ → ℂ) z) ∧
      ∀ φ : ℂ → ℂ, TestFunction Ω φ →
        (∫ z in Ω, ∑ i : Fin 2, dirD (riemannMappingDirichletRemainder F b) (coordDir i) z *
          dirD φ (coordDir i) z) = ∫ z in Ω, lap (b : ℂ → ℂ) z * φ z := by
  obtain ⟨b₀, hbdata⟩ := exists_riemannMappingGreenCorrection_smooth_boundary_data
    hb hS hsc F hF hinj himage
  let b := (show smoothTraceTests by
    let L := Complex.ofRealCLM.comp Complex.reCLM
    refine ⟨fun z => (b₀ z).re, ?_⟩
    refine ⟨L.contDiff.comp b₀.property.1, ?_, subset_univ _⟩
    exact b₀.property.2.1.comp_left (show L 0 = 0 by simp [L]))
  obtain ⟨u₀, hu₀, hgu₀⟩ := exists_riemannMappingGreenCorrectionH1 hb hS hsc F hF hinj himage
  let h : ℂ → ℂ := fun z => riemannMappingGreenCorrection F z
  have hharm : HarmonicOnNhd h Ω :=
    (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
      Complex.ofRealCLM
  have hs := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hv : ContDiffOn ℝ ∞ (riemannMappingDirichletRemainder F b) Ω :=
    hs.sub b.property.1.contDiffOn
  have hΔ z (hz : z ∈ Ω) :
      lap (riemannMappingDirichletRemainder F b) z = -lap b z := by
    have hh : ContDiffAt ℝ 2 h z := (hharm z hz).1
    have hb : ContDiffAt ℝ 2 b z := b.property.1.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
    exact (lap_sub_of_contDiffAt hh hb).trans (by
      rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds]
      simp)
  refine ⟨b, u₀ - smoothTraceH1 Ω b, ?_, hv, ?_, ?_, ?_, hΔ, ?_⟩
  · exact (Complex.ofRealCLM.continuous.comp_continuousOn
      (riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage)).sub
        b.property.1.continuous.continuousOn
  · intro z hz
    change (riemannMappingGreenCorrection F z : ℂ) - (b₀ z).re = 0
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
    have hc : fderiv ℝ h z =
        Complex.ofRealCLM.comp (fderiv ℝ (riemannMappingGreenCorrection F) z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) z = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt (((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)),
        ContinuousLinearMap.fderiv]
    have hh : DifferentiableAt ℝ h z :=
      (hs.differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)
    rw [hz, Pi.sub_apply, hu, h1Gradient_smoothTraceH1, hbz]
    change _ = fderiv ℝ (h - (b : ℂ → ℂ)) z (coordDir i)
    rw [fderiv_sub hh ((b.property.1.differentiable (by simp)) z), hc]
    simp
  · intro φ hφ
    rw [local_smooth_gradient_test_eq_neg_lap hS.1.1 hv hφ]
    rw [integral_congr_ae (by
      filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with z hz
      rw [hΔ z hz, neg_mul]), integral_neg, neg_neg]

/-! ## Actual smooth graph coordinates -/

/-- The genuine graph shear. Its inverse subtracts the same graph
height, because the shear preserves the real coordinate. -/
def smoothDirichletGraphShear (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  z + (f z.re : ℂ) * Complex.I

@[simp] theorem smoothDirichletGraphShear_re f z :
    (smoothDirichletGraphShear f z).re = z.re := by
  simp [smoothDirichletGraphShear]

@[simp] theorem smoothDirichletGraphShear_im f z :
    (smoothDirichletGraphShear f z).im = z.im + f z.re := by
  simp [smoothDirichletGraphShear]

/-- This is a global real homeomorphism, built from the supplied
continuous graph, rather than an assumed boundary coordinate map. -/
def smoothDirichletGraphShearHomeomorph (f : ℝ → ℝ) (hf : Continuous f) : ℂ ≃ₜ ℂ where
  toFun := smoothDirichletGraphShear f
  invFun := fun z => z - (f z.re : ℂ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp [smoothDirichletGraphShear]
  right_inv z := by
    apply Complex.ext <;> simp [smoothDirichletGraphShear]
  continuous_toFun := continuous_id.add
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)
  continuous_invFun := continuous_id.sub
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)

@[simp] theorem smoothDirichletGraphShearHomeomorph_apply f
    hf z :
    smoothDirichletGraphShearHomeomorph f hf z = smoothDirichletGraphShear f z := rfl

@[simp] theorem smoothDirichletGraphShearHomeomorph_symm_apply f
    hf z :
    (smoothDirichletGraphShearHomeomorph f hf).symm z =
      z - (f z.re : ℂ) * Complex.I := rfl

theorem smoothDirichletGraphShear_lipschitz  
    (hf : LipschitzWith K f) : LipschitzWith (K + 1) (smoothDirichletGraphShear f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp [dist_eq_norm]
  calc
    _ =
        ‖(z - w) + (f z.re - f w.re : ℝ) * Complex.I‖ := by
      congr 1
      simp [smoothDirichletGraphShear]
      ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      exact (hf.norm_sub_le z.re w.re).trans
        (mul_le_mul_of_nonneg_left (by
          simpa only [Real.norm_eq_abs, Complex.sub_re] using Complex.abs_re_le_norm (z - w)) K.coe_nonneg))
    _ = _ := by ring

/-- The graph shear followed by the actual rigid coordinates of the
smooth-domain chart. Only continuity of the supplied graph and a
nonzero rigid factor are required to construct this homeomorphism. -/
def smoothDirichletGraphChart (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) :
    ℂ ≃ₜ ℂ :=
  (smoothDirichletGraphShearHomeomorph f hf).trans
    ((Homeomorph.mulRight₀ c hc).symm.trans (Homeomorph.addLeft p))

@[simp] theorem smoothDirichletGraphChart_apply (p c : ℂ) hc
    f hf z :
    smoothDirichletGraphChart p c hc f hf z = p + smoothDirichletGraphShear f z / c := by
  simp [smoothDirichletGraphChart, Homeomorph.mulRight₀_symm_apply, div_eq_mul_inv]

theorem smoothDirichletGraphChart_rotate (p c : ℂ) hc
    f hf z :
    c * (smoothDirichletGraphChart p c hc f hf z - p) = smoothDirichletGraphShear f z := by
  rw [smoothDirichletGraphChart_apply]
  field_simp [hc]
  ring

theorem smoothDirichletGraphChart_contDiff (p c : ℂ) hc
     (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothDirichletGraphChart p c hc f hf.continuous) :=
  contDiff_const.add ((contDiff_id.add ((Complex.ofRealCLM.contDiff.comp (hf.comp Complex.reCLM.contDiff)).mul contDiff_const)).div_const c)

/-- The smooth-domain definition supplies an actual flattened full
rectangle on which physical membership is exactly positive height.
The homeomorphism is built above from that domain's own graph. -/
theorem exists_smoothDomain_flattening_rectangle  (hS : IsSmoothDomain Ω)
     (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      ∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im) := by
  obtain ⟨c, r, h, K, f, hc₁, hr, hh, hf, hLip, hf₀, _, hchart⟩ := hS.2 p hp
  have hc : c ≠ 0 := by
    intro heq
    simp only [heq, norm_zero] at hc₁
    norm_num at hc₁
  let b := h / 4
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  refine ⟨c, hc, f, hf, K, min r (h / (4 * (K + 1))), b, hc₁, hLip, hf₀, lt_min hr (div_pos hh hden), div_pos hh (by norm_num), ?_⟩
  intro z hzre hzim
  have hscale : 4 * ((K : ℝ) + 1) * |z.re| < h := by
    simpa [mul_comm] using
      (lt_div_iff₀ hden).mp (hzre.trans_le (min_le_right _ _))
  have hfz : |f z.re| ≤ (K : ℝ) * |z.re| := by
    simpa [hf₀] using hLip.norm_sub_le z.re 0
  have hfzh : |f z.re| < h / 4 := by
    nlinarith [abs_nonneg z.re]
  simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re,
    smoothDirichletGraphShear_im, lt_add_iff_pos_left] using (hchart (smoothDirichletGraphChart p c hc f hf.continuous z) (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re] using (hzre.trans_le (min_le_left _ _))) (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_im] using (show |z.im + f z.re| < h by
      have hs := abs_add_le z.im (f z.re)
      dsimp [b] at hzim
      linarith)))

/-- The bottom edge in an actual flattening rectangle maps to the
physical frontier. This follows from positive-height approach and
the local membership equivalence; frontier membership is not a new
coordinate premise. -/
theorem smoothDirichletGraphChart_mem_frontier  (hΩ : IsOpen Ω)
    (p c : ℂ) hc f hf {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
     (hx : |x| < a) :
    smoothDirichletGraphChart p c hc f hf (x : ℂ) ∈ frontier Ω := by
  let Ψ := smoothDirichletGraphChart p c hc f hf
  rw [hΩ.frontier_eq]
  exact ⟨mem_closure_of_tendsto ((Ψ.continuous.tendsto x).comp (by
    simpa using ((tendsto_const_nhds.add ((Complex.ofRealCLM.continuous.tendsto 0).mul_const Complex.I)).mono_left nhdsWithin_le_nhds))) (show ∀ᶠ t : ℝ in 𝓝[>] 0, Ψ (x + t * Complex.I) ∈ Ω by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
    have ht₀ := ht
    apply (hchart _ (by simpa using hx) (by simpa [abs_of_pos ht₀] using htb)).mpr
    simpa using ht₀), (show Ψ x ∉ Ω by
    simpa only [Complex.ofReal_im, lt_self_iff_false, iff_false] using (hchart x (by simpa using hx) (by simpa using hb)))⟩

/-- True zero boundary values of a physical continuous solution
remain true zero values on the flattened boundary interval. -/
theorem smoothDirichletGraphChart_zero_boundary  (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) f hf {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    (v : ℂ → ℂ) (hv : ∀ z ∈ frontier Ω, v z = 0)  (hx : |x| < a) :
    v (smoothDirichletGraphChart p c hc f hf (x : ℂ)) = 0 :=
  hv _ (smoothDirichletGraphChart_mem_frontier hΩ p c hc f hf hb hchart hx)

/-- An actual pointwise H¹ function remains pointwise H¹ under the
constructed graph coordinates. This uses the proved bi-Lipschitz
L² pullback and actual chain differential, with no assumed pullback
energy or flattened Sobolev regularity. -/
theorem smoothDirichletGraphChart_pullback_memLp {Ω U : Set ℂ}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (p c : ℂ) hc (hc₁ : ‖c‖ = 1)
     (hf : ContDiff ℝ ∞ f)  (hLip : LipschitzWith K f)
    (himage : smoothDirichletGraphChart p c hc f hf.continuous '' U ⊆ Ω)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ ∞ v Ω)
    (hm : MemLp v 2 (volume.restrict Ω))
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict Ω)) :
    MemLp (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) 2
      (volume.restrict U) ∧
    ∀ i : Fin 2, MemLp
      (dirD (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) (coordDir i))
      2 (volume.restrict U) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  have hK : 0 < K + 1 := by positivity
  have hΨ : LipschitzOnWith (K + 1) Ψ U :=
    (show LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hLip.continuous) by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      have heq : smoothDirichletGraphChart p c hc f hLip.continuous z -
          smoothDirichletGraphChart p c hc f hLip.continuous w =
          (smoothDirichletGraphShear f z - smoothDirichletGraphShear f w) / c := by
        simp
        ring
      simpa only [dist_eq_norm, heq, norm_div, hc₁, div_one] using
        (smoothDirichletGraphShear_lipschitz hLip).dist_le_mul z w).lipschitzOnWith
  have hΨinv : LipschitzOnWith (K + 1) Ψ.symm (Ψ '' U) :=
    (show LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hLip.continuous).symm by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      change dist ((smoothDirichletGraphShearHomeomorph f hLip.continuous).symm ((-p + z) * c))
        ((smoothDirichletGraphShearHomeomorph f hLip.continuous).symm ((-p + w) * c)) ≤ _
      have heq : (-p + z) * c - (-p + w) * c = (z - w) * c := by ring
      simpa [dist_eq_norm, heq, hc₁] using ((show LipschitzWith (K + 1) (smoothDirichletGraphShearHomeomorph f hLip.continuous).symm by
        rw [show (smoothDirichletGraphShearHomeomorph f hLip.continuous).symm = smoothDirichletGraphShear (fun x => -f x) by
          funext z
          simp [smoothDirichletGraphShear, sub_eq_add_neg]]
        exact smoothDirichletGraphShear_lipschitz hLip.neg).dist_le_mul ((-p + z) * c) ((-p + w) * c))).lipschitzOnWith
  have hm' :=
    hm.mono_measure (Measure.restrict_mono_set volume himage)
  have hg' i : MemLp (dirD v (coordDir i)) 2 (volume.restrict (Ψ '' U)) :=
    (hg i).mono_measure (Measure.restrict_mono_set volume himage)
  refine ⟨memLp_comp_bilip' hU hK hΨ hΨinv hm', ?_⟩
  intro i
  let G : Fin 2 → L2 (Ψ '' U) := fun j => (hg' j).toLp _
  have hmc := memLp_chainGrad hU hK hΨ hΨinv G i
  apply hmc.ae_eq
  filter_upwards [(ae_all_iff.mpr (fun j => (quasiMeasurePreserving_restrict hΨinv).ae (hg' j).coeFn_toLp) : ∀ᵐ z ∂(volume.restrict U), ∀ j : Fin 2, G j (Ψ z) = dirD v (coordDir j) (Ψ z)), ae_restrict_mem hU.measurableSet] with z hz hzU
  have hzΩ := himage (mem_image_of_mem Ψ hzU)
  have hdv := (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hzΩ)
  have hdΨ := ((smoothDirichletGraphChart_contDiff p c hc hf).differentiable (by simp)) z
  change chainGrad Ψ (fun j => (G j : ℂ → ℂ)) i z =
    fderiv ℝ (v ∘ Ψ) z (coordDir i)
  rw [fderiv_comp z hdv hdΨ, ContinuousLinearMap.comp_apply, clm_apply_eq_sum_coordRe]
  simp [chainGrad, hz, dirD]

def smoothDirichletHalfBox (a b : ℝ) : Set ℂ :=
  {z | |z.re| < a ∧ 0 < z.im ∧ z.im < b}

def smoothDirichletClosedHalfBox (a b : ℝ) : Set ℂ :=
  {z | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b}

theorem isOpen_smoothDirichletHalfBox a b : IsOpen (smoothDirichletHalfBox a b) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-! ## The actual elliptic coefficients of graph flattening -/

/-- The actual differential of the graph shear at graph slope `d`.
It maps `(x,y)` to `(x,y+d*x)`. -/
def smoothDirichletGraphDifferential (d : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + (d • Complex.reCLM).smulRight Complex.I

@[simp] theorem smoothDirichletGraphDifferential_apply d w :
    smoothDirichletGraphDifferential d w = w + (d * w.re) • Complex.I := by
  simp [smoothDirichletGraphDifferential]

theorem smoothDirichletGraphChart_hasFDerivAt (p c : ℂ) (hc : c ≠ 0)
     (hf : ContDiff ℝ ∞ f) z :
    HasFDerivAt (smoothDirichletGraphChart p c hc f hf.continuous)
      (c⁻¹ • smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hs := ((show HasFDerivAt (smoothDirichletGraphShear f) (smoothDirichletGraphDifferential (deriv f z.re)) z by
    have hs := (hasFDerivAt_id z).add ((((hf.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt).smul_const Complex.I)
    have h_simpa := hs
    simp [smoothDirichletGraphDifferential] at h_simpa ⊢
    exact h_simpa).mul_const c⁻¹).const_add p
  convert hs using 1
  funext x
  simp [div_eq_mul_inv]

theorem smoothDirichletGraphChart_fderiv_apply (p c : ℂ) hc
     (hf : ContDiff ℝ ∞ f) z w :
    fderiv ℝ (smoothDirichletGraphChart p c hc f hf.continuous) z w =
      c⁻¹ * (w + (deriv f z.re * w.re) • Complex.I) := by
  rw [(smoothDirichletGraphChart_hasFDerivAt p c hc hf z).fderiv]
  simp

/-- The actual chain rule exposes the inverse-graph energy
components. The physical derivatives occur in the rigid directions
`1/c` and `I/c`; the tangential shear term cancels exactly. -/
theorem smoothDirichletGraphChart_pullback_gradient (p c : ℂ) hc
     (hf : ContDiff ℝ ∞ f)  
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let u := v ∘ Ψ
     dirD u 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD u Complex.I z = fderiv ℝ v (Ψ z) (1 / c)) ∧
    dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      fderiv ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z) (Complex.I / c) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let T := fderiv ℝ v (Ψ z)
  let d := deriv f z.re
  have hchain w : dirD (v ∘ Ψ) w z = T (c⁻¹ * (w + (d * w.re) • Complex.I)) := by
    change fderiv ℝ (v ∘ Ψ) z w = _
    rw [fderiv_comp z hv ((smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt), ContinuousLinearMap.comp_apply,
      smoothDirichletGraphChart_fderiv_apply p c hc hf z w]
  have hI : dirD (v ∘ Ψ) Complex.I z = T (Complex.I / c) := by
    rw [hchain]
    simp [div_eq_mul_inv, mul_comm]
  constructor
  · change dirD (v ∘ Ψ) 1 z - d * dirD (v ∘ Ψ) Complex.I z = T (1 / c)
    rw [show dirD (v ∘ Ψ) 1 z = T (1 / c) + d • T (Complex.I / c) by
      rw [hchain]
      have he : c⁻¹ * ((1 : ℂ) + (d * (1 : ℂ).re) • Complex.I) =
          1 / c + d • (Complex.I / c) := by
        simp [div_eq_mul_inv]
        ring
      rw [he, map_add, map_smul], hI, Complex.real_smul, add_sub_cancel_right]
  · exact hI

/-- The energy form of the inverse graph differential. Its matrix is
`[[1, -d], [-d, 1+d²]]`, with `d = f′(x)`. -/
def smoothDirichletGraphQuadratic (d x y : ℝ) : ℝ :=
  x ^ 2 - 2 * d * x * y + (1 + d ^ 2) * y ^ 2

theorem smoothDirichletGraphQuadratic_eq_sq d x y :
    smoothDirichletGraphQuadratic d x y = (x - d * y) ^ 2 + y ^ 2 := by
  unfold smoothDirichletGraphQuadratic
  ring

/-- Genuine ellipticity follows from the actual Lipschitz graph
bound; no elliptic coefficient premise is substituted for it. -/
theorem smoothDirichletGraphQuadratic_bounds  
    (hf : LipschitzWith K f) (t x y : ℝ) :
    (x ^ 2 + y ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      smoothDirichletGraphQuadratic (deriv f t) x y ∧
    smoothDirichletGraphQuadratic (deriv f t) x y ≤
      2 * (1 + (K : ℝ) ^ 2) * (x ^ 2 + y ^ 2) := by
  let d := deriv f t
  have hd₂ : d ^ 2 ≤ K ^ 2 := by
    simpa using ((sq_le_sq₀ (abs_nonneg d) K.coe_nonneg).mpr (by
      simpa using norm_deriv_le_of_lipschitz hf (x₀ := t)))
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
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hd₂) (show 0 ≤ (x - d * y) ^ 2 + y ^ 2 by positivity)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd₂)
      (add_nonneg (sq_nonneg x) (sq_nonneg y))]

/-- The same genuine elliptic bounds hold for complex-valued
solutions, by applying the real coefficient form to the actual real
and imaginary components. -/
theorem smoothDirichletGraph_complex_energy_bounds  
    (hf : LipschitzWith K f) (t : ℝ) x y :
    (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ∧
    ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ≤
      2 * (1 + (K : ℝ) ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hr₁, hr₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.re y.re
  obtain ⟨hi₁, hi₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.im y.im
  rw [show ‖x - (deriv f t : ℝ) * y‖ ^ 2 + ‖y‖ ^ 2 = smoothDirichletGraphQuadratic (deriv f t) x.re y.re + smoothDirichletGraphQuadratic (deriv f t) x.im y.im by
    simp [Complex.sq_norm, Complex.normSq_apply, smoothDirichletGraphQuadratic]
    ring]
  constructor
  · have h := add_le_add hr₁ hi₁
    convert h using 1
    simp [Complex.sq_norm, Complex.normSq_apply, ← add_div]
    ring
  · have h := add_le_add hr₂ hi₂
    convert h using 1
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring

/-! ## The genuine one-dimensional zero-boundary energy step -/

/-- Actual L² derivative energy controls the value next to a zero
endpoint. This is the estimate needed to remove a thin boundary
strip when closing Dirichlet tests in H¹. -/
theorem dirichlet_zero_endpoint_norm_sq_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    ‖v t‖ ^ 2 ≤ t * ∫ s in 0..t, ‖dv s‖ ^ 2 := by
  let μ := volume.restrict (Ioc 0 t)
  have hm' : MemLp dv 2 μ :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2 μ := memLp_const 1
  have hnormsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (show ‖∫ s in 0..t, dv s‖ ≤ ‖h1.toLp _‖ * ‖hm'.toLp _‖ by
      rw [show (∫ s in (0 : ℝ)..t, dv s) = inner ℂ (h1.toLp _) (hm'.toLp _) by
        rw [intervalIntegral.integral_of_le ht.1.le, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [h1.coeFn_toLp, hm'.coeFn_toLp] with s hs₁ hs₂
        simp only [hs₁, hs₂, RCLike.inner_apply, map_one, mul_one]]
      exact norm_inner_le_norm _ _)
  rw [mul_pow, show ‖h1.toLp _‖ ^ 2 = t by
    rw [norm_sq_toLp_eq_integral]
    simp only [norm_one, one_pow]
    simp [μ, Measure.real, ht.1.le], show ‖hm'.toLp _‖ ^ 2 = ∫ s in 0..t, ‖dv s‖ ^ 2 by
    rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le ht.1.le]] at hnormsq
  rw [show v t = ∫ s in 0..t, dv s by
    have hvc := hv.mono
      (Icc_subset_Icc le_rfl ht.2)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
      (fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩) (by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
        exact (hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))).integrable (by norm_num)) (by
        have h := hvc 0 ⟨le_rfl, ht.1.le⟩
        rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ht.1] at h
        exact h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)) (by
        have h := hvc t ⟨ht.1.le, le_rfl⟩
        rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE ht.1] at h
        exact h.mono_left (nhdsWithin_mono t Iio_subset_Iic_self))
    rw [hv₀, sub_zero] at h
    exact h.symm]
  exact hnormsq

/-- The actual zero endpoint controls the mass of a thin boundary
strip by the derivative energy in that same strip. The crude
constant `1` is sufficient to close Dirichlet cutoff tests. -/
theorem dirichlet_zero_endpoint_strip_mass_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b)))  (hε : ε ∈ Ioc 0 b) :
    (∫ t in 0..ε, ‖v t‖ ^ 2) / ε ^ 2 ≤
      ∫ t in 0..ε, ‖dv t‖ ^ 2 := by
  have hmi : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioc 0 b) :=
    hm.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hbnd t (ht : t ∈ Ioo 0 ε) :
      ‖v t‖ ^ 2 ≤ ε * ∫ s in 0..ε, ‖dv s‖ ^ 2 := by
    exact (dirichlet_zero_endpoint_norm_sq_le hv hv₀ hd hm (⟨ht.1, ht.2.le.trans hε.2⟩)).trans ((mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le (Eventually.of_forall fun _ => sq_nonneg _) (by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε.1.le]
      exact hmi.mono_set (Ioc_subset_Ioc le_rfl hε.2))) ht.1.le).trans
      (mul_le_mul_of_nonneg_right ht.2.le (by
        rw [intervalIntegral.integral_of_le hε.1.le]
        exact integral_nonneg (fun t => sq_nonneg _))))
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hε.1.le (((hv.mono (Icc_subset_Icc le_rfl hε.2)).norm.pow 2).intervalIntegrable_of_Icc hε.1.le : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 ε)
    (intervalIntegrable_const (c := ε * ∫ s in 0..ε, ‖dv s‖ ^ 2)) hbnd
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hε.1)).mpr
  nlinarith

/-- Genuine L² normal derivative energy gives L² energy on almost
every vertical slice, by the actual Lebesgue coordinate map. -/
theorem dirichlet_halfBox_vertical_memLp  
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
        (volume.restrict (Ioc (0 : ℝ) b)) := by
  let e := Complex.measurableEquivRealProd.symm
  have he p : e p = p.1 + p.2 * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hprod := ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage e.measurableEmbedding).mpr (hg.integrable_norm_pow (by norm_num : 2 ≠ 0))
  rw [show e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo 0 b by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt, and_assoc], IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖dirD v Complex.I (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) at hprod
  have hslice := hprod.prod_right_ae
  simp only [he] at hslice
  filter_upwards [hslice] with x hx
  have hmeas :=
    (measurable_fderiv_apply_const ℝ v Complex.I).comp (continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const) : Continuous (fun y : ℝ => x + y * Complex.I)).measurable
  have hmL :=
    (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr hx
  rw [restrict_Ioo_eq_restrict_Ioc] at hmL
  exact hmL

theorem dirichlet_halfBox_vertical_hasDerivAt  
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
     (hx : |x| < a) (hy : y ∈ Ioo 0 b) :
    HasDerivAt (fun s : ℝ => v ((x : ℂ) + (s : ℂ) * Complex.I))
      (dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) y := by
  exact ((hs.differentiableOn (by simp)).differentiableAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds (by
    simpa [smoothDirichletHalfBox] using (⟨hx, hy.1, hy.2⟩)))).hasFDerivAt.comp_hasDerivAt y (show HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) Complex.I y by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ))

/-- Actual half-rectangle L² energy in real product coordinates.
This is precisely the product measure of its two coordinate
intervals, with the physical Lebesgue normalization preserved. -/
theorem dirichlet_halfBox_sq_integrable_real_prod {a b : ℝ} 
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Integrable (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2)
      ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) := by
  let e := Complex.measurableEquivRealProd.symm
  have he p : e p = p.1 + p.2 * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hprod := ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage e.measurableEmbedding).mpr (hg.integrable_norm_pow (by norm_num : 2 ≠ 0))
  rw [show e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo 0 b by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt, and_assoc], IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖g (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) at hprod
  simpa [he] using hprod

/-- The true boundary-strip estimate after integration over the
tangential variable. Both sides are actual two-dimensional energies,
expressed by Fubini with the ordinary Lebesgue measure. -/
theorem dirichlet_halfBox_strip_mass_le 
     (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
     (hε : ε ∈ Ioc 0 b) :
    (∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε,
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2 ≤
    ∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hε.2⟩
  simpa only [div_eq_mul_inv, integral_mul_const] using (integral_mono_ae ((show Integrable (fun x : ℝ => ∫ t in 0..ε, ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) by
    simpa [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod (hm.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left).div_const (ε ^ 2)) (by
    simpa [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod (hg.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left) (by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg, ae_restrict_mem measurableSet_Ioo]
      with x hmL hxI
    have hx := abs_lt.mpr hxI
    let L : ℝ → ℂ := fun t => x + t * Complex.I
    exact dirichlet_zero_endpoint_strip_mass_le (hv.comp (continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const)).continuousOn (by
      intro t ht
      simpa [L, smoothDirichletClosedHalfBox] using
        (⟨hx.le, ht.1, ht.2⟩))) (by simpa [L] using hz x hx)
      (fun t ht => dirichlet_halfBox_vertical_hasDerivAt hs hx ht) hmL hε))

/-! ### Genuine smooth normal cutoffs -/

/-- The derivative of the actual smooth transition is zero off its
transition interval, including its two endpoints. The endpoint assertion
uses genuine differentiability at the global minimum or maximum. -/
theorem dirichlet_smoothTransition_deriv_eq_zero 
    (ht : t ≤ 0 ∨ 1 ≤ t) : deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have hmin : IsLocalMin Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition t ≤ _
      rw [Real.smoothTransition.zero_of_nonpos ht]
      exact Eventually.of_forall Real.smoothTransition.nonneg
    exact hmin.deriv_eq_zero
  · have hmax : IsLocalMax Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition s ≤ _
      rw [Real.smoothTransition.one_of_one_le ht]
      exact Eventually.of_forall Real.smoothTransition.le_one
    exact hmax.deriv_eq_zero

theorem exists_dirichlet_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    ((show ContDiff ℝ 2 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv (by norm_num)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc 0 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have htz : t ≤ 0 ∨ 1 ≤ t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      exact ht.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
    rw [dirichlet_smoothTransition_deriv_eq_zero htz, norm_zero]
    exact le_max_right _ _

/-- A genuine smooth cutoff of the normal coordinate: it is zero below
height `ε` and one above height `2 * ε`. -/
def dirichletNormalCutoff (ε : ℝ) (z : ℂ) : ℂ :=
  (Real.smoothTransition (z.im / ε - 1) : ℂ)

theorem dirichletNormalCutoff_contDiff ε :
    ContDiff ℝ ∞ (dirichletNormalCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((Complex.imCLM.contDiff.div_const ε).sub contDiff_const))

theorem norm_dirichletNormalCutoff_le ε z :
    ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
  rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg
    (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem dirichletNormalCutoff_eq_zero  (hε : 0 < ε) 
    (hz : z.im ≤ ε) : dirichletNormalCutoff ε z = 0 := by
  simp [dirichletNormalCutoff, Real.smoothTransition.zero_of_nonpos (show z.im / ε - 1 ≤ 0 by
    have := (div_le_one hε).mpr hz
    linarith)]

theorem dirichletNormalCutoff_eq_one  (hε : 0 < ε) 
    (hz : 2 * ε ≤ z.im) : dirichletNormalCutoff ε z = 1 := by
  simp [dirichletNormalCutoff, Real.smoothTransition.one_of_one_le (show 1 ≤ z.im / ε - 1 by
    have := (le_div_iff₀ hε).mpr hz
    linarith)]

theorem dirichletNormalCutoff_fderiv ε z w :
    fderiv ℝ (dirichletNormalCutoff ε) z w =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε * w.im : ℝ) : ℂ) := by
  have hi : HasFDerivAt (fun u => u.im / ε - 1)
      (ε⁻¹ • Complex.imCLM) z := by
    have h_simpa := ((Complex.imCLM.hasFDerivAt (x := z)).mul_const ε⁻¹).sub_const 1
    simp [div_eq_mul_inv] at h_simpa ⊢
    exact h_simpa
  have ht := (show Differentiable ℝ Real.smoothTransition from
    (show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable
      (by norm_num)) (z.im / ε - 1)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (ht.hasDerivAt.comp_hasFDerivAt z hi)
  have hd' : HasFDerivAt (dirichletNormalCutoff ε)
      (Complex.ofRealCLM.comp
        (deriv Real.smoothTransition (z.im / ε - 1) • (ε⁻¹ • Complex.imCLM))) z := hd
  rw [hd'.fderiv]
  simp [div_eq_mul_inv, mul_assoc]

@[simp] theorem dirD_dirichletNormalCutoff_one ε (z : ℂ) :
    dirD (dirichletNormalCutoff ε) 1 z = 0 := by
  simp [dirD, dirichletNormalCutoff_fderiv]

theorem dirD_dirichletNormalCutoff_I ε z :
    dirD (dirichletNormalCutoff ε) Complex.I z =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε : ℝ) : ℂ) := by
  simp [dirD, dirichletNormalCutoff_fderiv]

theorem dirD_dirichletNormalCutoff_I_eq_zero  (hε : 0 < ε) 
    (hz : z.im ≤ ε ∨ 2 * ε ≤ z.im) :
    dirD (dirichletNormalCutoff ε) Complex.I z = 0 := by
  rw [dirD_dirichletNormalCutoff_I, dirichlet_smoothTransition_deriv_eq_zero (by
    rcases hz with hz | hz
    · have := (div_le_one hε).mpr hz
      exact Or.inl (by linarith)
    · have := (le_div_iff₀ hε).mpr hz
      exact Or.inr (by linarith))]
  simp

theorem norm_dirD_dirichletNormalCutoff_I_le {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) z :
    ‖dirD (dirichletNormalCutoff ε) Complex.I z‖ ≤ C / ε := by
  rw [dirD_dirichletNormalCutoff_I, Complex.norm_real, norm_div,
    Real.norm_of_nonneg hε.le]
  exact div_le_div_of_nonneg_right (hC _) hε.le

/-- The actual additional gradient term created by a normal cutoff. -/
def dirichletNormalCutoffError (ε : ℝ) (v : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletNormalCutoff ε) Complex.I z * v z

theorem dirichletNormalCutoffError_memLp {a b C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) 
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletNormalCutoffError ε v) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply hm.of_le_mul (c := C / ε) ((((dirichletNormalCutoff_contDiff ε).fderiv_right (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply continuous_const).aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖dirD (dirichletNormalCutoff ε) Complex.I z * v z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_dirD_dirichletNormalCutoff_I_le hε hC z)
      (norm_nonneg _)

theorem dirichletNormalCutoffError_slice_eq_strip {ε b : ℝ} (hε : 0 < ε)
    (hεb : 2 * ε ≤ b) v (x : ℝ) :
    (∫ t in 0..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
    ∫ t in 0..(2 * ε),
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ b),
    intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε)]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc le_rfl hεb)
  intro t ht
  simp [dirichletNormalCutoffError, (dirD_dirichletNormalCutoff_I_eq_zero hε (Or.inr (by simpa using ((lt_of_not_ge (fun h => ht.2 ⟨ht.1.1, h⟩)).le))) : dirD (dirichletNormalCutoff ε) Complex.I (x + t * Complex.I) = 0)]

/-- The full additional-gradient energy is bounded by the genuine
derivative-scale strip mass. No boundary derivative or target H² gain
is used in this cutoff estimate. -/
theorem dirichletNormalCutoffError_energy_le {a b C ε : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε ≤ b) (hC₀ : 0 ≤ C)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ x in Ioo (-a) a, ∫ t in 0..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
    C ^ 2 / ε ^ 2 *
      (∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hmi := hm.mono_measure (Measure.restrict_mono_set volume (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hεb⟩ : smoothDirichletHalfBox a (2 * ε) ⊆ smoothDirichletHalfBox a b))
  simpa only [integral_const_mul] using
    integral_mono_ae (by
      simpa [intervalIntegral.integral_of_le ((by positivity : 0 < 2 * ε).trans_le hεb).le, integral_Ioc_eq_integral_Ioo]
        using (dirichlet_halfBox_sq_integrable_real_prod (dirichletNormalCutoffError_memLp hε hC hm)).integral_prod_left) ((show Integrable (fun x : ℝ => ∫ t in 0..(2 * ε), ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) by
          simpa [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε), integral_Ioc_eq_integral_Ioo]
            using (dirichlet_halfBox_sq_integrable_real_prod hmi).integral_prod_left).const_mul (C ^ 2 / ε ^ 2)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      let L : ℝ → ℂ := fun t => x + t * Complex.I
      have hLc : Continuous L := continuous_const.add
        (Complex.ofRealCLM.continuous.mul continuous_const)
      have hvL := hv.comp hLc.continuousOn (show MapsTo L (Icc 0 (2 * ε)) (smoothDirichletClosedHalfBox a b) by
        intro t ht
        simpa [L, smoothDirichletClosedHalfBox] using
          (show |x| ≤ a ∧ 0 ≤ t ∧ t ≤ b from ⟨(abs_lt.mpr hx).le, ht.1, ht.2.trans hεb⟩))
      rw [dirichletNormalCutoffError_slice_eq_strip hε hεb]
      have h := intervalIntegral.integral_mono_on_of_le_Ioo (by positivity : 0 ≤ 2 * ε)
        ((((((((dirichletNormalCutoff_contDiff ε).fderiv_right (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply continuous_const).comp hLc).continuousOn.mul hvL).norm).pow 2).intervalIntegrable_of_Icc (by positivity) : IntervalIntegrable (fun t => ‖dirichletNormalCutoffError ε v (L t)‖ ^ 2) volume 0 (2 * ε)) (((hvL.norm.pow 2).intervalIntegrable_of_Icc (by positivity)).const_mul (C ^ 2 / ε ^ 2)) (by
          intro t _
          dsimp only [dirichletNormalCutoffError]
          rw [norm_mul, mul_pow]
          simpa [div_pow] using mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (div_nonneg hC₀ hε.le)).mpr (norm_dirD_dirichletNormalCutoff_I_le hε hC (L t))) (sq_nonneg _))
      simpa [L] using h)

/-- Fubini identifies the actual physical squared norm with its two
real coordinate integrals. The coordinate transformation has Jacobian
one, so no scale factor is introduced. -/
theorem dirichlet_halfBox_sq_integral_eq_real_prod {a b : ℝ} (hb : 0 < b)
     (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ x in Ioo (-a) a, ∫ t in 0..b,
        ‖g ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  let e := Complex.measurableEquivRealProd.symm
  have he p : e p = p.1 + p.2 * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hmeas :=
    (isOpen_smoothDirichletHalfBox a b).measurableSet
  have hi := (Complex.volume_preserving_equiv_real_prod.symm _).integral_comp e.measurableEmbedding
    ((smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2))
  rw [show (fun p => (smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2) (e p)) = (e ⁻¹' smoothDirichletHalfBox a b).indicator (fun p => ‖g (e p)‖ ^ 2) by
    funext p
    by_cases hz : e p ∈ smoothDirichletHalfBox a b <;> simp [hz], integral_indicator (hmeas.preimage e.measurable),
    integral_indicator hmeas, show e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo 0 b by
      ext ⟨x, y⟩
      simp [e, smoothDirichletHalfBox, abs_lt, and_assoc], Measure.volume_eq_prod,
    ← Measure.prod_restrict] at hi
  rw [← hi]
  simpa [he, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
    using integral_prod
      (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * Complex.I)‖ ^ 2) (dirichlet_halfBox_sq_integrable_real_prod hg)

/-- Multiplication by the actual cutoff tends to the identity in L².
The majorant is four times the original squared norm. -/
theorem dirichletNormalCutoff_weight_error_energy_tendsto_zero  
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε => ∫ z in smoothDirichletHalfBox a b,
      ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let B : ℂ → ℝ := fun z => 4 * ‖g z‖ ^ 2
  have hbound : ∀ ε : ℝ, ∀ᵐ z ∂μ,
      ‖‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2‖ ≤ B z := by
    intro ε
    exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hnorm : ‖dirichletNormalCutoff ε z - 1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by
          rw [norm_one]
          linarith [norm_dirichletNormalCutoff_le ε z])
      simpa [B, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr hnorm) (sq_nonneg ‖g z‖)
  simpa using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall (show ∀ ε : ℝ, AEStronglyMeasurable (fun z => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) μ by
        intro ε
        exact ((((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const).aestronglyMeasurable.mul
          hg.aestronglyMeasurable).norm).pow 2)) (Eventually.of_forall hbound) ((hg.integrable_norm_pow (by norm_num : 2 ≠ 0)).const_mul 4) (show ∀ᵐ z ∂μ, Tendsto (fun ε => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] 0) (𝓝 0) by
        filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
          with z hz
        have h : Tendsto (fun ε => (dirichletNormalCutoff ε z - 1) * g z)
            (𝓝[>] 0) (𝓝 ((1 - 1) * g z)) :=
          ((show Tendsto (fun ε => dirichletNormalCutoff ε z) (𝓝[>] 0) (𝓝 1) by
            apply tendsto_const_nhds.congr'
            filter_upwards [self_mem_nhdsWithin,
              (eventually_lt_nhds (half_pos hz.2.1)).filter_mono nhdsWithin_le_nhds]
              with ε hε hεz
            exact (dirichletNormalCutoff_eq_one hε (by linarith)).symm).sub
            tendsto_const_nhds).mul tendsto_const_nhds
        simpa using h.norm.pow 2)

/-- Localization may reach the bottom edge. Its actual smooth normal
cutoff is nevertheless a genuine compact interior test, because it
vanishes on a whole neighborhood of that edge. -/
theorem dirichletNormalCutoff_testFunction {a b ε : ℝ} (hε : 0 < ε)
    (η : smoothTraceTests)
    (hη : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
     (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b)) :
    TestFunction (smoothDirichletHalfBox a b)
      (fun z => η z * dirichletNormalCutoff ε z * v z) := by
  let w : ℂ → ℂ := fun z => η z * dirichletNormalCutoff ε z * v z
  refine ⟨(by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ smoothDirichletHalfBox a b
    · exact (η.property.1.contDiffAt.mul
        (dirichletNormalCutoff_contDiff ε).contDiffAt).mul
        (hs.contDiffAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))
    · apply (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
      by_cases hzε : z.im < ε
      · have hn :=
          (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzε
        filter_upwards [hn] with u hu
        simp only [dirichletNormalCutoff_eq_zero hε hu.le, mul_zero, zero_mul]
      · have hzη : z ∉ tsupport η := by
          intro hzη
          obtain ⟨hx, hy⟩ := hη hzη
          exact hz ⟨hx, hε.trans_le (le_of_not_gt hzε), hy⟩
        filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hzη] with u hu
        simp only [image_eq_zero_of_notMem_tsupport hu, zero_mul]), η.property.2.1.mul_right.mul_right, fun z hz => ?_⟩
  obtain ⟨hx, hy⟩ := hη ((tsupport_mul_subset_left.trans tsupport_mul_subset_left) hz)
  exact ⟨hx, hε.trans_le ((show tsupport w ⊆ {z : ℂ | ε ≤ z.im} by
    apply closure_minimal _ (isClosed_le continuous_const Complex.continuous_im)
    intro z hz
    by_contra h
    exact hz (by simp only [w, dirichletNormalCutoff_eq_zero hε (le_of_not_ge h), mul_zero, zero_mul])) hz), hy⟩

theorem dirichletNormalCutoff_weight_error_memLp  ε 
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (fun z => (dirichletNormalCutoff ε z - 1) * g z) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply hg.of_le_mul (c := 2) ((((dirichletNormalCutoff_contDiff ε).continuous.sub
    continuous_const).aestronglyMeasurable).mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖(dirichletNormalCutoff ε z - 1) * g z‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith [norm_dirichletNormalCutoff_le ε z])

/-- The cutoff product rule is proved at every actual interior point. -/
theorem dirichletNormalCutoff_product_dirD  ε 
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
     (hz : z ∈ smoothDirichletHalfBox a b) w :
    dirD (fun u => dirichletNormalCutoff ε u * v u) w z =
      dirichletNormalCutoff ε z * dirD v w z +
        dirD (dirichletNormalCutoff ε) w z * v z := by
  simp [dirD]
  change (fderiv ℝ (dirichletNormalCutoff ε * v) z) w = _
  rw [fderiv_mul (((dirichletNormalCutoff_contDiff ε).differentiable (by simp)) z) ((hs.differentiableOn (by simp)).differentiableAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))]
  simp
  ring

/-- The actual normal gradient of the cutoff product converges in
L² to the actual normal gradient of the original zero-boundary H¹
function. Both terms in the product rule are controlled separately. -/
theorem dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) 
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
        dirD v Complex.I z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let A : ℝ → ℂ → ℂ := fun ε z =>
    (dirichletNormalCutoff ε z - 1) * dirD v Complex.I z
  let B : ℝ → ℂ → ℂ := fun ε z => dirichletNormalCutoffError ε v z
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (show Tendsto (fun ε => 2 * (∫ z, ‖A ε z‖ ^ 2 ∂μ) + 2 * (∫ z, ‖B ε z‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) by
    simpa [A, B, μ] using
      (tendsto_const_nhds.mul (dirichletNormalCutoff_weight_error_energy_tendsto_zero hg)).add (tendsto_const_nhds.mul (show Tendsto (fun ε => ∫ z in smoothDirichletHalfBox a b, ‖dirichletNormalCutoffError ε v z‖ ^ 2) (𝓝[>] 0) (𝓝 0) by
        obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
        apply (show Tendsto (fun ε => ∫ x in Ioo (-a) a, ∫ t in 0..b, ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (𝓝[>] 0) (𝓝 0) by
          obtain ⟨C, hC₀, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by
            have h : Tendsto (fun ε => 4 * C ^ 2 *
                ((∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
                  ‖v (x + t * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
                (𝓝[>] 0) (𝓝 ((4 * C ^ 2) * 0)) :=
              tendsto_const_nhds.mul ((show Tendsto (fun ε => (∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε, ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2) (𝓝[>] 0) (𝓝 0) by
                apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
                  (by
                    let B : ℝ → ℝ := fun x => ∫ t in 0..b,
                      ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2
                    have hB : Integrable B (volume.restrict (Ioo (-a) a)) := by
                      simpa [B, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
                        using (dirichlet_halfBox_sq_integrable_real_prod hg).integral_prod_left
                    have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
                        (fun x : ℝ => ∫ t in 0..ε,
                          ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
                        (volume.restrict (Ioo (-a) a)) := by
                      filter_upwards [self_mem_nhdsWithin,
                        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
                      have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
                        fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hεb⟩
                      have hgm := hg.mono_measure (Measure.restrict_mono_set volume hsub)
                      have hc : Integrable (fun x : ℝ => ∫ t in 0..ε,
                          ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
                          (volume.restrict (Ioo (-a) a)) := by
                        simpa [intervalIntegral.integral_of_le (show 0 ≤ ε from hε.le), integral_Ioc_eq_integral_Ioo] using (dirichlet_halfBox_sq_integrable_real_prod hgm).integral_prod_left
                      exact hc.aestronglyMeasurable
                    have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
                        ‖∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ B x := by
                      filter_upwards [self_mem_nhdsWithin,
                        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
                      filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
                      have hε₀ := hε
                      have hnon : 0 ≤ ∫ t in 0..ε,
                          ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2 := by
                        rw [intervalIntegral.integral_of_le hε₀.le]
                        exact integral_nonneg (fun _ => sq_nonneg _)
                      rw [Real.norm_of_nonneg hnon]
                      exact intervalIntegral.integral_mono_interval le_rfl hε₀.le hεb.le
                        (Eventually.of_forall fun _ => sq_nonneg _) ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr (hx.integrable_norm_pow (by norm_num : 2 ≠ 0)))
                    have hlim : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a), Tendsto
                        (fun ε : ℝ => ∫ t in (0 : ℝ)..ε,
                          ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2)
                        (𝓝[>] 0) (𝓝 0) := by
                      filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
                      exact (by
                        have h := (intervalIntegral.continuousOn_primitive_interval' ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr (hx.integrable_norm_pow (by norm_num : 2 ≠ 0))) left_mem_uIcc) 0 left_mem_uIcc
                        rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb] at h
                        simpa using
                          h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
                    simpa using (MeasureTheory.tendsto_integral_filter_of_dominated_convergence (f := fun _ : ℝ => (0 : ℝ)) B hmeas hbound hB hlim))
                · filter_upwards [self_mem_nhdsWithin] with ε hε
                  apply div_nonneg _ (sq_nonneg _)
                  apply integral_nonneg
                  intro x
                  change 0 ≤ ∫ t in 0..ε, ‖v (x + t * Complex.I)‖ ^ 2
                  rw [intervalIntegral.integral_of_le hε.le]
                  exact integral_nonneg (fun _ => sq_nonneg _)
                · filter_upwards [self_mem_nhdsWithin,
                    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
                  exact dirichlet_halfBox_strip_mass_le hv hs hz hm hg ⟨hε, hεb.le⟩).comp (by
                apply tendsto_nhdsWithin_iff.mpr
                constructor
                · simpa using
                    (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
                      Tendsto (fun ε => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝 (2 * 0)))
                · filter_upwards [self_mem_nhdsWithin] with ε hε
                  have hε₀ : 0 < ε := hε
                  show 0 < 2 * ε
                  positivity))
            have heq : ∀ ε : ℝ, C ^ 2 / ε ^ 2 *
                (∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
                  ‖v (x + t * Complex.I)‖ ^ 2) =
                4 * C ^ 2 * ((∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
                  ‖v (x + t * Complex.I)‖ ^ 2) / (2 * ε) ^ 2) := by
              intro ε
              by_cases hε : ε = 0
              · simp [hε]
              · have hfactor m : C ^ 2 / ε ^ 2 * m =
                    4 * C ^ 2 * (m / (2 * ε) ^ 2) := by
                  field_simp [hε]
                  ring
                exact hfactor _
            simpa [← heq] using
              (h : Tendsto (fun ε => 4 * C ^ 2 *
                ((∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
                  ‖v (x + t * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
                (𝓝[>] 0) (𝓝 ((4 * C ^ 2) * 0))))
          · exact Eventually.of_forall fun ε => integral_nonneg fun x =>
              intervalIntegral.integral_nonneg_of_forall hb.le (fun _ => sq_nonneg _)
          · filter_upwards [self_mem_nhdsWithin,
              (eventually_lt_nhds (half_pos hb)).filter_mono nhdsWithin_le_nhds]
              with ε hε hεb
            exact dirichletNormalCutoffError_energy_le hε (by linarith) hC₀ hC hv hm).congr'
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (dirichlet_halfBox_sq_integral_eq_real_prod hb
          (dirichletNormalCutoffError_memLp hε hC hm)).symm)))
  · exact Eventually.of_forall fun ε => integral_nonneg fun z => sq_nonneg _
  · obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAm : MemLp (A ε) 2 μ := dirichletNormalCutoff_weight_error_memLp ε hg
    have hBm := dirichletNormalCutoffError_memLp hε hC hm
    have hsum : (fun z => A ε z + B ε z) =ᵐ[μ]
        (fun z => dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z) := by
      filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
        with z hzV
      rw [dirichletNormalCutoff_product_dirD ε hs hzV]
      dsimp only [A, B, dirichletNormalCutoffError]
      ring
    have hAi := hAm.integrable_norm_pow (by norm_num : 2 ≠ 0)
    have hBi := hBm.integrable_norm_pow (by norm_num : 2 ≠ 0)
    simpa only [Pi.add_apply, integral_add (hAi.const_mul 2) (hBi.const_mul 2), integral_const_mul]
      using (integral_mono_ae (((hAm.add hBm).ae_eq hsum).integrable_norm_pow (by norm_num : 2 ≠ 0)) ((hAi.const_mul 2).add (hBi.const_mul 2)) (show (fun z => ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z - dirD v Complex.I z‖ ^ 2) ≤ᵐ[μ] (fun z => 2 * ‖A ε z‖ ^ 2 + 2 * ‖B ε z‖ ^ 2) by
        filter_upwards [hsum] with z hzsum
        rw [← hzsum]
        have hn' := (sq_le_sq₀ (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le (A ε z) (B ε z))
        nlinarith [sq_nonneg (‖A ε z‖ - ‖B ε z‖)]))

theorem dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero 
    
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hg : MemLp (dirD v 1) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) 1 z -
        dirD v 1 z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  apply (dirichletNormalCutoff_weight_error_energy_tendsto_zero hg).congr'
  exact Eventually.of_forall fun ε => by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    rw [dirichletNormalCutoff_product_dirD ε hs hz, dirD_dirichletNormalCutoff_one]
    congr 2; ring

end PolyaNeumann

end
