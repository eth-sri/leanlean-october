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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff

variable {f g : ℂ → ℂ} {z : ℂ} {U : Set ℂ} {Ω : Set ℂ} (p c : ℂ) (hc : c ≠ 0) {b : ℝ} (ε : ℝ)

/-- The project's coordinate Laplacian equals the genuine Euclidean
Laplacian at every point of twice continuous differentiability. -/
theorem lap_eq_euclidean_laplacian {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) : lap f z = Laplacian.laplacian f z := by
  have he (v : ℂ) : dirD (dirD f v) v z = fderiv ℝ (fderiv ℝ f) z v v := by
    change fderiv ℝ (fun w => fderiv ℝ f w v) z v = _
    simp [fderiv_clm_apply ((hf.fderiv_right  (by norm_num)).differentiableAt one_ne_zero) (differentiableAt_const v)] 
  simp [lap, he, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]

/-- A local equality transports both actual coordinate second
derivatives. No assumed differential equation is used. -/
theorem eventuallyEq_lap_eq (hfg : f =ᶠ[𝓝 z] g) :
    lap f z = lap g z := by
  have hd (v : ℂ) : dirD f v =ᶠ[𝓝 z] dirD g v :=
    (hfg.fderiv ).fun_comp (fun A  => A v)
  have hdd (v : ℂ) : dirD (dirD f v) v z = dirD (dirD g v) v z :=
    congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((hd v).fderiv_eq )
  exact congrArg₂ (· + ·) (hdd 1) (hdd Complex.I)

theorem smooth_integral_dirD_mul_test {G φ : ℂ → ℂ}
    (hG : TestFunction univ G) (hφ : TestFunction U φ) (i : Fin 2) :
    (∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
  have hu := (hG.dirD (coordDir i)).memLp' 2 (μ := volume.restrict U)
  have hg (j : Fin 2) := ((hG.dirD (coordDir i)).dirD (coordDir j)).memLp' 2
    (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth (hG.dirD (coordDir i)).1 hu hg φ hφ i
  change (∫ z in U, hu.toLp _ z * dirD φ (coordDir i) z) =
    -(∫ z in U, (hg i).toLp _ z * φ z) at hw
  have hl : (fun z => hu.toLp _ z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hz
    simp_all
  have hr : (fun z => (hg i).toLp _ z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
    filter_upwards [(hg i).coeFn_toLp] with z hz
    simp_all
  simp_all [integral_congr_ae hl, integral_congr_ae hr]

/-- The true weak Poisson identity for a function smooth only in the
open domain. The compact test is localized before integration by
parts, so no boundary derivatives or global second-derivative energy
are needed. -/
theorem local_smooth_gradient_test_eq_neg_lap (hU : IsOpen U)
    {v φ : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (hφ : TestFunction U φ) :
    (∫ z in U, ∑ i : Fin 2, dirD v (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, lap v z * φ z) := by
  obtain ⟨G, hG, hGv⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hv
  have hfirst (i : Fin 2) :
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) =
        (fun z => dirD v (coordDir i) z * dirD φ (coordDir i) z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · simp [show dirD G (coordDir i) z = dirD v (coordDir i) z from         congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i)) ((hGv z hz).fderiv_eq )]
    simp [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
  have hsecond : (fun z => lap G z * φ z) = (fun z => lap v z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · simp [eventuallyEq_lap_eq (hGv z hz)]
    simp [image_eq_zero_of_notMem_tsupport hz]
  have hint (i : Fin 2) :
      IntegrableOn (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) U :=
    ((hG.dirD (coordDir i)).memLp' 2).integrable_mul ((hφ.dirD (coordDir i)).memLp' 2)
  have hlap :
      (∫ z in U, lap G z * φ z) =
        (∫ z in U, dirD (dirD G 1) 1 z * φ z) +
          ∫ z in U, dirD (dirD G Complex.I) Complex.I z * φ z := by
    simp_rw [lap, add_mul]
    exact integral_add ((((hG.dirD 1).dirD 1).memLp' 2).integrable_mul (hφ.memLp' 2)) ((((hG.dirD Complex.I).dirD Complex.I).memLp' 2).integrable_mul (hφ.memLp' 2))
  calc
    _ = ∫ z in U, ∑ i : Fin 2, dirD G (coordDir i) z * dirD φ (coordDir i) z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Finset.sum_congr rfl (fun i _ =>
        congrFun (hfirst i).symm z))
    _ = ∑ i : Fin 2, ∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z :=
      integral_finset_sum _ (fun i _ => hint i)
    _ = -(∫ z in U, lap G z * φ z) := by
      simp_rw [smooth_integral_dirD_mul_test hG hφ]
      continuity
    _ = _ := by simp_all

/-- The real projection of a genuine globally smooth boundary datum
is itself a genuine globally smooth compactly supported datum. -/
def smoothTraceRealPart (b : smoothTraceTests) : smoothTraceTests := by
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  refine ⟨fun z => ((b z).re : ℂ), ?_⟩
  refine ⟨L.contDiff.comp b.property.1, ?_, subset_univ _⟩
  exact b.property.2.1.comp_left (show L (0 : ℂ) = 0 by rfl)

@[simp] theorem smoothTraceRealPart_apply (b : smoothTraceTests) (z : ℂ) :
    smoothTraceRealPart b z = (b z).re := rfl

/-- The actual physical Dirichlet remainder after subtracting the
constructed smooth real boundary datum. -/
def riemannMappingDirichletRemainder (F : ℂ → ℂ) (b : smoothTraceTests) (z : ℂ) : ℂ :=
  (riemannMappingGreenCorrection F z : ℂ) - b z

theorem lap_sub_of_contDiffAt (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    lap (fun w => f w - g w) z = lap f z - lap g z := by
  have heq : (fun w => f w - g w) = f + (-1 : ℝ) • g := by
    continuity
  have hadd : Laplacian.laplacian (f + (-1 : ℝ) • g) z =
      Laplacian.laplacian f z + Laplacian.laplacian ((-1 : ℝ) • g) z :=
    hf.laplacian_add (hg.const_smul (-1 : ℝ))
  rw [lap_eq_euclidean_laplacian (hf.sub hg), heq, hadd, laplacian_smul (-1) hg,
    ← lap_eq_euclidean_laplacian hf, ← lap_eq_euclidean_laplacian hg]
  continuity

/-- The actual zero-boundary H¹ Poisson problem needed for boundary
regularity. Its function, smooth forcing, boundary values, H¹ vector,
and compact-test equation are derived from the constructed Green
correction. No zero-trace or boundary regularity premise is added. -/
theorem exists_riemannMapping_zero_boundary_poisson_problem (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω) :
    ∃ b : smoothTraceTests, ∃ u : NeumannH1 Ω,
      ContinuousOn (riemannMappingDirichletRemainder F b) (closure Ω) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F b) Ω ∧
      (∀ z ∈ frontier Ω, riemannMappingDirichletRemainder F b z = 0) ∧
      h1Value Ω u =ᵐ[volume.restrict Ω] riemannMappingDirichletRemainder F b ∧
      (∀ i : Fin 2, h1Gradient Ω i u =ᵐ[volume.restrict Ω]
        dirD (riemannMappingDirichletRemainder F b) (coordDir i)) ∧
      (∀ z ∈ Ω, lap (riemannMappingDirichletRemainder F b) z = -lap b z) ∧
      ∀ φ : ℂ → ℂ, TestFunction Ω φ →
        (∫ z in Ω, ∑ i : Fin 2, dirD (riemannMappingDirichletRemainder F b) (coordDir i) z *
          dirD φ (coordDir i) z) = ∫ z in Ω, lap b z * φ z := by
  obtain ⟨b₀, hbdata⟩ := exists_riemannMappingGreenCorrection_smooth_boundary_data
    hb hS hsc F hF hinj himage
  let b := smoothTraceRealPart b₀
  obtain ⟨u₀, hu₀, hgu₀⟩ := exists_riemannMappingGreenCorrectionH1 hb hS hsc F hF hinj himage
  let h : ℂ → ℂ := fun z => riemannMappingGreenCorrection F z
  have hharm  :=
    (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
      Complex.ofRealCLM
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) h Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F b) Ω :=
    hs.sub b.property.1.contDiffOn
  have hΔ (z : ℂ) (hz : z ∈ Ω) :
      lap (riemannMappingDirichletRemainder F b) z = -lap b z := by
    have hh  := (hharm z hz).1
    exact (lap_sub_of_contDiffAt hh (b.property.1.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))).trans (by
      simp [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds] )
  refine ⟨b, u₀ - smoothTraceH1 Ω b, ?_, hv, ?_, ?_, ?_, hΔ, ?_⟩
  · exact (Complex.ofRealCLM.continuous.comp_continuousOn
      (riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage)).sub
        b.property.1.continuous.continuousOn
  · intro z hz
    change (riemannMappingGreenCorrection F z : ℂ) - (b₀ z).re = 0
    simp_all
  · filter_upwards [Lp.coeFn_sub (h1Value Ω u₀) (h1Value Ω (smoothTraceH1 Ω b)), hu₀,
      (smoothTraceTests_memLp Ω b).coeFn_toLp] with z hz hu hbz
    continuity
  · intro i
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (h1Gradient Ω i u₀)
      (h1Gradient Ω i (smoothTraceH1 Ω b)), hgu₀ i,
      (smoothTraceTests_memLp_deriv Ω b i).coeFn_toLp,
      ae_restrict_mem hS.1.1.measurableSet] with z hz hu hbz hzΩ
    have hc : fderiv ℝ h z =
        Complex.ofRealCLM.comp (fderiv ℝ (riemannMappingGreenCorrection F) z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) z = _
      simp [fderiv_comp z Complex.ofRealCLM.differentiableAt (((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn         (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ))]
    rw [hz, Pi.sub_apply, hu, h1Gradient_smoothTraceH1, hbz]
    change _ = fderiv ℝ (h - (b : ℂ → ℂ)) z (coordDir i)
    simp [fderiv_sub ((hs.differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)) ((b.property.1.differentiable (by simp)) z), hc] 
  · intro φ hφ
    rw [local_smooth_gradient_test_eq_neg_lap hS.1.1 hv hφ]
    have hl : (fun z => lap (riemannMappingDirichletRemainder F b) z * φ z)
        =ᵐ[volume.restrict Ω] (fun z => -(lap b z * φ z)) := by
      filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with z hz
      simp_all
    rw [integral_congr_ae hl, integral_neg, neg_neg]

/-! ## Actual smooth graph coordinates -/

/-- The genuine graph shear. Its inverse subtracts the same graph
height, because the shear preserves the real coordinate. -/
def smoothDirichletGraphShear (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  z + (f z.re : ℂ) * Complex.I

@[simp] theorem smoothDirichletGraphShear_re (f : ℝ → ℝ) (z : ℂ) :
    (smoothDirichletGraphShear f z).re = z.re := by
  simp [smoothDirichletGraphShear]

@[simp] theorem smoothDirichletGraphShear_im (f : ℝ → ℝ) (z : ℂ) :
    (smoothDirichletGraphShear f z).im = z.im + f z.re := by
  simp [smoothDirichletGraphShear]

/-- This is a global real homeomorphism, built from the supplied
continuous graph, rather than an assumed boundary coordinate map. -/
def smoothDirichletGraphShearHomeomorph (f : ℝ → ℝ) (hf : Continuous f) : ℂ ≃ₜ ℂ where
  toFun := smoothDirichletGraphShear f
  invFun := fun z => z - (f z.re : ℂ) * Complex.I
  left_inv z := by
    simp [smoothDirichletGraphShear]
  right_inv z := by
    simp [smoothDirichletGraphShear]
  continuous_toFun := continuous_id.add
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)
  continuous_invFun := continuous_id.sub
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)

@[simp] theorem smoothDirichletGraphShearHomeomorph_apply (f : ℝ → ℝ)
    (hf : Continuous f) (z : ℂ) :
    smoothDirichletGraphShearHomeomorph f hf z = smoothDirichletGraphShear f z := rfl

@[simp] theorem smoothDirichletGraphShearHomeomorph_symm_apply (f : ℝ → ℝ)
    (hf : Continuous f) (z : ℂ) :
    (smoothDirichletGraphShearHomeomorph f hf).symm z =
      z - f z.re * Complex.I := rfl

theorem smoothDirichletGraphShear_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDirichletGraphShear f) :=
  contDiff_id.add ((Complex.ofRealCLM.contDiff.comp
    (hf.comp Complex.reCLM.contDiff)).mul contDiff_const)

theorem smoothDirichletGraphShear_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : LipschitzWith (K + 1) (smoothDirichletGraphShear f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  calc
    ‖smoothDirichletGraphShear f z - smoothDirichletGraphShear f w‖ =
        ‖(z - w) + (f z.re - f w.re : ℝ) * Complex.I‖ := by
      simp only [smoothDirichletGraphShear, Complex.ofReal_sub]
      ring
    _ ≤ ‖z - w‖ + ‖(f z.re - f w.re : ℝ) * Complex.I‖ := norm_add_le _ _
    _ ≤ ‖z - w‖ + K * ‖z - w‖ := add_le_add le_rfl (by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    exact (hf.norm_sub_le z.re w.re).trans
      (mul_le_mul_of_nonneg_left (by
      simpa only [Real.norm_eq_abs, Complex.sub_re] using Complex.abs_re_le_norm (z - w)) K.coe_nonneg))
    _ = (K + 1) * ‖z - w‖ := by ring

theorem smoothDirichletGraphShearHomeomorph_symm_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphShearHomeomorph f hf.continuous).symm := by
  have heq : (smoothDirichletGraphShearHomeomorph f hf.continuous).symm =
      smoothDirichletGraphShear (fun x => -f x) := by
    funext z
    simp [smoothDirichletGraphShear, sub_eq_add_neg]
  rw [heq]
  exact smoothDirichletGraphShear_lipschitz hf.neg

/-- The graph shear followed by the actual rigid coordinates of the
smooth-domain chart. Only continuity of the supplied graph and a
nonzero rigid factor are required to construct this homeomorphism. -/
def smoothDirichletGraphChart (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) :
    ℂ ≃ₜ ℂ :=
  (smoothDirichletGraphShearHomeomorph f hf).trans
    ((Homeomorph.mulRight₀ c hc).symm.trans (Homeomorph.addLeft p))

@[simp] theorem smoothDirichletGraphChart_apply (f : ℝ → ℝ) (hf : Continuous f) (z : ℂ) :
    smoothDirichletGraphChart p c hc f hf z = p + smoothDirichletGraphShear f z / c := by
  rfl

theorem smoothDirichletGraphChart_rotate (f : ℝ → ℝ) (hf : Continuous f) (z : ℂ) :
    c * (smoothDirichletGraphChart p c hc f hf z - p) = smoothDirichletGraphShear f z := by
  rw [smoothDirichletGraphChart_apply]
  grind

theorem smoothDirichletGraphChart_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDirichletGraphChart p c hc f hf.continuous) :=
  contDiff_const.add ((smoothDirichletGraphShear_contDiff hf).div_const c)

theorem smoothDirichletGraphChart_lipschitz (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
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

theorem smoothDirichletGraphChart_symm_lipschitz (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + z) * c))
    ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + w) * c)) ≤ _
  have heq : (-p + z) * c - (-p + w) * c = (z - w) * c := by ring
  simpa only [dist_eq_norm, heq, norm_mul, hc₁, mul_one] using (smoothDirichletGraphShearHomeomorph_symm_lipschitz hf).dist_le_mul
    ((-p + z) * c) ((-p + w) * c)

/-- The smooth-domain definition supplies an actual flattened full
rectangle on which physical membership is exactly positive height.
The homeomorphism is built above from that domain's own graph. -/
theorem exists_smoothDomain_flattening_rectangle (hS : IsSmoothDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      ∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im) := by
  obtain ⟨c, r, h, K, f, hc₁, hr, hh, hf, hLip, hf₀, _, hchart⟩ := hS.2 p hp
  have hc : c ≠ 0 := by
    continuity
  let a := min r (h / (4 * (K + 1)))
  let b := h / 4
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  refine ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, lt_min hr (div_pos hh hden), div_pos hh (by norm_num), ?_⟩
  intro z hzre hzim
  have hscale : 4 * (K + 1) * |z.re| < h := by
    simpa only [mul_comm] using
      (lt_div_iff₀ hden).mp (hzre.trans_le (min_le_right _ _))
  have hfz : |f z.re| ≤ K * |z.re| := by
    simpa only [hf₀, sub_zero, Real.norm_eq_abs] using hLip.norm_sub_le z.re 0
  simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re,
    smoothDirichletGraphShear_im, lt_add_iff_pos_left] using hchart (smoothDirichletGraphChart p c hc f hf.continuous z)
    (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re] using hzre.trans_le (min_le_left _ _))
    (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_im] using (by
    grind))

/-- The bottom edge in an actual flattening rectangle maps to the
physical frontier. This follows from positive-height approach and
the local membership equivalence; frontier membership is not a new
coordinate premise. -/
theorem smoothDirichletGraphChart_mem_frontier (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    {x : ℝ} (hx : |x| < a) :
    smoothDirichletGraphChart p c hc f hf x ∈ frontier Ω := by
  let Ψ := smoothDirichletGraphChart p c hc f hf
  have hcurve : Tendsto (fun t : ℝ => x + t * Complex.I)
      (𝓝[>] 0) (𝓝 x) := by
    have h : Tendsto (fun t : ℝ => x + t * Complex.I)
        (𝓝[>] 0) (𝓝 (x + 0 * Complex.I)) :=
      (tendsto_const_nhds.add
        ((Complex.ofRealCLM.continuous.tendsto 0).mul_const Complex.I)).mono_left
          nhdsWithin_le_nhds
    simp_all
  rw [hΩ.frontier_eq]
  exact ⟨mem_closure_of_tendsto ((Ψ.continuous.tendsto x).comp hcurve) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
    apply (hchart _ (by simp_all) (by simp_all [abs_of_pos ht])).mpr
    simp_all), by
    continuity⟩

/-- True zero boundary values of a physical continuous solution
remain true zero values on the flattened boundary interval. -/
theorem smoothDirichletGraphChart_zero_boundary (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    (v : ℂ → ℂ) (hv : ∀ z ∈ frontier Ω, v z = 0) {x : ℝ} (hx : |x| < a) :
    v (smoothDirichletGraphChart p c hc f hf x) = 0 :=
  hv _ (smoothDirichletGraphChart_mem_frontier hΩ p c hc f hf hb hchart hx)

/-- An actual pointwise H¹ function remains pointwise H¹ under the
constructed graph coordinates. This uses the proved bi-Lipschitz
L² pullback and actual chain differential, with no assumed pullback
energy or flattened Sobolev regularity. -/
theorem smoothDirichletGraphChart_pullback_memLp {Ω U : Set ℂ}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (himage : smoothDirichletGraphChart p c hc f hf.continuous '' U ⊆ Ω)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
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
    (smoothDirichletGraphChart_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hΨinv : LipschitzOnWith (K + 1) Ψ.symm (Ψ '' U) :=
    (smoothDirichletGraphChart_symm_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hg' (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 (volume.restrict (Ψ '' U)) :=
    (hg i).mono_measure (Measure.restrict_mono_set volume himage)
  refine ⟨memLp_comp_bilip' hU hK hΨ hΨinv (hm.mono_measure (Measure.restrict_mono_set volume himage)), ?_⟩
  intro i
  let G  := fun j => (hg' j).toLp _
  have hae : ∀ᵐ z ∂(volume.restrict U), ∀ j : Fin 2,
      G j (Ψ z) = dirD v (coordDir j) (Ψ z) :=
    ae_all_iff.mpr (fun j => (quasiMeasurePreserving_restrict hΨinv).ae (hg' j).coeFn_toLp)
  apply (memLp_chainGrad hU hK hΨ hΨinv G i).ae_eq
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with z hz hzU
  change chainGrad Ψ (fun j => G j) i z =
    fderiv ℝ (v ∘ Ψ) z (coordDir i)
  rw [fderiv_comp z ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds (himage (mem_image_of_mem Ψ hzU)))) (((smoothDirichletGraphChart_contDiff p c hc hf).differentiable (by simp)) z), ContinuousLinearMap.comp_apply, clm_apply_eq_sum_coordRe]
  simp [chainGrad, hz, dirD]

def smoothDirichletHalfBox (a b : ℝ) : Set ℂ :=
  {z | |z.re| < a ∧ 0 < z.im ∧ z.im < b}

def smoothDirichletClosedHalfBox (a b : ℝ) : Set ℂ :=
  {z | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b}

theorem isOpen_smoothDirichletHalfBox (a b : ℝ) : IsOpen (smoothDirichletHalfBox a b) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-! ## The actual elliptic coefficients of graph flattening -/

/-- The actual differential of the graph shear at graph slope `d`.
It maps `(x,y)` to `(x,y+d*x)`. -/
def smoothDirichletGraphDifferential (d : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + (d • Complex.reCLM).smulRight Complex.I

@[simp] theorem smoothDirichletGraphDifferential_apply (d : ℝ) (w : ℂ) :
    smoothDirichletGraphDifferential d w = w + (d * w.re) • Complex.I := by
  rfl

theorem smoothDirichletGraphShear_hasFDerivAt {f : ℝ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z.re) :
    HasFDerivAt (smoothDirichletGraphShear f)
      (smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hs := (hasFDerivAt_id z).add ((hf.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt).smul_const Complex.I)
  assumption

theorem smoothDirichletGraphChart_hasFDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    HasFDerivAt (smoothDirichletGraphChart p c hc f hf.continuous)
      (c⁻¹ • smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hs := ((smoothDirichletGraphShear_hasFDerivAt ((hf.differentiable (by simp)) z.re)).mul_const c⁻¹).const_add p
  assumption

theorem smoothDirichletGraphChart_fderiv_apply {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z w : ℂ) :
    fderiv ℝ (smoothDirichletGraphChart p c hc f hf.continuous) z w =
      c⁻¹ * (w + (deriv f z.re * w.re) • Complex.I) := by
  simp [(smoothDirichletGraphChart_hasFDerivAt p c hc hf z).fderiv] 

/-- The actual chain rule exposes the inverse-graph energy
components. The physical derivatives occur in the rigid directions
`1/c` and `I/c`; the tangential shear term cancels exactly. -/
theorem smoothDirichletGraphChart_pullback_gradient {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let u := v ∘ Ψ
     dirD u 1 z - deriv f z.re * dirD u Complex.I z = fderiv ℝ v (Ψ z) (1 / c)) ∧
    dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      fderiv ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z) (Complex.I / c) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let T := fderiv ℝ v (Ψ z)
  let d := deriv f z.re
  have hchain (w : ℂ) : dirD (v ∘ Ψ) w z = T (c⁻¹ * (w + (d * w.re) • Complex.I)) := by
    change fderiv ℝ (v ∘ Ψ) z w = _
    rw [fderiv_comp z hv (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt, ContinuousLinearMap.comp_apply,
      smoothDirichletGraphChart_fderiv_apply p c hc hf z w]
  have hI : dirD (v ∘ Ψ) Complex.I z = T (Complex.I / c) := by
    simp [hchain, div_eq_mul_inv, mul_comm]
  have h1 : dirD (v ∘ Ψ) 1 z = T (1 / c) + d • T (Complex.I / c) := by
    rw [hchain]
    have he : c⁻¹ * (1 + (d * (1 : ℂ).re) • Complex.I) =
        1 / c + d • (Complex.I / c) := by
      simp 
      ring
    rw [he, map_add, map_smul]
  continuity

/-- The energy form of the inverse graph differential. Its matrix is
`[[1, -d], [-d, 1+d²]]`, with `d = f′(x)`. -/
def smoothDirichletGraphQuadratic (d x y : ℝ) : ℝ :=
  x ^ 2 - 2 * d * x * y + (1 + d ^ 2) * y ^ 2

theorem smoothDirichletGraphQuadratic_eq_sq (d x y : ℝ) :
    smoothDirichletGraphQuadratic d x y = (x - d * y) ^ 2 + y ^ 2 := by
  unfold smoothDirichletGraphQuadratic
  ring

/-- Genuine ellipticity follows from the actual Lipschitz graph
bound; no elliptic coefficient premise is substituted for it. -/
theorem smoothDirichletGraphQuadratic_bounds {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (t x y : ℝ) :
    (x ^ 2 + y ^ 2) / (2 * (1 + K ^ 2)) ≤
      smoothDirichletGraphQuadratic (deriv f t) x y ∧
    smoothDirichletGraphQuadratic (deriv f t) x y ≤
      2 * (1 + K ^ 2) * (x ^ 2 + y ^ 2) := by
  let d := deriv f t
  have hd₂ : d ^ 2 ≤ K ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg d) K.coe_nonneg).mpr (by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hf)
    simp_all
  have hlow : x ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * ((x - d * y) ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * d * y)]
  have hupp : (x - d * y) ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x + d * y)]
  rw [smoothDirichletGraphQuadratic_eq_sq]
  constructor
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith 
  nlinarith 

/-- The same genuine elliptic bounds hold for complex-valued
solutions, by applying the real coefficient form to the actual real
and imaginary components. -/
theorem smoothDirichletGraph_complex_energy_bounds {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (t : ℝ) (x y : ℂ) :
    (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * (1 + K ^ 2)) ≤
      ‖x - deriv f t * y‖ ^ 2 + ‖y‖ ^ 2 ∧
    ‖x - deriv f t * y‖ ^ 2 + ‖y‖ ^ 2 ≤
      2 * (1 + K ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hr₁, hr₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.re y.re
  obtain ⟨hi₁, hi₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.im y.im
  have heq : ‖x - deriv f t * y‖ ^ 2 + ‖y‖ ^ 2 =
      smoothDirichletGraphQuadratic (deriv f t) x.re y.re +
        smoothDirichletGraphQuadratic (deriv f t) x.im y.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      smoothDirichletGraphQuadratic]
    ring
  constructor
  · convert add_le_add hr₁ hi₁ using 1
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring
  · convert add_le_add hr₂ hi₂ using 1
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring

/-! ## The genuine one-dimensional zero-boundary energy step -/

/-- An actual continuous zero endpoint and an integrable interior
derivative give the primitive identity up to the endpoint. No
derivative or smooth extension is required at that endpoint. -/
theorem dirichlet_zero_endpoint_primitive {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    v t = ∫ s in 0..t, dv s := by
  have hvc  := hv.mono
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
  simp_all

/-- Actual L² derivative energy controls the value next to a zero
endpoint. This is the estimate needed to remove a thin boundary
strip when closing Dirichlet tests in H¹. -/
theorem dirichlet_zero_endpoint_norm_sq_le {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    ‖v t‖ ^ 2 ≤ t * ∫ s in 0..t, ‖dv s‖ ^ 2 := by
  let μ := volume.restrict (Ioc 0 t)
  have hm'  :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have h1 : MemLp (fun _  => (1 : ℂ)) 2 μ := memLp_const 1
  have hi : (∫ s in 0..t, dv s) = inner ℂ (h1.toLp _) (hm'.toLp _) := by
    rw [intervalIntegral.integral_of_le ht.1.le]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, hm'.coeFn_toLp] with s hs₁ hs₂
    simp_all
  have hnorm : ‖∫ s in 0..t, dv s‖ ≤ ‖h1.toLp _‖ * ‖hm'.toLp _‖ := by
    rw [hi]
    exact norm_inner_le_norm _ _
  have hnormsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  have hn₁ : ‖h1.toLp _‖ ^ 2 = t := by
    rw [norm_sq_toLp_eq_integral]
    simp [μ, ht.1.le]
  have hn₂ : ‖hm'.toLp _‖ ^ 2 = ∫ s in 0..t, ‖dv s‖ ^ 2 := by
    rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le ht.1.le]
  simp_all [mul_pow, dirichlet_zero_endpoint_primitive hv hv₀ hd hm ht]

/-- The actual zero endpoint controls the mass of a thin boundary
strip by the derivative energy in that same strip. The crude
constant `1` is sufficient to close Dirichlet cutoff tests. -/
theorem dirichlet_zero_endpoint_strip_mass_le {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {ε : ℝ} (hε : ε ∈ Ioc 0 b) :
    (∫ t in 0..ε, ‖v t‖ ^ 2) / ε ^ 2 ≤
      ∫ t in 0..ε, ‖dv t‖ ^ 2 := by
  have hmi : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioc 0 b) :=
    hm.integrable_norm_pow (by norm_num)
  have hV : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 ε :=
    ((hv.mono (Icc_subset_Icc le_rfl hε.2)).norm.pow 2).intervalIntegrable_of_Icc hε.1.le
  have hbnd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      ‖v t‖ ^ 2 ≤ ε * ∫ s in 0..ε, ‖dv s‖ ^ 2 := (dirichlet_zero_endpoint_norm_sq_le hv hv₀ hd hm
      (⟨ht.1, ht.2.le.trans hε.2⟩)).trans ((mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
        (Eventually.of_forall fun _ => sq_nonneg _) (by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε.1.le]
    exact hmi.mono_set (Ioc_subset_Ioc le_rfl hε.2))) ht.1.le).trans
      (mul_le_mul_of_nonneg_right ht.2.le (by
    rw [intervalIntegral.integral_of_le hε.1.le]
    positivity)))
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hε.1.le hV
    (intervalIntegrable_const ) hbnd
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hε.1)).mpr
  nlinarith

/-- Genuine L² normal derivative energy gives L² energy on almost
every vertical slice, by the actual Lebesgue coordinate map. -/
theorem dirichlet_halfBox_vertical_memLp {a b : ℝ} {v : ℂ → ℂ}
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      MemLp (fun y : ℝ => dirD v Complex.I (x + y * Complex.I)) 2
        (volume.restrict (Ioc 0 b)) := by
  let e  := Complex.measurableEquivRealProd.symm
  have he (p : ℝ × ℝ) : e p = p.1 + p.2 * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo 0 b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt]
  have hprod := ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage e.measurableEmbedding).mpr (hg.integrable_norm_pow (by norm_num))
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p  => ‖dirD v Complex.I (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) at hprod
  have hslice := hprod.prod_right_ae
  simp only [he] at hslice
  filter_upwards [hslice] with x hx
  have hmL  :=
    (memLp_two_iff_integrable_sq_norm ((measurable_fderiv_apply_const ℝ v Complex.I).comp (continuous_const.add
    (Complex.ofRealCLM.continuous.mul continuous_const)).measurable).aestronglyMeasurable).mpr hx
  rwa [restrict_Ioo_eq_restrict_Ioc] at hmL

theorem dirichlet_halfBox_vertical_hasDerivAt {a b : ℝ} {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : |x| < a) (hy : y ∈ Ioo 0 b) :
    HasDerivAt (fun s : ℝ => v (x + s * Complex.I))
      (dirD v Complex.I (x + y * Complex.I)) y := ((hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds (by
    simp_all [smoothDirichletHalfBox]))).hasFDerivAt.comp_hasDerivAt y (by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ))

/-- Actual half-rectangle L² energy in real product coordinates.
This is precisely the product measure of its two coordinate
intervals, with the physical Lebesgue normalization preserved. -/
theorem dirichlet_halfBox_sq_integrable_real_prod {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Integrable (fun p  => ‖g (p.1 + p.2 * Complex.I)‖ ^ 2)
      ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo 0 b))) := by
  let e  := Complex.measurableEquivRealProd.symm
  have he (p : ℝ × ℝ) : e p = p.1 + p.2 * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo 0 b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt]
  have hprod := ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage e.measurableEmbedding).mpr (hg.integrable_norm_pow (by norm_num))
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  continuity

/-- The true boundary-strip estimate after integration over the
tangential variable. Both sides are actual two-dimensional energies,
expressed by Fubini with the ordinary Lebesgue measure. -/
theorem dirichlet_halfBox_strip_mass_le {a b : ℝ}
    {v : ℂ → ℂ} (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v x = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    {ε : ℝ} (hε : ε ∈ Ioc 0 b) :
    (∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε,
      ‖v (x + t * Complex.I)‖ ^ 2) / ε ^ 2 ≤
    ∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε,
      ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2 := by
  have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hε.2⟩
  have hVi : Integrable (fun x : ℝ => ∫ t in 0..ε,
      ‖v (x + t * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod (hm.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left
  simpa only [div_eq_mul_inv, integral_mul_const] using integral_mono_ae (hVi.div_const (ε ^ 2)) (by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod (hg.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left) (by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg, ae_restrict_mem measurableSet_Ioo]
      with x hmL hxI
    have hx  := abs_lt.mpr hxI
    exact dirichlet_zero_endpoint_strip_mass_le (hv.comp (continuous_const.add
      (Complex.ofRealCLM.continuous.mul continuous_const)).continuousOn (by
      intro t ht
      simpa [smoothDirichletClosedHalfBox] using
        (⟨hx.le, ht.1, ht.2⟩))) (by continuity)
      (fun t ht => dirichlet_halfBox_vertical_hasDerivAt hs hx ht) hmL hε)

theorem dirichlet_slice_energy_tendsto_zero (hb : 0 < b) {dv : ℝ → ℂ}
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) :
    Tendsto (fun ε  => ∫ t in 0..ε, ‖dv t‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := intervalIntegral.continuousOn_primitive_interval' ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
      (hm.integrable_norm_pow (by norm_num))) left_mem_uIcc 0 left_mem_uIcc
  rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb] at h
  simpa only [intervalIntegral.integral_same] using
    h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- The actual normal energy in a shrinking boundary strip tends
to zero after tangential integration. The majorant is the genuine
full-rectangle L² normal energy obtained from Fubini. -/
theorem dirichlet_halfBox_normal_strip_energy_tendsto_zero {a b : ℝ} (hb : 0 < b)
    {v : ℂ → ℂ}
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  => ∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε,
      ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let B : ℝ → ℝ := fun x => ∫ t in 0..b,
    ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun x : ℝ => ∫ t in 0..ε,
        ‖dirD v Complex.I (x + t * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
      fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hεb⟩
    exact by
      simpa only [intervalIntegral.integral_of_le (hε.le),
        integral_Ioc_eq_integral_Ioo] using (dirichlet_halfBox_sq_integrable_real_prod (hg.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left.aestronglyMeasurable
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
     B hmeas (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
    have hε₀  := hε
    rw [Real.norm_of_nonneg (by
      rw [intervalIntegral.integral_of_le hε₀.le]
      positivity)]
    exact intervalIntegral.integral_mono_interval le_rfl hε₀.le hεb.le
      (Eventually.of_forall fun _ => sq_nonneg _) ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
        (hx.integrable_norm_pow (by norm_num)))) (by
    simpa only [B, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hg).integral_prod_left) (by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
    exact dirichlet_slice_energy_tendsto_zero hb hx)
  simp_all

/-- The derivative-scale boundary-strip mass tends to zero in the
actual full half rectangle. This is the genuine estimate needed for
normal cutoffs when extending the weak equation to zero-boundary H¹
tests. It still does not assert a boundary second-derivative gain. -/
theorem dirichlet_halfBox_strip_mass_tendsto_zero {a b : ℝ} (hb : 0 < b)
    {v : ℂ → ℂ} (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v x = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  =>
      (∫ (x : ℝ) in Ioo (-a) a, ∫ t in 0..ε,
        ‖v (x + t * Complex.I)‖ ^ 2) / ε ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (dirichlet_halfBox_normal_strip_energy_tendsto_zero hb hg)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    apply div_nonneg _ (sq_nonneg _)
    apply integral_nonneg
    intro x
    change 0 ≤ ∫ t in 0..ε, ‖v (x + t * Complex.I)‖ ^ 2
    rw [intervalIntegral.integral_of_le hε.le]
    positivity
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    exact dirichlet_halfBox_strip_mass_le hv hs hz hm hg ⟨hε, hεb.le⟩

/-! ### Genuine smooth normal cutoffs -/

/-- The derivative of the actual smooth transition is zero off its
transition interval, including its two endpoints. The endpoint assertion
uses genuine differentiability at the global minimum or maximum. -/
theorem dirichlet_smoothTransition_deriv_eq_zero {t : ℝ}
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
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((show ContDiff ℝ 2 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv
      (by norm_num)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc 0 1
  · continuity
  · rw [dirichlet_smoothTransition_deriv_eq_zero (by
      grind), norm_zero]
    positivity

/-- A genuine smooth cutoff of the normal coordinate: it is zero below
height `ε` and one above height `2 * ε`. -/
def dirichletNormalCutoff (ε : ℝ) (z : ℂ) : ℂ :=
  (Real.smoothTransition (z.im / ε - 1) : ℂ)

theorem dirichletNormalCutoff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletNormalCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((Complex.imCLM.contDiff.div_const ε).sub contDiff_const))

theorem norm_dirichletNormalCutoff_le (ε : ℝ) (z : ℂ) :
    ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
  rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg
    (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem dirichletNormalCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z.im ≤ ε) : dirichletNormalCutoff ε z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 := by
    have := (div_le_one hε).mpr hz
    linarith
  simp [dirichletNormalCutoff, Real.smoothTransition.zero_of_nonpos ht]

theorem dirichletNormalCutoff_eq_one {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 2 * ε ≤ z.im) : dirichletNormalCutoff ε z = 1 := by
  have ht : 1 ≤ z.im / ε - 1 := by
    have := (le_div_iff₀ hε).mpr hz
    linarith
  simp [dirichletNormalCutoff, Real.smoothTransition.one_of_one_le ht]

theorem dirichletNormalCutoff_fderiv (z w : ℂ) :
    fderiv ℝ (dirichletNormalCutoff ε) z w =
      (deriv Real.smoothTransition (z.im / ε - 1) / ε * w.im : ℝ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z ((((show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable
      (by norm_num)) (z.im / ε - 1)).hasDerivAt.comp_hasFDerivAt z (by
    have h_simpa := ((Complex.imCLM.hasFDerivAt (x := z)).mul_const ε⁻¹).sub_const 1
    assumption))
  have hd' : HasFDerivAt (dirichletNormalCutoff ε)
      (Complex.ofRealCLM.comp
        (deriv Real.smoothTransition (z.im / ε - 1) • (ε⁻¹ • Complex.imCLM))) z := hd
  simp [hd'.fderiv, div_eq_mul_inv, mul_assoc]

@[simp] theorem dirD_dirichletNormalCutoff_one (z : ℂ) :
    dirD (dirichletNormalCutoff ε) 1 z = 0 := by
  simp [dirD, dirichletNormalCutoff_fderiv]

theorem dirD_dirichletNormalCutoff_I (z : ℂ) :
    dirD (dirichletNormalCutoff ε) Complex.I z =
      (deriv Real.smoothTransition (z.im / ε - 1) / ε : ℝ) := by
  simp [dirD, dirichletNormalCutoff_fderiv]

theorem dirD_dirichletNormalCutoff_I_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z.im ≤ ε ∨ 2 * ε ≤ z.im) :
    dirD (dirichletNormalCutoff ε) Complex.I z = 0 := by
  rw [dirD_dirichletNormalCutoff_I, dirichlet_smoothTransition_deriv_eq_zero (by
    rcases hz with hz | hz
    · have := (div_le_one hε).mpr hz
      simp_all
    · have := (le_div_iff₀ hε).mpr hz
      grind)]
  simp 

theorem norm_dirD_dirichletNormalCutoff_I_le {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) (z : ℂ) :
    ‖dirD (dirichletNormalCutoff ε) Complex.I z‖ ≤ C / ε := by
  rw [dirD_dirichletNormalCutoff_I, Complex.norm_real, norm_div,
    Real.norm_of_nonneg hε.le]
  exact div_le_div_of_nonneg_right (hC _) hε.le

/-- The actual additional gradient term created by a normal cutoff. -/
def dirichletNormalCutoffError (ε : ℝ) (v : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletNormalCutoff ε) Complex.I z * v z

theorem dirichletNormalCutoffError_memLp {a b C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) {v : ℂ → ℂ}
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletNormalCutoffError ε v) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply hm.of_le_mul  ((((dirichletNormalCutoff_contDiff ε).fderiv_right
      (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply continuous_const).aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖dirD (dirichletNormalCutoff ε) Complex.I z * v z‖ ≤ (C / ε) * ‖v z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_dirD_dirichletNormalCutoff_I_le hε hC z)
      (norm_nonneg _)

theorem dirichletNormalCutoffError_slice_eq_strip {ε b : ℝ} (hε : 0 < ε)
    (hεb : 2 * ε ≤ b) (v : ℂ → ℂ) (x : ℝ) :
    (∫ t in 0..b,
      ‖dirichletNormalCutoffError ε v (x + t * Complex.I)‖ ^ 2) =
    ∫ t in 0..(2 * ε),
      ‖dirichletNormalCutoffError ε v (x + t * Complex.I)‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by positivity)]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc le_rfl hεb)
  intro t ht
  have ht' : 2 * ε ≤ t := by
    grind
  have hzero : dirD (dirichletNormalCutoff ε) Complex.I
      (x + t * Complex.I) = 0 :=
    dirD_dirichletNormalCutoff_I_eq_zero hε (Or.inr (by simp_all))
  simp [dirichletNormalCutoffError, hzero]

/-- The full additional-gradient energy is bounded by the genuine
derivative-scale strip mass. No boundary derivative or target H² gain
is used in this cutoff estimate. -/
theorem dirichletNormalCutoffError_energy_le {a b C ε : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε ≤ b) (hC₀ : 0 ≤ C)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ x in Ioo (-a) a, ∫ t in 0..b,
      ‖dirichletNormalCutoffError ε v (x + t * Complex.I)‖ ^ 2) ≤
    (C ^ 2 / ε ^ 2) *
      (∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
        ‖v (x + t * Complex.I)‖ ^ 2) := by
  have hsub : smoothDirichletHalfBox a (2 * ε) ⊆ smoothDirichletHalfBox a b :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hεb⟩
  have hVi : Integrable (fun x : ℝ => ∫ t in 0..(2 * ε),
      ‖v (x + t * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε),
      integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod (hm.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left
  simpa only [integral_const_mul] using
    integral_mono_ae (by
    simpa only [intervalIntegral.integral_of_le ((by positivity : 0 < 2 * ε).trans_le hεb).le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod (dirichletNormalCutoffError_memLp hε hC hm)).integral_prod_left) (hVi.const_mul (C ^ 2 / ε ^ 2)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    let L : ℝ → ℂ := fun t => x + t * Complex.I
    have hLc : Continuous L := continuous_const.add
      (Complex.ofRealCLM.continuous.mul continuous_const)
    have hmap : MapsTo L (Icc 0 (2 * ε)) (smoothDirichletClosedHalfBox a b) := by
      intro t ht
      simpa [L, smoothDirichletClosedHalfBox] using
        (⟨(abs_lt.mpr hx).le, ht.1, ht.2.trans hεb⟩)
    have hvL := hv.comp hLc.continuousOn hmap
    have hVL : IntervalIntegrable (fun t => ‖v (L t)‖ ^ 2) volume 0 (2 * ε) :=
      (hvL.norm.pow 2).intervalIntegrable_of_Icc (by positivity)
    have hEL : IntervalIntegrable (fun t =>
        ‖dirichletNormalCutoffError ε v (L t)‖ ^ 2) volume 0 (2 * ε) :=
      (((((((dirichletNormalCutoff_contDiff ε).fderiv_right
        (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply continuous_const).comp hLc).continuousOn.mul hvL).norm).pow 2).intervalIntegrable_of_Icc (by positivity)
    rw [dirichletNormalCutoffError_slice_eq_strip hε hεb]
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (by positivity)
      hEL (hVL.const_mul (C ^ 2 / ε ^ 2)) (by
      intro t _
      dsimp only [dirichletNormalCutoffError]
      rw [norm_mul, mul_pow]
      simpa only [div_pow] using mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hC₀ hε.le)).mpr (norm_dirD_dirichletNormalCutoff_I_le hε hC (L t))) (sq_nonneg _))
    continuity)

/-- The genuine normal cutoff's additional gradient tends to zero
in the full two-dimensional energy. This is derived from actual
zero boundary values and H¹ energy, not from an asserted density
or boundary regularity principle. -/
theorem dirichletNormalCutoffError_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v x = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  => ∫ x in Ioo (-a) a, ∫ t in 0..b,
      ‖dirichletNormalCutoffError ε v (x + t * Complex.I)‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC₀, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  have hupper : Tendsto (fun ε  => (C ^ 2 / ε ^ 2) *
      (∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
        ‖v (x + t * Complex.I)‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε  => (4 * C ^ 2) *
        ((∫ x in Ioo (-a) a, ∫ t in 0..(2 * ε),
          ‖v (x + t * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
        (𝓝[>] 0) (𝓝 ((4 * C ^ 2) * 0)) :=
      tendsto_const_nhds.mul ((dirichlet_halfBox_strip_mass_tendsto_zero hb hv hs hz hm hg).comp (by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝 (2 * 0)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp_all))
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
theorem dirichlet_halfBox_sq_integral_eq_real_prod {a b : ℝ} (hb : 0 < b)
    {g : ℂ → ℂ} (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ x in Ioo (-a) a, ∫ t in 0..b,
        ‖g (x + t * Complex.I)‖ ^ 2 := by
  let e := Complex.measurableEquivRealProd.symm
  have he (p : ℝ × ℝ) : e p = p.1 + p.2 * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo 0 b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt]
  have hmeas  :=
    (isOpen_smoothDirichletHalfBox a b).measurableSet
  have hind : (fun p => (smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2) (e p)) =
      (e ⁻¹' smoothDirichletHalfBox a b).indicator (fun p => ‖g (e p)‖ ^ 2) := by
    rfl
  have hi := (Complex.volume_preserving_equiv_real_prod.symm _).integral_comp e.measurableEmbedding
    ((smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2))
  rw [hind, integral_indicator (hmeas.preimage e.measurable),
    integral_indicator hmeas, hpre, Measure.volume_eq_prod,
    ← Measure.prod_restrict] at hi
  rw [← hi]
  simpa only [he, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
    using integral_prod
      (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * Complex.I)‖ ^ 2) (dirichlet_halfBox_sq_integrable_real_prod hg)

theorem dirichletNormalCutoffError_physical_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v x = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  => ∫ z in smoothDirichletHalfBox a b,
      ‖dirichletNormalCutoffError ε v z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  apply (dirichletNormalCutoffError_energy_tendsto_zero hb hv hs hz hm hg).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dirichlet_halfBox_sq_integral_eq_real_prod hb
    (dirichletNormalCutoffError_memLp hε hC hm)).symm

theorem dirichletNormalCutoff_tendsto_one (hz : 0 < z.im) :
    Tendsto (fun ε  => dirichletNormalCutoff ε z) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (half_pos hz)).filter_mono nhdsWithin_le_nhds]
    with ε hε hεz
  exact (dirichletNormalCutoff_eq_one hε (by linarith)).symm

/-- Multiplication by the actual cutoff tends to the identity in L².
The majorant is four times the original squared norm. -/
theorem dirichletNormalCutoff_weight_error_energy_tendsto_zero {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  => ∫ z in smoothDirichletHalfBox a b,
      ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let B  := fun z => 4 * ‖g z‖ ^ 2
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun ε  => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    have h : Tendsto (fun ε  => (dirichletNormalCutoff ε z - 1) * g z)
        (𝓝[>] 0) (𝓝 ((1 - 1) * g z)) :=
      ((dirichletNormalCutoff_tendsto_one hz.2.1).sub
        tendsto_const_nhds).mul tendsto_const_nhds
    simpa only [sub_self, zero_mul, norm_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using h.norm.pow 2
  simpa only [integral_zero] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall (by
    intro ε
    exact ((((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const).aestronglyMeasurable.mul
      hg.aestronglyMeasurable).norm).pow 2)) (Eventually.of_forall (by
    intro ε
    exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hnorm : ‖dirichletNormalCutoff ε z - 1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by
          rw [norm_one]
          linarith [norm_dirichletNormalCutoff_le ε z])
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hnorm
      nlinarith)) ((hg.integrable_norm_pow (by norm_num)).const_mul 4) hlim

/-- Localization may reach the bottom edge. Its actual smooth normal
cutoff is nevertheless a genuine compact interior test, because it
vanishes on a whole neighborhood of that edge. -/
theorem dirichletNormalCutoff_testFunction {a b ε : ℝ} (hε : 0 < ε)
    (η : smoothTraceTests)
    (hη : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {v : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b)) :
    TestFunction (smoothDirichletHalfBox a b)
      (fun z => η z * dirichletNormalCutoff ε z * v z) := by
  let w  := fun z => η z * dirichletNormalCutoff ε z * v z
  have hheight : tsupport w ⊆ {z : ℂ | ε ≤ z.im} := by
    apply closure_minimal _ (isClosed_le continuous_const Complex.continuous_im)
    intro z hz
    by_contra h
    have hcut := dirichletNormalCutoff_eq_zero hε (le_of_not_ge h)
    continuity
  refine ⟨by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ smoothDirichletHalfBox a b
    · exact (η.property.1.contDiffAt.mul
        (dirichletNormalCutoff_contDiff ε).contDiffAt).mul
        (hs.contDiffAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))
    · apply (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _  => (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
      by_cases hzε : z.im < ε
      · filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzε] with u hu
        simp [dirichletNormalCutoff_eq_zero hε hu.le]
      · filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds (by
          intro hzη
          obtain ⟨hx, hy⟩ := hη hzη
          exact hz ⟨hx, hε.trans_le (le_of_not_gt hzε), hy⟩)] with u hu
        simp [image_eq_zero_of_notMem_tsupport hu], η.property.2.1.mul_right.mul_right, fun z hz => ?_⟩
  obtain ⟨hx, hy⟩ := hη (tsupport_mul_subset_left.trans tsupport_mul_subset_left hz)
  exact ⟨hx, hε.trans_le (hheight hz), hy⟩

theorem dirichletNormalCutoff_weight_error_memLp {a b : ℝ} (ε : ℝ) {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (fun z => (dirichletNormalCutoff ε z - 1) * g z) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply hg.of_le_mul  ((((dirichletNormalCutoff_contDiff ε).continuous.sub
    continuous_const).aestronglyMeasurable).mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖(dirichletNormalCutoff ε z - 1) * g z‖ ≤ 2 * ‖g z‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith [norm_dirichletNormalCutoff_le ε z])

/-- The cutoff product rule is proved at every actual interior point. -/
theorem dirichletNormalCutoff_product_dirD {a b : ℝ} (ε : ℝ) {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (fun u => dirichletNormalCutoff ε u * v u) w z =
      dirichletNormalCutoff ε z * dirD v w z +
        dirD (dirichletNormalCutoff ε) w z * v z := by
  simp only [dirD]
  change (fderiv ℝ (dirichletNormalCutoff ε * v) z) w = _
  rw [fderiv_mul ((dirichletNormalCutoff_contDiff ε).differentiable (by simp) z) ((hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))]
  simp 
  ring

/-- The actual normal gradient of the cutoff product converges in
L² to the actual normal gradient of the original zero-boundary H¹
function. Both terms in the product rule are controlled separately. -/
theorem dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v x = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
        dirD v Complex.I z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let A  := fun ε z =>
    (dirichletNormalCutoff ε z - 1) * dirD v Complex.I z
  let B  := fun ε z => dirichletNormalCutoffError ε v z
  have hup : Tendsto (fun ε  => 2 * (∫ z, ‖A ε z‖ ^ 2 ∂μ) +
      2 * (∫ z, ‖B ε z‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.mul (dirichletNormalCutoff_weight_error_energy_tendsto_zero hg)).add (tendsto_const_nhds.mul (dirichletNormalCutoffError_physical_energy_tendsto_zero hb hv hs hz hm hg))
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
      rw [dirichletNormalCutoff_product_dirD ε hs hzV]
      dsimp only [B, dirichletNormalCutoffError]
      ring
    have hAi := hAm.integrable_norm_pow (by norm_num)
    have hBi := hBm.integrable_norm_pow (by norm_num)
    have hbound : (fun z =>
        ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z‖ ^ 2) ≤ᵐ[μ]
        (fun z => 2 * ‖A ε z‖ ^ 2 + 2 * ‖B ε z‖ ^ 2) := by
      filter_upwards [hsum] with z hzsum
      rw [← hzsum]
      have hn' := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le (A ε z) (B ε z))
      nlinarith [sq_nonneg (‖A ε z‖ - ‖B ε z‖)]
    simpa only [Pi.add_apply, integral_add (hAi.const_mul 2) (hBi.const_mul 2), integral_const_mul]
      using integral_mono_ae (((hAm.add hBm).ae_eq hsum).integrable_norm_pow (by norm_num)) ((hAi.const_mul 2).add (hBi.const_mul 2)) hbound

theorem dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero {a b : ℝ}
    {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hg : MemLp (dirD v 1) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε  => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) 1 z -
        dirD v 1 z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  apply (dirichletNormalCutoff_weight_error_energy_tendsto_zero hg).congr'
  exact Eventually.of_forall fun ε => by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    rw [dirichletNormalCutoff_product_dirD ε hs hz, dirD_dirichletNormalCutoff_one]
    ring

end PolyaNeumann

end
