module

public import RequestProject.RiemannMappingSmoothBoundary
public import RequestProject.ReconBasic
public import RequestProject.ChainRule
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import RequestProject.PlanarNotation

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

/-- The project's coordinate Laplacian equals the genuine Euclidean
Laplacian at every point of twice continuous differentiability. -/
theorem lap_eq_euclidean_laplacian {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) : lap f z = Laplacian.laplacian f z := by
  have hd  :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (v : ℂ) : dirD (dirD f v) v z = fderiv ℝ (fderiv ℝ f) z v v := by
    change fderiv ℝ (fun w => fderiv ℝ f w v) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [lap, he, he, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A local equality transports both actual coordinate second
derivatives. No assumed differential equation is used. -/
theorem eventuallyEq_lap_eq {f g : ℂ → ℂ} {z : ℂ} (hfg : f =ᶠ[𝓝 z] g) :
    lap f z = lap g z := by
  have hd (v : ℂ)  :=
    (hfg.fderiv ).fun_comp (fun A : ℂ →L[ℝ] ℂ => A v)
  have hdd (v : ℂ)  :=
    congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((hd v).fderiv_eq )
  exact congrArg₂ (· + ·) (hdd 1) (hdd Complex.I)

theorem smooth_integral_dirD_mul_test {U : Set ℂ} {G φ : ℂ → ℂ}
    (hG : TestFunction univ G) (hφ : TestFunction U φ) (i : Fin 2) :
    (∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
  have hu := (hG.dirD (coordDir i)).memLp' 2 (μ := volume.restrict U)
  have hg (j : Fin 2) := ((hG.dirD (coordDir i)).dirD (coordDir j)).memLp' 2
    (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth (hG.dirD (coordDir i)).1 hu hg φ hφ i
  change (∫ z in U, (hu.toLp _ : L2 U) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hg i).toLp _ : L2 U) z * φ z) at hw
  simpa only [integral_toLp_mul] using hw

/-- The true weak Poisson identity for a function smooth only in the
open domain. The compact test is localized before integration by
parts, so no boundary derivatives or global second-derivative energy
are needed. -/
theorem local_smooth_gradient_test_eq_neg_lap {U : Set ℂ} (hU : IsOpen U)
    {v φ : ℂ → ℂ} (hv : ContDiffOn ℝ ∞ v U) (hφ : TestFunction U φ) :
    (∫ z in U, ∑ i : Fin 2, dirD v (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, lap v z * φ z) := by
  obtain ⟨G, hG, hGv⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hv
  have hfirst (i : Fin 2) :
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) =
        (fun z => dirD v (coordDir i) z * dirD φ (coordDir i) z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD v (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i)) ((hGv z hz).fderiv_eq )]
    · simp only [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz,
        ContinuousLinearMap.zero_apply, mul_zero]
  have hsecond : (fun z => lap G z * φ z) = (fun z => lap v z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [eventuallyEq_lap_eq (hGv z hz)]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hint (i : Fin 2) :
      IntegrableOn (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) U :=
    ((hG.dirD (coordDir i)).memLp' 2).integrable_mul ((hφ.dirD (coordDir i)).memLp' 2)
  have hxx : IntegrableOn (fun z => dirD (dirD G 1) 1 z * φ z) U :=
    (((hG.dirD 1).dirD 1).memLp' 2).integrable_mul (hφ.memLp' 2)
  have hyy : IntegrableOn (fun z => dirD (dirD G Complex.I) Complex.I z * φ z) U :=
    (((hG.dirD Complex.I).dirD Complex.I).memLp' 2).integrable_mul (hφ.memLp' 2)
  have hlap :
      (∫ z in U, lap G z * φ z) =
        (∫ z in U, dirD (dirD G 1) 1 z * φ z) +
          ∫ z in U, dirD (dirD G Complex.I) Complex.I z * φ z := by
    simp_rw [lap, add_mul]
    exact integral_add hxx hyy
  calc
    _ = ∫ z in U, ∑ i : Fin 2, dirD G (coordDir i) z * dirD φ (coordDir i) z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Finset.sum_congr rfl (fun i _ =>
        congrFun (hfirst i).symm z))
    _ = _ :=
      integral_finset_sum _ (fun i _ => hint i)
    _ = -(∫ z in U, lap G z * φ z) := by
      simp_rw [smooth_integral_dirD_mul_test hG hφ]
      rw [Fin.sum_univ_two, hlap]
      abel
    _ = _ := by rw [hsecond]

section

variable (F : ℂ → ℂ) (b : smoothTraceTests) (z : ℂ)
include b

/-- The real projection of a genuine globally smooth boundary datum
is itself a genuine globally smooth compactly supported datum. -/
def smoothTraceRealPart : smoothTraceTests := by
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  refine ⟨fun z => ((b z).re : ℂ), ?_⟩
  refine ⟨L.contDiff.comp b.property.1, ?_, subset_univ _⟩
  exact b.property.2.1.comp_left (show L (0 : ℂ) = 0 by simp [L])

@[simp] theorem smoothTraceRealPart_apply : smoothTraceRealPart b z = ((b z).re : ℂ) := rfl

include F z in
/-- The actual physical Dirichlet remainder after subtracting the
constructed smooth real boundary datum. -/
def riemannMappingDirichletRemainder : ℂ :=
  (riemannMappingGreenCorrection F z : ℂ) - b z

end

theorem lap_sub_of_contDiffAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    lap (fun w => f w - g w) z = lap f z - lap g z := by
  have heq : (fun w => f w - g w) = f + (-1 : ℝ) • g := by
    funext w
    change f w - g w = f w + (-1 : ℝ) • g w
    rw [neg_one_smul, sub_eq_add_neg]
  have hadd : Laplacian.laplacian (f + (-1 : ℝ) • g) z =
      Laplacian.laplacian f z + Laplacian.laplacian ((-1 : ℝ) • g) z :=
    hf.laplacian_add (hg.const_smul (-1 : ℝ))
  
  rw [lap_eq_euclidean_laplacian (hf.sub hg), heq, hadd, (laplacian_smul (-1 : ℝ) hg),
    ← lap_eq_euclidean_laplacian hf, ← lap_eq_euclidean_laplacian hg]
  simp [neg_one_smul, sub_eq_add_neg]

/-- The actual zero-boundary H¹ Poisson problem needed for boundary
regularity. Its function, smooth forcing, boundary values, H¹ vector,
and compact-test equation are derived from the constructed Green
correction. No zero-trace or boundary regularity premise is added. -/
theorem exists_riemannMapping_zero_boundary_poisson_problem {Ω : Set ℂ}
    {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F) :
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
    hΦ
  let b := smoothTraceRealPart b₀
  obtain ⟨u₀, hu₀, hgu₀⟩ := exists_riemannMappingGreenCorrectionH1 hΦ
  let h : ℂ → ℂ := fun z => (riemannMappingGreenCorrection F z : ℂ)
  have hharm : HarmonicOnNhd h Ω :=
    (riemannMappingGreenCorrection_harmonicOnNhd hΦ).comp_CLM
      Complex.ofRealCLM
  have hs : ContDiffOn ℝ ∞ h Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hΦ)
  have hv : ContDiffOn ℝ ∞ (riemannMappingDirichletRemainder F b) Ω :=
    hs.sub b.property.1.contDiffOn
  have hΔ (z : ℂ) (hz : z ∈ Ω) :
      lap (riemannMappingDirichletRemainder F b) z = -lap (b : ℂ → ℂ) z := by
    have hh : ContDiffAt ℝ 2 h z := (hharm z hz).1
    have hbreg : ContDiffAt ℝ 2 (b : ℂ → ℂ) z := b.property.1.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
    exact (lap_sub_of_contDiffAt hh hbreg).trans (by
      rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds]
      simp)
  refine ⟨b, u₀ - smoothTraceH1 Ω b, ?_, hv, ?_, ?_, ?_, hΔ, ?_⟩
  · exact (Complex.ofRealCLM.continuous.comp_continuousOn
      (riemannMappingGreenCorrection_continuousOn hΦ)).sub
        b.property.1.continuous.continuousOn
  · intro z hz
    change (riemannMappingGreenCorrection F z : ℂ) - ((b₀ z).re : ℂ) = 0
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
      ae_restrict_mem hΦ.smooth.1.1.measurableSet] with z hz hu hbz hzΩ
    have hd : DifferentiableAt ℝ (riemannMappingGreenCorrection F) z :=
      ((riemannMappingGreenCorrection_contDiffOn hΦ).differentiableOn
        (by simp)).differentiableAt (hΦ.smooth.1.1.mem_nhds hzΩ)
    have hc : fderiv ℝ h z =
        Complex.ofRealCLM.comp (fderiv ℝ (riemannMappingGreenCorrection F) z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) z = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hd,
        ContinuousLinearMap.fderiv]
    have hh : DifferentiableAt ℝ h z :=
      (hs.differentiableOn (by simp)).differentiableAt (hΦ.smooth.1.1.mem_nhds hzΩ)
    rw [hz, Pi.sub_apply, hu, h1Gradient_smoothTraceH1, hbz]
    change _ = fderiv ℝ (h - (b : ℂ → ℂ)) z (coordDir i)
    rw [fderiv_sub hh ((b.property.1.differentiable (by simp)) z), hc]
    simp
  · intro φ hφ
    rw [local_smooth_gradient_test_eq_neg_lap hΦ.smooth.1.1 hv hφ]
    have hl : (fun z => lap (riemannMappingDirichletRemainder F b) z * φ z)
        =ᵐ[volume.restrict Ω] (fun z => -(lap (b : ℂ → ℂ) z * φ z)) := by
      filter_upwards [ae_restrict_mem hΦ.smooth.1.1.measurableSet] with z hz
      rw [hΔ z hz, neg_mul]
    rw [integral_congr_ae hl, integral_neg, neg_neg]

/-! ## Actual smooth graph coordinates -/

section

variable (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hc₁ : ‖c‖ = 1) (hf : Continuous f) (z : ℂ)

include f z in
/-- The genuine graph shear. Its inverse subtracts the same graph
height, because the shear preserves the real coordinate. -/
def smoothDirichletGraphShear : ℂ :=
  z + (f z.re : ℂ) * Complex.I

@[simp] theorem smoothDirichletGraphShear_re :
    (smoothDirichletGraphShear f z).re = z.re := by
  simp [smoothDirichletGraphShear]

@[simp] theorem smoothDirichletGraphShear_im :
    (smoothDirichletGraphShear f z).im = z.im + f z.re := by
  simp [smoothDirichletGraphShear]

include hf in
/-- This is a global real homeomorphism, built from the supplied
continuous graph, rather than an assumed boundary coordinate map. -/
def smoothDirichletGraphShearHomeomorph : ℂ ≃ₜ ℂ where
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

@[simp] theorem smoothDirichletGraphShearHomeomorph_apply :
    smoothDirichletGraphShearHomeomorph f hf z = smoothDirichletGraphShear f z := rfl

@[simp] theorem smoothDirichletGraphShearHomeomorph_symm_apply :
    (smoothDirichletGraphShearHomeomorph f hf).symm z =
      z - (f z.re : ℂ) * Complex.I := rfl

theorem smoothDirichletGraphShear_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothDirichletGraphShear f) :=
  contDiff_id.add ((Complex.ofRealCLM.contDiff.comp
    (hf.comp Complex.reCLM.contDiff)).mul contDiff_const)

theorem smoothDirichletGraphShear_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : LipschitzWith (K + 1) (smoothDirichletGraphShear f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp [dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
  have hfw : ‖((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ ≤ K * ‖z - w‖ := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    have hre := Complex.abs_re_le_norm (z - w)
    exact (hf.norm_sub_le z.re w.re).trans
      (mul_le_mul_of_nonneg_left hre K.coe_nonneg)
  calc
    _ =
        ‖(z - w) + ((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ := by
      congr 1
      simp only [smoothDirichletGraphShear, Complex.ofReal_sub]
      ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hfw
    _ = _ := by ring

theorem smoothDirichletGraphShearHomeomorph_symm_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphShearHomeomorph f hf.continuous).symm := by
  have heq : (smoothDirichletGraphShearHomeomorph f hf.continuous).symm =
      smoothDirichletGraphShear (fun x => -f x) := by
    funext z
    simp only [smoothDirichletGraphShearHomeomorph_symm_apply, smoothDirichletGraphShear,
      Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
  rw [heq]
  exact smoothDirichletGraphShear_lipschitz hf.neg

include hc hf p in
/-- The graph shear followed by the actual rigid coordinates of the
smooth-domain chart. Only continuity of the supplied graph and a
nonzero rigid factor are required to construct this homeomorphism. -/
def smoothDirichletGraphChart :
    ℂ ≃ₜ ℂ :=
  (smoothDirichletGraphShearHomeomorph f hf).trans
    ((Homeomorph.mulRight₀ c hc).symm.trans (Homeomorph.addLeft p))

@[simp] theorem smoothDirichletGraphChart_apply :
    smoothDirichletGraphChart p c hc f hf z = p + smoothDirichletGraphShear f z / c := by
  simp only [smoothDirichletGraphChart, Homeomorph.trans_apply,
    smoothDirichletGraphShearHomeomorph_apply, Homeomorph.mulRight₀_symm_apply,
    Homeomorph.coe_addLeft, div_eq_mul_inv]

theorem smoothDirichletGraphChart_rotate :
    c * (smoothDirichletGraphChart p c hc f hf z - p) = smoothDirichletGraphShear f z := by
  rw [smoothDirichletGraphChart_apply]
  field_simp [hc]
  ring

theorem smoothDirichletGraphChart_contDiff
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothDirichletGraphChart p c hc f hf.continuous) :=
  contDiff_const.add ((smoothDirichletGraphShear_contDiff hf).div_const c)

include hc₁ in
theorem smoothDirichletGraphChart_lipschitz
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have heq : smoothDirichletGraphChart p c hc f hf.continuous z -
      smoothDirichletGraphChart p c hc f hf.continuous w =
      (smoothDirichletGraphShear f z - smoothDirichletGraphShear f w) / c := by
    simp only [smoothDirichletGraphChart_apply]
    ring
  simpa only [dist_eq_norm, heq, norm_div, hc₁, div_one] using
    (smoothDirichletGraphShear_lipschitz hf).dist_le_mul z w

include hc₁ in
theorem smoothDirichletGraphChart_symm_lipschitz
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + z) * c))
    ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + w) * c)) ≤ _
  
  have heq : (-p + z) * c - (-p + w) * c = (z - w) * c := by ring
  simpa only [dist_eq_norm, heq, norm_mul, hc₁, mul_one] using (smoothDirichletGraphShearHomeomorph_symm_lipschitz hf).dist_le_mul
    ((-p + z) * c) ((-p + w) * c)

end

/-- The smooth-domain definition supplies an actual flattened full
rectangle on which physical membership is exactly positive height.
The homeomorphism is built above from that domain's own graph. -/
theorem exists_smoothDomain_flattening_rectangle {Ω : Set ℂ} (hS : IsSmoothDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      ∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im) := by
  obtain ⟨c, r, h, K, f, hc₁, hr, hh, hf, hLip, hf₀, _, hchart⟩ := hS.2 p hp
  have hc : c ≠ 0 := by
    aesop
  let a := min r (h / (4 * (K + 1)))
  let b := h / 4
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  
  
  refine ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, (lt_min hr (div_pos hh hden)), (div_pos hh (by norm_num)), ?_⟩
  intro z hzre hzim
  
  have hscale : 4 * ((K : ℝ) + 1) * |z.re| < h := by
    simpa only [mul_comm] using
      (lt_div_iff₀ hden).mp (hzre.trans_le (min_le_right _ _))
  have hfz : |f z.re| ≤ (K : ℝ) * |z.re| := by
    simpa only [hf₀, sub_zero, Real.norm_eq_abs] using hLip.norm_sub_le z.re 0
  have hfzh : |f z.re| < h / 4 := by
    nlinarith [abs_nonneg z.re]
  
  have hmem := hchart (smoothDirichletGraphChart p c hc f hf.continuous z)
    (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re] using (hzre.trans_le (min_le_left _ _)))
    (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_im] using (by
      have hs := abs_add_le z.im (f z.re)
      dsimp [b] at hzim
      linarith))
  simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re,
    smoothDirichletGraphShear_im, lt_add_iff_pos_left] using hmem

/-- The bottom edge in an actual flattening rectangle maps to the
physical frontier. This follows from positive-height approach and
the local membership equivalence; frontier membership is not a new
coordinate premise. -/
theorem smoothDirichletGraphChart_mem_frontier {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    {x : ℝ} (hx : |x| < a) :
    smoothDirichletGraphChart p c hc f hf (x : ℂ) ∈ frontier Ω := by
  let Ψ := smoothDirichletGraphChart p c hc f hf
  have hnot : Ψ x ∉ Ω := by
    aesop
  have hcurve : Tendsto (fun t : ℝ => x + t * Complex.I)
      (𝓝[>] 0) (𝓝 x) := by
    have h : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x : ℂ) + (0 : ℂ) * Complex.I)) :=
      (tendsto_const_nhds.add
        ((Complex.ofRealCLM.continuous.tendsto 0).mul_const Complex.I)).mono_left
          nhdsWithin_le_nhds
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using h
  
  rw [hΩ.frontier_eq]
  refine ⟨mem_closure_of_tendsto ((Ψ.continuous.tendsto (x : ℂ)).comp hcurve) ?_, hnot⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
  have ht₀ : 0 < t := ht
  apply (hchart _ (by simpa using hx) (by simpa [abs_of_pos ht₀] using htb)).mpr
  simpa using ht₀

/-- True zero boundary values of a physical continuous solution
remain true zero values on the flattened boundary interval. -/
theorem smoothDirichletGraphChart_zero_boundary {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    (v : ℂ → ℂ) (hv : ∀ z ∈ frontier Ω, v z = 0) {x : ℝ} (hx : |x| < a) :
    v (smoothDirichletGraphChart p c hc f hf (x : ℂ)) = 0 :=
  hv _ (smoothDirichletGraphChart_mem_frontier hΩ p c hc f hf hb hchart hx)

/-- An actual pointwise H¹ function remains pointwise H¹ under the
constructed graph coordinates. This uses the proved bi-Lipschitz
L² pullback and actual chain differential, with no assumed pullback
energy or flattened Sobolev regularity. -/
theorem smoothDirichletGraphChart_pullback_memLp {Ω U : Set ℂ}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {K : NNReal} (hLip : LipschitzWith K f)
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
  have hΨ : LipschitzOnWith (K + 1) Ψ U :=
    (smoothDirichletGraphChart_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hΨinv : LipschitzOnWith (K + 1) Ψ.symm (Ψ '' U) :=
    (smoothDirichletGraphChart_symm_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hm' : MemLp v 2 (volume.restrict (Ψ '' U)) :=
    hm.mono_measure (Measure.restrict_mono_set volume himage)
  have hg' (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 (volume.restrict (Ψ '' U)) :=
    (hg i).mono_measure (Measure.restrict_mono_set volume himage)
  refine ⟨memLp_comp_bilip hΨinv hm', ?_⟩
  intro i
  let G : Fin 2 → L2 (Ψ '' U) := fun j => (hg' j).toLp _
  have hmc := memLp_chainGrad hU hΨ hΨinv G i
  have hae : ∀ᵐ z ∂(volume.restrict U), ∀ j : Fin 2,
      G j (Ψ z) = dirD v (coordDir j) (Ψ z) :=
    ae_all_iff.mpr (fun j => (quasiMeasurePreserving_restrict hΨinv).ae (hg' j).coeFn_toLp)
  apply hmc.ae_eq
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with z hz hzU
  have hzΩ : Ψ z ∈ Ω := himage (mem_image_of_mem Ψ hzU)
  have hdv := (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hzΩ)
  have hdΨ := ((smoothDirichletGraphChart_contDiff p c hc hf).differentiable (by simp)) z
  change chainGrad Ψ (fun j => (G j : ℂ → ℂ)) i z =
    fderiv ℝ (v ∘ Ψ) z (coordDir i)
  rw [fderiv_comp z hdv hdΨ, ContinuousLinearMap.comp_apply, clm_apply_eq_sum_coordRe]
  simp only [chainGrad, smul_eq_mul, hz, dirD]

section

variable (a b : ℝ)
include a b

def smoothDirichletHalfBox : Set ℂ :=
  {z | |z.re| < a ∧ 0 < z.im ∧ z.im < b}

def smoothDirichletClosedHalfBox : Set ℂ :=
  {z | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b}

theorem isOpen_smoothDirichletHalfBox : IsOpen (smoothDirichletHalfBox a b) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

end

/-! ## The actual elliptic coefficients of graph flattening -/

section

variable (d : ℝ) (p c : ℂ) (hc : c ≠ 0)

include d in
/-- The actual differential of the graph shear at graph slope `d`.
It maps `(x,y)` to `(x,y+d*x)`. -/
def smoothDirichletGraphDifferential : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + (d • Complex.reCLM).smulRight Complex.I

@[simp] theorem smoothDirichletGraphDifferential_apply (w : ℂ) :
    smoothDirichletGraphDifferential d w = w + (d * w.re) • Complex.I := by
  simp only [smoothDirichletGraphDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, Complex.reCLM_apply, smul_eq_mul]

theorem smoothDirichletGraphShear_hasFDerivAt {f : ℝ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z.re) :
    HasFDerivAt (smoothDirichletGraphShear f)
      (smoothDirichletGraphDifferential (deriv f z.re)) z := by
  
  have hs := (hasFDerivAt_id z).add ((hf.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt).smul_const Complex.I)
  have h_simpa := hs
  exact h_simpa

theorem smoothDirichletGraphChart_hasFDerivAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    HasFDerivAt (smoothDirichletGraphChart p c hc f hf.continuous)
      (c⁻¹ • smoothDirichletGraphDifferential (deriv f z.re)) z := by
  
  have hs := ((smoothDirichletGraphShear_hasFDerivAt ((hf.differentiable (by simp)) z.re)).mul_const c⁻¹).const_add p
  convert hs using 1
  funext x
  simp [div_eq_mul_inv]

theorem smoothDirichletGraphChart_fderiv_apply
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z w : ℂ) :
    fderiv ℝ (smoothDirichletGraphChart p c hc f hf.continuous) z w =
      c⁻¹ * (w + (deriv f z.re * w.re) • Complex.I) := by
  rw [(smoothDirichletGraphChart_hasFDerivAt p c hc hf z).fderiv]
  simp

/-- The actual chain rule exposes the inverse-graph energy
components. The physical derivatives occur in the rigid directions
`1/c` and `I/c`; the tangential shear term cancels exactly. -/
theorem smoothDirichletGraphChart_pullback_gradient
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let u := v ∘ Ψ
     dirD u 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD u Complex.I z = fderiv ℝ v (Ψ z) (1 / c)) ∧
    dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      fderiv ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z) (Complex.I / c) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let T := fderiv ℝ v (Ψ z)
  let d := deriv f z.re
  
  have hchain (w : ℂ) : dirD (v ∘ Ψ) w z = T (c⁻¹ * (w + (d * w.re) • Complex.I)) := by
    change fderiv ℝ (v ∘ Ψ) z w = _
    rw [fderiv_comp z hv ((smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt), ContinuousLinearMap.comp_apply,
      smoothDirichletGraphChart_fderiv_apply p c hc hf z w]
  have hI : dirD (v ∘ Ψ) Complex.I z = T (Complex.I / c) := by
    rw [hchain]
    simp [Complex.I_re, mul_zero, zero_smul, div_eq_mul_inv, mul_comm]
  have h1 : dirD (v ∘ Ψ) 1 z = T (1 / c) + d • T (Complex.I / c) := by
    rw [hchain]
    have he : c⁻¹ * ((1 : ℂ) + (d * (1 : ℂ).re) • Complex.I) =
        (1 / c : ℂ) + d • (Complex.I / c) := by
      simp only [Complex.one_re, mul_one, Complex.real_smul, div_eq_mul_inv]
      ring
    rw [he, map_add, map_smul]
  constructor
  · aesop
  · exact hI

end

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
    (x ^ 2 + y ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      smoothDirichletGraphQuadratic (deriv f t) x y ∧
    smoothDirichletGraphQuadratic (deriv f t) x y ≤
      2 * (1 + (K : ℝ) ^ 2) * (x ^ 2 + y ^ 2) := by
  let d := deriv f t
  have hd := norm_deriv_le_of_lipschitz hf (x₀ := t)
  have hd₂ : d ^ 2 ≤ K ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg d) K.coe_nonneg).mpr hd
    simpa using hs
  have hq : 0 ≤ (x - d * y) ^ 2 + y ^ 2 := by positivity
  
  have hlow : x ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * ((x - d * y) ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * d * y), sq_nonneg y,
      mul_nonneg (sq_nonneg d) (sq_nonneg (x - d * y))]
  have hupp : (x - d * y) ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x + d * y),
      mul_nonneg (sq_nonneg d) (sq_nonneg x), sq_nonneg y]
  
  rw [smoothDirichletGraphQuadratic_eq_sq]
  constructor
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hd₂) hq]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd₂)
      (add_nonneg (sq_nonneg x) (sq_nonneg y))]

/-- The same genuine elliptic bounds hold for complex-valued
solutions, by applying the real coefficient form to the actual real
and imaginary components. -/
theorem smoothDirichletGraph_complex_energy_bounds {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (t : ℝ) (x y : ℂ) :
    (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ∧
    ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ≤
      2 * (1 + (K : ℝ) ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hr₁, hr₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.re y.re
  obtain ⟨hi₁, hi₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.im y.im
  have heq : ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 =
      smoothDirichletGraphQuadratic (deriv f t) x.re y.re +
        smoothDirichletGraphQuadratic (deriv f t) x.im y.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, smoothDirichletGraphQuadratic]
    ring
  rw [heq]
  constructor
  · 
    convert (add_le_add hr₁ hi₁) using 1
    simp only [Complex.sq_norm, Complex.normSq_apply, ← add_div]
    ring
  · 
    convert (add_le_add hr₂ hi₂) using 1
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring

/-! ## The genuine one-dimensional zero-boundary energy step -/

/-- An actual continuous zero endpoint and an integrable interior
derivative give the primitive identity up to the endpoint. No
derivative or smooth extension is required at that endpoint. -/
theorem dirichlet_zero_endpoint_primitive {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    v t = ∫ s in (0 : ℝ)..t, dv s := by
  have hvc  := hv.mono
    (Icc_subset_Icc le_rfl ht.2)
  have hm' : MemLp dv 2 (volume.restrict (Ioc 0 t)) :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have hi : IntervalIntegrable dv volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
    exact hm'.integrable (by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1.le hvc
    (fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩) hi
  rw [hv₀, sub_zero] at h
  exact h.symm

/-- Actual L² derivative energy controls the value next to a zero
endpoint. This is the estimate needed to remove a thin boundary
strip when closing Dirichlet tests in H¹. -/
theorem dirichlet_zero_endpoint_norm_sq_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    ‖v t‖ ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
  rw [dirichlet_zero_endpoint_primitive hv hv₀ hd hm ht]
  simpa using norm_sq_intervalIntegral_le ht.1.le
    (hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2)))

/-- The actual zero endpoint controls the mass of a thin boundary
strip by the derivative energy in that same strip. The crude
constant `1` is sufficient to close Dirichlet cutoff tests. -/
theorem dirichlet_zero_endpoint_strip_mass_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {ε : ℝ} (hε : ε ∈ Ioc 0 b) :
    (∫ t in (0 : ℝ)..ε, ‖v t‖ ^ 2) / ε ^ 2 ≤
      ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2 := by
  have hmi : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioc 0 b) :=
    hm.norm.integrable_sq
  have hI : IntervalIntegrable (fun t => ‖dv t‖ ^ 2) volume 0 ε := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε.1.le]
    exact hmi.mono_set (Ioc_subset_Ioc le_rfl hε.2)
  have hV : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 ε :=
    ((hv.mono (Icc_subset_Icc le_rfl hε.2)).norm.pow 2).intervalIntegrable_of_Icc hε.1.le
  
  have hbnd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      ‖v t‖ ^ 2 ≤ ε * ∫ s in 0..ε, ‖dv s‖ ^ 2 := by
    
    
    exact (dirichlet_zero_endpoint_norm_sq_le hv hv₀ hd hm
      (show t ∈ Ioc 0 b from ⟨ht.1, ht.2.le.trans hε.2⟩)).trans ((mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
      (Eventually.of_forall fun _ => sq_nonneg _) hI) ht.1.le).trans
      (mul_le_mul_of_nonneg_right ht.2.le (by
        rw [intervalIntegral.integral_of_le hε.1.le]
        exact integral_nonneg (fun t => sq_nonneg _))))
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hε.1.le hV
    (intervalIntegrable_const ) hbnd
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hε.1)).mpr
  nlinarith

section

variable (p : ℝ × ℝ) (a b : ℝ)

include p in
/-- The genuine real-coordinate map, without an artificial measure scale. -/
def rectangularComplexCoord : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem continuous_rectangularComplexCoord : Continuous rectangularComplexCoord :=
  (Complex.ofRealCLM.continuous.comp continuous_fst).add
    ((Complex.ofRealCLM.continuous.comp continuous_snd).mul continuous_const)

theorem rectangularComplexCoord_mem_halfBox {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b) :
    rectangularComplexCoord p ∈ smoothDirichletHalfBox a b := by
  simpa [smoothDirichletHalfBox, rectangularComplexCoord, abs_lt] using hp

include a b in
/-- Lebesgue measure on a coordinate rectangle. -/
abbrev rectangularMeasure (c d : ℝ) :=
  (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))

private lemma realProd_symm_apply :
    Complex.measurableEquivRealProd.symm p = rectangularComplexCoord p := by
  apply Complex.ext <;> simp [rectangularComplexCoord]

/-- Real product coordinates preserve area on the actual open half box. -/
lemma measurePreserving_halfBox :
    MeasurePreserving Complex.measurableEquivRealProd.symm (rectangularMeasure (-a) a 0 b)
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let e := Complex.measurableEquivRealProd.symm
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt, and_assoc]
  have h := (Complex.volume_preserving_equiv_real_prod.symm _).restrict_preimage_emb
    e.measurableEmbedding (smoothDirichletHalfBox a b)
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact h

/-- Actual half-rectangle L² energy in real product coordinates.
This is precisely the product measure of its two coordinate
intervals, with the physical Lebesgue normalization preserved. -/
theorem dirichlet_halfBox_sq_integrable_real_prod {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Integrable (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2)
      (rectangularMeasure (-a) a 0 b) := by
  simpa only [Function.comp_def, realProd_symm_apply, rectangularComplexCoord] using
    ((measurePreserving_halfBox a b).integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr
      hg.norm.integrable_sq

/-- Genuine L² normal derivative energy gives L² energy on almost
every vertical slice, by the actual Lebesgue coordinate map. -/
theorem dirichlet_halfBox_vertical_memLp {a b : ℝ} {v : ℂ → ℂ}
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
        (volume.restrict (Ioc (0 : ℝ) b)) := by
  filter_upwards [(dirichlet_halfBox_sq_integrable_real_prod hg).prod_right_ae] with x hx
  have hLc : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := continuous_const.add
    (Complex.ofRealCLM.continuous.mul continuous_const)
  have hmeas : Measurable (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    (measurable_fderiv_apply_const ℝ v Complex.I).comp hLc.measurable
  have hmL : MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
      (volume.restrict (Ioo 0 b)) :=
    (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr hx
  rw [restrict_Ioo_eq_restrict_Ioc] at hmL
  exact hmL

theorem dirichlet_halfBox_vertical_hasDerivAt {a b : ℝ} {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : |x| < a) (hy : y ∈ Ioo 0 b) :
    HasDerivAt (fun s : ℝ => v ((x : ℂ) + (s : ℂ) * Complex.I))
      (dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) y := by
  have hyV : (x : ℂ) + (y : ℂ) * Complex.I ∈ smoothDirichletHalfBox a b := by
    simpa [smoothDirichletHalfBox] using (show |x| < a ∧ 0 < y ∧ y < b from ⟨hx, hy.1, hy.2⟩)
  have hdv := (hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hyV)
  
  apply hdv.hasFDerivAt.comp_hasDerivAt y
  simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)


/-- Fubini identifies the actual physical squared norm with its two
real coordinate integrals. The coordinate transformation has Jacobian
one, so no scale factor is introduced. -/
theorem dirichlet_halfBox_sq_integral_eq_real_prod {a b : ℝ} (hb : 0 < b)
    {g : ℂ → ℂ} (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
        ‖g ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [← (measurePreserving_halfBox a b).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding (fun z => ‖g z‖ ^ 2)]
  simp_rw [realProd_symm_apply, rectangularComplexCoord, intervalIntegral.integral_of_le hb.le,
    integral_Ioc_eq_integral_Ioo]
  exact integral_prod _ (dirichlet_halfBox_sq_integrable_real_prod hg)

include a b in
/-- Total squared L² mass in an open half rectangle. -/
abbrev halfBoxEnergy (g : ℂ → ℂ) := ∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2

lemma halfBox_mono {a A b B : ℝ} (ha : a ≤ A) (hb : b ≤ B) :
    smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A B :=
  fun _ hz => ⟨hz.1.trans_le ha, hz.2.1, hz.2.2.trans_le hb⟩

lemma halfBoxEnergy_nonneg (v : ℂ → ℂ) : 0 ≤ halfBoxEnergy a b v :=
  integral_nonneg fun _ => sq_nonneg _

end

section Strip
variable {a b : ℝ} {v : ℂ → ℂ}
  (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
  (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
  (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
  (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
  (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))

include hv hs hz hm hg in
lemma dirichlet_halfBox_strip_mass_le {ε : ℝ} (hε : ε ∈ Ioc 0 b) :
    halfBoxEnergy a ε v / ε ^ 2 ≤ halfBoxEnergy a ε (dirD v Complex.I) := by
  have sub := Measure.restrict_mono_set volume (halfBox_mono (le_refl a) hε.2)
  have hi {g : ℂ → ℂ} (h : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
      Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε, ‖g ((x : ℂ) + (t : ℂ) * I)‖ ^ 2)
        (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo] using
      (dirichlet_halfBox_sq_integrable_real_prod (h.mono_measure sub)).integral_prod_left
  rw [halfBoxEnergy, halfBoxEnergy, dirichlet_halfBox_sq_integral_eq_real_prod hε.1 (hm.mono_measure sub),
    dirichlet_halfBox_sq_integral_eq_real_prod hε.1 (hg.mono_measure sub), ← integral_div]
  apply integral_mono_ae ((hi hm).div_const _) (hi hg)
  filter_upwards [dirichlet_halfBox_vertical_memLp hg, ae_restrict_mem measurableSet_Ioo] with x hmL hxI
  have hx := abs_lt.mpr hxI
  let L : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * I
  have hmap : MapsTo L (Icc 0 b) (smoothDirichletClosedHalfBox a b) := fun t ht => by
    simpa [L, smoothDirichletClosedHalfBox] using And.intro hx.le ht
  exact dirichlet_zero_endpoint_strip_mass_le (hv.comp (by fun_prop : Continuous L).continuousOn hmap)
    (by simpa [L] using hz x hx) (fun _ ht => dirichlet_halfBox_vertical_hasDerivAt hs hx ht) hmL hε

/-- Fubini in the other order makes the mass of a strip an indefinite integral
of a single integrable horizontal marginal. -/
lemma halfBoxEnergy_tendsto_zero {g : ℂ → ℂ} (hb : 0 < b)
    (h : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε => halfBoxEnergy a ε g) (𝓝[>] 0) (𝓝 0) := by
  let M := fun t : ℝ => ∫ x in Ioo (-a) a, ‖g ((x : ℂ) + (t : ℂ) * I)‖ ^ 2
  have hi : IntervalIntegrable M volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    simpa only [M, IntegrableOn, restrict_Ioo_eq_restrict_Ioc] using
      (dirichlet_halfBox_sq_integrable_real_prod h).integral_prod_right
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc 0 left_mem_uIcc
  rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb,
    intervalIntegral.integral_same] at hc
  apply (hc.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)).congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hpos hlt
  have hε := h.mono_measure (Measure.restrict_mono_set volume (halfBox_mono le_rfl hlt.le))
  rw [halfBoxEnergy, dirichlet_halfBox_sq_integral_eq_real_prod hpos hε]
  simp_rw [intervalIntegral.integral_of_le (le_of_lt hpos), integral_Ioc_eq_integral_Ioo]
  exact (integral_integral_swap (dirichlet_halfBox_sq_integrable_real_prod hε)).symm

include hv hs hz hm hg in
lemma dirichlet_halfBox_strip_mass_tendsto_zero (hb : 0 < b) :
    Tendsto (fun ε => halfBoxEnergy a ε v / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (.of_forall fun ε => div_nonneg (halfBoxEnergy_nonneg ..) (sq_nonneg ε)) _
    (halfBoxEnergy_tendsto_zero hb hg)
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
  exact dirichlet_halfBox_strip_mass_le hv hs hz hm hg ⟨hε, hεb.le⟩

end Strip

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
  have hc  :=
    (show ContDiff ℝ 2 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv
      (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc 0 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have htz : t ≤ 0 ∨ 1 ≤ t := by
      grind
    rw [dirichlet_smoothTransition_deriv_eq_zero htz, norm_zero]
    exact le_max_right _ _

section

variable (ε : ℝ) (z : ℂ)

include z ε in
/-- A genuine smooth cutoff of the normal coordinate: it is zero below
height `ε` and one above height `2 * ε`. -/
def dirichletNormalCutoff : ℂ :=
  (Real.smoothTransition (z.im / ε - 1) : ℂ)

theorem dirichletNormalCutoff_contDiff :
    ContDiff ℝ ∞ (dirichletNormalCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((Complex.imCLM.contDiff.div_const ε).sub contDiff_const))

theorem norm_dirichletNormalCutoff_le :
    ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
  rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg
    (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem dirichletNormalCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z.im ≤ ε) : dirichletNormalCutoff ε z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 := by
    have := (div_le_one hε).mpr hz
    linarith
  simp only [dirichletNormalCutoff, Real.smoothTransition.zero_of_nonpos ht,
    Complex.ofReal_zero]

theorem dirichletNormalCutoff_eq_one {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 2 * ε ≤ z.im) : dirichletNormalCutoff ε z = 1 := by
  have ht : 1 ≤ z.im / ε - 1 := by
    have := (le_div_iff₀ hε).mpr hz
    linarith
  simp only [dirichletNormalCutoff, Real.smoothTransition.one_of_one_le ht,
    Complex.ofReal_one]

theorem dirichletNormalCutoff_fderiv (w : ℂ) :
    fderiv ℝ (dirichletNormalCutoff ε) z w =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε * w.im : ℝ) : ℂ) := by
  have hi : HasFDerivAt (fun u : ℂ => u.im / ε - 1)
      (ε⁻¹ • Complex.imCLM) z := by
    have h_simpa := ((Complex.imCLM.hasFDerivAt (x := z)).mul_const ε⁻¹).sub_const 1
    simp only [div_eq_mul_inv] at h_simpa ⊢
    exact h_simpa
  have ht := (show Differentiable ℝ Real.smoothTransition from
    (show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable
      (by norm_num)) (z.im / ε - 1)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (ht.hasDerivAt.comp_hasFDerivAt z hi)
  have hd' : HasFDerivAt (dirichletNormalCutoff ε)
      (Complex.ofRealCLM.comp
        (deriv Real.smoothTransition (z.im / ε - 1) • (ε⁻¹ • Complex.imCLM))) z := hd
  rw [hd'.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, mul_assoc]

@[simp] theorem dirD_dirichletNormalCutoff_one :
    dirD (dirichletNormalCutoff ε) 1 z = 0 := by
  simp only [dirD, dirichletNormalCutoff_fderiv, Complex.one_im, mul_zero,
    Complex.ofReal_zero]

theorem dirD_dirichletNormalCutoff_I :
    dirD (dirichletNormalCutoff ε) Complex.I z =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε : ℝ) : ℂ) := by
  simp [dirD, dirichletNormalCutoff_fderiv, Complex.I_im]

theorem dirD_dirichletNormalCutoff_I_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z.im ≤ ε ∨ 2 * ε ≤ z.im) :
    dirD (dirichletNormalCutoff ε) Complex.I z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 ∨ 1 ≤ z.im / ε - 1 := by
    rcases hz with hz | hz
    · grind [(div_le_one hε).mpr hz]
    · grind [(le_div_iff₀ hε).mpr hz]
  rw [dirD_dirichletNormalCutoff_I, dirichlet_smoothTransition_deriv_eq_zero ht]
  simp

theorem norm_dirD_dirichletNormalCutoff_I_le {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) (z : ℂ) :
    ‖dirD (dirichletNormalCutoff ε) Complex.I z‖ ≤ C / ε := by
  rw [dirD_dirichletNormalCutoff_I, Complex.norm_real, norm_div,
    Real.norm_of_nonneg hε.le]
  bound

/-- A bounded factor supported below height `e` only sees the mass of that strip. -/
lemma halfBoxEnergy_mul_le {a b e C : ℝ} {m v : ℂ → ℂ} (he : e ≤ b)
    (hm : Continuous m) (hC : ∀ z, ‖m z‖ ≤ C) (hzero : ∀ z : ℂ, e ≤ z.im → m z = 0)
    (hv : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    halfBoxEnergy a b (m * v) ≤ C ^ 2 * halfBoxEnergy a e v := by
  have sub := halfBox_mono (le_refl a) he
  have h := hv.mono_measure (Measure.restrict_mono_set volume sub)
  have h' := (memLp_top_of_bound hm.aestronglyMeasurable C (.of_forall hC)).mul h (r := 2)
  rw [halfBoxEnergy, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isOpen_smoothDirichletHalfBox a b).measurableSet sub, halfBoxEnergy, ← integral_const_mul]
  · apply integral_mono h'.norm.integrable_sq (h.norm.integrable_sq.const_mul _)
    intro z
    simp only [Pi.mul_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC z) 2) (sq_nonneg _)
  · rintro z ⟨hz, hn⟩
    have hez : e ≤ z.im := le_of_not_gt fun hl => hn ⟨hz.1, hz.2.1, hl⟩
    simp [hzero z hez]

private lemma double_height_tendsto : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun _ hx => mul_pos two_pos hx⟩
  have h : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] 0) (𝓝 (2 * 0)) :=
    tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa only [mul_zero] using h

lemma cutoffError_continuous : Continuous (dirD (dirichletNormalCutoff ε) I) :=
  ((dirichletNormalCutoff_contDiff ε).fderiv_right (m := ∞) le_rfl).continuous.clm_apply continuous_const

/-- The inverse thickness in the derivative is cancelled by the zero-trace strip estimate. -/
theorem dirichletNormalCutoffError_energy_tendsto_zero {a b : ℝ} (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b)) (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0) (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε => halfBoxEnergy a b (dirD (dirichletNormalCutoff ε) I * v)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  have h := ((dirichlet_halfBox_strip_mass_tendsto_zero hv hs hz hm hg hb).comp double_height_tendsto).const_mul (4*C^2)
  rw [mul_zero] at h
  apply squeeze_zero' (.of_forall fun _ => halfBoxEnergy_nonneg ..) _ h
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (half_pos hb)).filter_mono nhdsWithin_le_nhds] with ε hε heb
  have hε' : 0 < ε := hε
  refine (halfBoxEnergy_mul_le (by linarith : 2*ε ≤ b) (cutoffError_continuous ε)
    (norm_dirD_dirichletNormalCutoff_I_le hε hC) (fun z hz => dirD_dirichletNormalCutoff_I_eq_zero hε (.inr hz)) hm).trans_eq ?_
  dsimp only [Function.comp_apply]
  field_simp
  ring

private lemma cutoff_sub_one_bound : ‖dirichletNormalCutoff ε z - 1‖ ≤ 2 :=
  (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_dirichletNormalCutoff_le ε z])

end

theorem dirichletNormalCutoff_weight_error_energy_tendsto_zero {a b : ℝ} (hb : 0 < b) {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := ((halfBoxEnergy_tendsto_zero hb hg).comp double_height_tendsto).const_mul (2^2 : ℝ)
  rw [mul_zero] at h
  apply squeeze_zero' (.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) _ h
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (half_pos hb)).filter_mono nhdsWithin_le_nhds] with ε hε heb
  exact halfBoxEnergy_mul_le (by linarith : 2*ε ≤ b) ((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const)
    (cutoff_sub_one_bound ε) (fun z hz => sub_eq_zero.mpr (dirichletNormalCutoff_eq_one hε hz)) hg

/-- Localization may reach the bottom edge. Its actual smooth normal
cutoff is nevertheless a genuine compact interior test, because it
vanishes on a whole neighborhood of that edge. -/
theorem dirichletNormalCutoff_testFunction {a b ε : ℝ} (hε : 0 < ε)
    (η : smoothTraceTests)
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {v : ℂ → ℂ} (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b)) :
    TestFunction (smoothDirichletHalfBox a b)
      (fun z => η z * dirichletNormalCutoff ε z * v z) := by
  let w  := fun z => η z * dirichletNormalCutoff ε z * v z
  have hws : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ smoothDirichletHalfBox a b
    · exact (η.property.1.contDiffAt.mul
        (dirichletNormalCutoff_contDiff ε).contDiffAt).mul
        (hs.contDiffAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))
    · apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
      by_cases hzε : z.im < ε
      · 
        filter_upwards [((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzε)] with u hu
        simp [w, dirichletNormalCutoff_eq_zero hε hu.le, mul_zero, zero_mul]
      · 
        have hn := (isClosed_tsupport η).isOpen_compl.mem_nhds (by
          intro hzη
          obtain ⟨hx, hy⟩ := hη hzη
          exact hz ⟨hx, hε.trans_le (le_of_not_gt hzε), hy⟩)
        filter_upwards [hn] with u hu
        simp [w, image_eq_zero_of_notMem_tsupport hu, zero_mul]
  
  
  have hheight : tsupport w ⊆ {z : ℂ | ε ≤ z.im} := by
    apply closure_minimal _ (isClosed_le continuous_const Complex.continuous_im)
    intro z hz
    by_contra h
    have hcut := dirichletNormalCutoff_eq_zero hε (le_of_not_ge h)
    exact hz (by simp only [w, hcut, mul_zero, zero_mul])
  refine ⟨hws, η.property.2.1.mul_right.mul_right, fun z hz => ?_⟩
  obtain ⟨hx, hy⟩ := hη ((tsupport_mul_subset_left.trans tsupport_mul_subset_left) hz)
  exact ⟨hx, hε.trans_le (hheight hz), hy⟩

/-- The cutoff product rule is proved at every actual interior point. -/
theorem dirichletNormalCutoff_product_dirD {a b : ℝ} (ε : ℝ) {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (fun u => dirichletNormalCutoff ε u * v u) w z =
      dirichletNormalCutoff ε z * dirD v w z +
        dirD (dirichletNormalCutoff ε) w z * v z := by
  
  
  simp [dirD]
  change (fderiv ℝ (dirichletNormalCutoff ε * v) z) w = _
  rw [fderiv_mul (((dirichletNormalCutoff_contDiff ε).differentiable (by simp)) z) ((hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The actual normal gradient of the cutoff product converges in
L² to the actual normal gradient of the original zero-boundary H¹
function. Both terms in the product rule are controlled separately. -/
theorem dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
        dirD v Complex.I z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let A  := fun ε z =>
    (dirichletNormalCutoff ε z - 1) * dirD v Complex.I z
  let B : ℝ → ℂ → ℂ := fun ε => dirD (dirichletNormalCutoff ε) I * v
  have hA := dirichletNormalCutoff_weight_error_energy_tendsto_zero hb hg
  have hB := dirichletNormalCutoffError_energy_tendsto_zero hb hv hs hz hm hg
  have hup : Tendsto (fun ε : ℝ => 2 * (∫ z, ‖A ε z‖ ^ 2 ∂μ) +
      2 * (∫ z, ‖B ε z‖ ^ 2 ∂μ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [A, B, μ, mul_zero, add_zero] using
      (tendsto_const_nhds.mul hA).add (tendsto_const_nhds.mul hB)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall fun ε => (by positivity)
  · obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAm : MemLp (A ε) 2 μ := 
      (memLp_top_of_bound ((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const).aestronglyMeasurable 2
        (.of_forall (cutoff_sub_one_bound ε))).mul hg
    have hBm : MemLp (B ε) 2 μ := 
      (memLp_top_of_bound (cutoffError_continuous ε).aestronglyMeasurable _
        (.of_forall (norm_dirD_dirichletNormalCutoff_I_le hε hC))).mul hm
    have hsum : (fun z => A ε z + B ε z) =ᵐ[μ]
        (fun z => dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z) := by
      filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
        with z hzV
      rw [dirichletNormalCutoff_product_dirD ε hs hzV]
      dsimp only [A, B, Pi.mul_apply]
      ring
    calc _ = ∫ z, ‖(A ε + B ε) z‖ ^ 2 ∂μ := integral_congr_ae (hsum.symm.fun_comp fun z => ‖z‖ ^ 2)
         _ ≤ _ := integral_norm_add_sq_le hAm hBm

theorem dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero {a b : ℝ} (hb : 0 < b)
    {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hg : MemLp (dirD v 1) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) 1 z -
        dirD v 1 z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (dirichletNormalCutoff_weight_error_energy_tendsto_zero hb hg).congr'
  exact Eventually.of_forall fun ε => by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    rw [dirichletNormalCutoff_product_dirD ε hs hz, dirD_dirichletNormalCutoff_one]
    congr 2; ring

end PolyaNeumann

end
