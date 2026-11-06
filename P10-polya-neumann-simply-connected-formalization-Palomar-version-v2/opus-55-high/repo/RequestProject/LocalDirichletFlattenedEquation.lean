module

public import RequestProject.LocalDirichletBoundaryRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual divergence equation after graph flattening

The coefficients below are those of the genuine smooth graph chart,
`[[1, -f′], [-f′, 1 + f′²]]`. Their divergence is proved equal to the
physical Laplacian. The proof differentiates the actual pulled-back
physical gradient fields; it does not assume an elliptic equation or
boundary second derivatives of the constructed solution.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff ComplexConjugate

/-- Real bilinearity alone gives invariance of the trace under a
unit rotation. Symmetry of the bilinear map is not needed. -/
theorem dirichlet_bilinear_rotated_trace (T : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)
    {e : ℂ} (he : ‖e‖ = 1) :
    T e e + T (Complex.I * e) (Complex.I * e) = T 1 1 + T Complex.I Complex.I := by
  let a := e.re
  let b := e.im
  have hE : e = a • 1 + b • Complex.I := by
    continuity
  have hIE : Complex.I * e = (-b) • 1 + a • Complex.I := by
    apply Complex.ext <;> simp [a, b]
  have hsC : (a : ℂ) ^ 2 + b ^ 2 = 1 := by exact_mod_cast (by
    have h := congrArg (fun r  => r ^ 2) he
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    linarith)
  rw [congrArg (fun w => T w w) hE, congrArg (fun w => T w w) hIE]
  simp only [map_add, ContinuousLinearMap.map_smul]
  simp 
  grind

theorem dirichlet_rotated_lap {v : ℂ → ℂ} {z e : ℂ}
    (hv : ContDiffAt ℝ 2 v z) (he : ‖e‖ = 1) :
    dirD (dirD v e) e z + dirD (dirD v (Complex.I * e)) (Complex.I * e) z = lap v z := by
  have hD (w : ℂ) : dirD (dirD v w) w z = fderiv ℝ (fderiv ℝ v) z w w := by
    change fderiv ℝ (fun u => fderiv ℝ v u w) z w = _
    simp [fderiv_clm_apply ((hv.fderiv_right  (by norm_num)).differentiableAt one_ne_zero) (differentiableAt_const w)] 
  rw [hD, hD, lap, hD, hD]
  exact dirichlet_bilinear_rotated_trace _ he

/-- The actual real graph slope, regarded as a complex scalar. -/
def dirichletGraphSlope (f : ℝ → ℝ) (z : ℂ) : ℂ := ((deriv f z.re : ℝ) : ℂ)

theorem dirichletGraphSlope_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletGraphSlope f) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_infty_iff_deriv.mp hf).2.comp Complex.reCLM.contDiff)

@[simp] theorem dirD_dirichletGraphSlope_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletGraphSlope f) Complex.I z = 0 := by
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z Complex.I = 0
  rw [(Complex.ofRealCLM.hasFDerivAt.comp z
    ((((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)).fderiv]
  simp 

/-- The flux of the actual graph coefficient matrix. -/
def dirichletFlattenedFlux (f : ℝ → ℝ) (u : ℂ → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD u 1 z - dirichletGraphSlope f z * dirD u Complex.I z,
    -dirichletGraphSlope f z * dirD u 1 z +
      (1 + dirichletGraphSlope f z ^ 2) * dirD u Complex.I z] i

def dirichletFlattenedDivergence (f : ℝ → ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletFlattenedFlux f u 0) 1 z +
    dirD (dirichletFlattenedFlux f u 1) Complex.I z

theorem dirichletFlattenedFlux_pullback (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 0 z = dirD v (1 / c) (Ψ z)) ∧
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 1 z =
       dirD v (Complex.I / c) (Ψ z) - dirichletGraphSlope f z * dirD v (1 / c) (Ψ z)) := by
  have h := smoothDirichletGraphChart_pullback_gradient p c hc hf hv
  constructor
  · simpa only [dirichletFlattenedFlux, Matrix.cons_val_zero, dirichletGraphSlope, dirD]
      using h.1
  · let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
    let u := v ∘ Ψ
    let d := dirichletGraphSlope f z
    have hX : dirD u 1 z - d * dirD u Complex.I z = dirD v (1 / c) (Ψ z) := h.1
    have hY : dirD u Complex.I z = dirD v (Complex.I / c) (Ψ z) := h.2
    change -d * dirD u 1 z + (1 + d ^ 2) * dirD u Complex.I z = _
    grind

/-- This is a pointwise identity for the actual physical function
and the actual graph chart. In particular, the resulting divergence
equation is not an additional assumption about the flattened solution. -/
theorem dirichletFlattenedDivergence_pullback {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    dirichletFlattenedDivergence f
      (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) z =
      lap v (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := v ∘ Ψ
  let g₀ := dirD v (1 / c)
  let g₁ := dirD v (Complex.I / c)
  have hvc := hv.contDiffAt (hΩ.mem_nhds hz)
  have hdg (w : ℂ) : DifferentiableAt ℝ (dirD v w) (Ψ z) :=
    ((hvc.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hn  := Ψ.continuous.continuousAt.eventually (hΩ.mem_nhds hz)
  have h₀ : dirichletFlattenedFlux f u 0 =ᶠ[𝓝 z] g₀ ∘ Ψ := by
    filter_upwards [hn] with w hw
    exact (dirichletFlattenedFlux_pullback p c hc hf
      ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).1
  have h₁ : dirichletFlattenedFlux f u 1 =ᶠ[𝓝 z]
      (fun w => g₁ (Ψ w) - dirichletGraphSlope f w * g₀ (Ψ w)) := by
    filter_upwards [hn] with w hw
    exact (dirichletFlattenedFlux_pullback p c hc hf
      ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).2
  have hcompI (g : ℂ → ℂ) (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) Complex.I z = dirD g (Complex.I / c) (Ψ z) :=
    (smoothDirichletGraphChart_pullback_gradient p c hc hf hg).2
  have hcompOne (g : ℂ → ℂ) (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) 1 z = dirD g (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g (Complex.I / c) (Ψ z) := by
    have he := sub_eq_iff_eq_add.mp (smoothDirichletGraphChart_pullback_gradient p c hc hf hg).1
    continuity
  have hD₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD g₀ (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    change fderiv ℝ (dirichletFlattenedFlux f u 0) z 1 = _
    rw [h₀.fderiv_eq ]
    continuity
  have hD₁ : dirD (dirichletFlattenedFlux f u 1) Complex.I z =
      dirD g₁ (Complex.I / c) (Ψ z) -
        dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    have hgs := (dirichletGraphSlope_contDiff hf).differentiable (by simp)
    have hd₀  := (hdg (1 / c)).comp z hdΨ
    change fderiv ℝ (dirichletFlattenedFlux f u 1) z Complex.I = _
    rw [h₁.fderiv_eq ]
    change fderiv ℝ ((g₁ ∘ Ψ) - (dirichletGraphSlope f * (g₀ ∘ Ψ))) z Complex.I = _
    rw [fderiv_sub ((hdg (Complex.I / c)).comp z hdΨ) ((hgs z).mul hd₀), fderiv_mul (hgs z) hd₀]
    change dirD (g₁ ∘ Ψ) Complex.I z -
      (dirichletGraphSlope f z * dirD (g₀ ∘ Ψ) Complex.I z +
        g₀ (Ψ z) * dirD (dirichletGraphSlope f) Complex.I z) = _
    continuity
  calc
    _ = dirD g₀ (1 / c) (Ψ z) + dirD g₁ (Complex.I / c) (Ψ z) := by
      rw [dirichletFlattenedDivergence, hD₀, hD₁]
      ring
    _ = lap v (Ψ z) := by
      simpa only [g₀, g₁, div_eq_mul_inv, one_mul] using dirichlet_rotated_lap (hvc.of_le (WithTop.coe_le_coe.mpr le_top)) (by simp_all)

/-- Total directional derivatives of a function smooth on an open
set are again smooth on that same open set. -/
theorem dirichlet_contDiffOn_dirD {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (w : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirD g w) U := by
  intro z hz
  exact (((hg.contDiffAt (hU.mem_nhds hz)).fderiv_right
     le_rfl).clm_apply contDiffAt_const).contDiffWithinAt

/-- Local smoothness plus a genuine compact test suffices for this
integrability statement. No global second-derivative energy is used. -/
theorem dirichlet_local_smooth_mul_test_integrable {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hφ : TestFunction U φ) :
    IntegrableOn (fun z => g z * φ z) U := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have heq : (fun z => g z * φ z) = (fun z => G z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · simp [(hGg z hz).self_of_nhds]
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [heq]
  exact (hG.memLp' 2).integrable_mul (hφ.memLp' 2)

theorem dirichlet_local_smooth_field_test_eq_neg_dirD {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hφ : TestFunction U φ)
    (i : Fin 2) :
    (∫ z in U, g z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD g (coordDir i) z * φ z) := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have hu := hG.memLp' 2 (μ := volume.restrict U)
  have hgrad (j : Fin 2) := (hG.dirD (coordDir j)).memLp' 2 (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth hG.1 hu hgrad φ hφ i
  have hl : (fun z => hu.toLp G z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => g z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · simp [(hGg z hz).self_of_nhds]
    simp [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
  have hr : (fun z => (hgrad i).toLp _ z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD g (coordDir i) z * φ z) := by
    filter_upwards [(hgrad i).coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · simp [show dirD G (coordDir i) z = dirD g (coordDir i) z from         congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i))           ((hGg z hz).fderiv_eq )]
    simp [image_eq_zero_of_notMem_tsupport hz]
  change (∫ z in U, hu.toLp G z * dirD φ (coordDir i) z) =
    -(∫ z in U, (hgrad i).toLp _ z * φ z) at hw
  simp_all [integral_congr_ae hl, integral_congr_ae hr]

theorem dirichletFlattenedFlux_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletFlattenedFlux f u i) U := by
  have hx := dirichlet_contDiffOn_dirD hU hu 1
  have hy := dirichlet_contDiffOn_dirD hU hu Complex.I
  have hd := (dirichletGraphSlope_contDiff hf).contDiffOn (s := U)
  fin_cases i
  · exact hx.sub (hd.mul hy)
  · exact (hd.neg.mul hx).add ((contDiffOn_const.add (hd.pow 2)).mul hy)

theorem riemannMappingDirichletRemainder_contDiffOn {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    (d : smoothTraceTests) :
    ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F d) Ω :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)).sub
      d.property.1.contDiffOn

/-- Every actual smooth datum gives this physical Laplacian identity;
the selected datum is needed only for the separately proved zero
boundary values. -/
theorem riemannMappingDirichletRemainder_lap {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    (d : smoothTraceTests) {z : ℂ} (hz : z ∈ Ω) :
    lap (riemannMappingDirichletRemainder F d) z = -lap d z := by
  have hharm := (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
    Complex.ofRealCLM
  have hh := (hharm z hz).1
  exact (lap_sub_of_contDiffAt hh (d.property.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))).trans (by
    simp [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds])

/-! ### Actual zero-boundary test approximation -/

theorem dirichlet_bounded_mul_memLp {μ : Measure ℂ} {a g : ℂ → ℂ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hbound : ∀ z, ‖a z‖ ≤ C)
    (hg : MemLp g 2 μ) : MemLp (fun z => a z * g z) 2 μ := by
  apply hg.of_le_mul  (ha.mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖a z * g z‖ ≤ C * ‖g z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _)

theorem dirichlet_localized_memLp {μ : Measure ℂ} (η : smoothTraceTests) {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) : MemLp (fun z => η z * g z) 2 μ := by
  obtain ⟨C, hC⟩ := η.property.2.1.exists_bound_of_continuous η.property.1.continuous
  exact dirichlet_bounded_mul_memLp η.property.1.continuous.aestronglyMeasurable hC hg

theorem dirichlet_localized_dirD {U : Set ℂ} (hU : IsOpen U) (η : smoothTraceTests)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) {z : ℂ} (hz : z ∈ U) (w : ℂ) :
    dirD (fun u => η u * g u) w z = η z * dirD g w z + dirD η w z * g z := by
  change fderiv ℝ ((η : ℂ → ℂ) * g) z w = _
  rw [fderiv_mul (η.property.1.differentiable (by simp) z) ((hg.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dirD]
  ring

theorem dirichlet_localized_gradient_memLp {U : Set ℂ} (hU : IsOpen U)
    (η : smoothTraceTests) {g : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hm : MemLp g 2 (volume.restrict U)) {i : Fin 2}
    (hg : MemLp (dirD g (coordDir i)) 2 (volume.restrict U)) :
    MemLp (dirD (fun z => η z * g z) (coordDir i)) 2 (volume.restrict U) := by
  let dη : smoothTraceTests := ⟨dirD η (coordDir i), η.property.dirD (coordDir i)⟩
  apply ((dirichlet_localized_memLp η hg).add (dirichlet_localized_memLp dη hm)).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  exact (dirichlet_localized_dirD hU η hs hz (coordDir i)).symm

/-- These are genuine compact interior tests, with convergence in
all three actual H¹ energies. The localization can touch the flat
boundary; its sides and top remain inside the coordinate rectangle. -/
theorem dirichlet_localized_zero_boundary_test_approximation {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g x = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    (let v := fun z => η z * g z
     (∀ ε : ℝ, 0 < ε → TestFunction (smoothDirichletHalfBox a b)
       (fun z => dirichletNormalCutoff ε z * v z)) ∧
     Tendsto (fun ε  => ∫ z in smoothDirichletHalfBox a b,
       ‖dirichletNormalCutoff ε z * v z - v z‖ ^ 2) (𝓝[>] 0) (𝓝 0) ∧
     ∀ i : Fin 2, Tendsto (fun ε  => ∫ z in smoothDirichletHalfBox a b,
       ‖dirD (fun u => dirichletNormalCutoff ε u * v u) (coordDir i) z -
         dirD v (coordDir i) z‖ ^ 2) (𝓝[>] 0) (𝓝 0)) := by
  let v  := fun z => η z * g z
  have hvS  :=
    η.property.1.contDiffOn.mul hs
  have hvz : ∀ x : ℝ, |x| < a → v x = 0 := by
    grind
  have hvm := dirichlet_localized_memLp η hm
  have hvg (i : Fin 2) := dirichlet_localized_gradient_memLp
    (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have htest := dirichletNormalCutoff_testFunction hε η hη hs
    grind
  · have h := dirichletNormalCutoff_weight_error_energy_tendsto_zero hvm
    grind
  · intro i
    fin_cases i
    · apply dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero hvS
      continuity
    · apply dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero hb (η.property.1.continuous.continuousOn.mul hc) hvS hvz hvm
      continuity

theorem dirichlet_eLpNorm_toReal_eq_sqrt_energy {μ : Measure ℂ} {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) :
    (eLpNorm g 2 μ).toReal = Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂μ) := by
  rw [← Lp.norm_toLp g hg, ← norm_sq_toLp_eq_integral hg,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Actual L² energy convergence gives convergence of pairing
against any fixed actual L² function. This is the Cauchy–Schwarz
step needed to pass genuine interior tests to the boundary. -/
theorem dirichlet_pairing_tendsto_zero_of_energy {μ : Measure ℂ}
    {g : ℂ → ℂ} (hg : MemLp g 2 μ) {e : ℝ → ℂ → ℂ}
    (he : ∀ᶠ ε : ℝ in 𝓝[>] 0, MemLp (e ε) 2 μ)
    (hE : Tendsto (fun ε  => ∫ z, ‖e ε z‖ ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε  => ∫ z, g z * e ε z ∂μ) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hup : Tendsto (fun ε  => (eLpNorm g 2 μ).toReal *
      Real.sqrt (∫ z, ‖e ε z‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hE)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · norm_num
  · filter_upwards [he] with ε hε
    simpa only [dirichlet_eLpNorm_toReal_eq_sqrt_energy hε] using
      norm_integral_mul_le_eLpNorm hg hε

theorem dirichlet_pairing_tendsto_of_energy_approximation {μ : Measure ℂ}
    {g k : ℂ → ℂ} (hg : MemLp g 2 μ) (hk : MemLp k 2 μ) {kε : ℝ → ℂ → ℂ}
    (hmem : ∀ᶠ ε : ℝ in 𝓝[>] 0, MemLp (kε ε) 2 μ)
    (hE : Tendsto (fun ε  => ∫ z, ‖kε ε z - k z‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε  => ∫ z, g z * kε ε z ∂μ) (𝓝[>] 0)
      (𝓝 (∫ z, g z * k z ∂μ)) := by
  have hplus := (dirichlet_pairing_tendsto_zero_of_energy hg (hmem.mono fun _ h => h.sub hk) hE).add (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ∫ z, g z * k z ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z * k z ∂μ)))
  have hplus' : Tendsto (fun ε  =>
      (∫ z, g z * (kε ε z - k z) ∂μ) + ∫ z, g z * k z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z, g z * k z ∂μ)) := by
    simp_all
  apply hplus'.congr'
  filter_upwards [hmem] with ε hε
  simp_rw [mul_sub]
  have hiε : Integrable (fun z => g z * kε ε z) μ := hg.integrable_mul hε
  have hik : Integrable (fun z => g z * k z) μ := hg.integrable_mul hk
  simp [integral_sub hiε hik]

/-- The passage from actual compact interior tests to a localized
zero-boundary H¹ test. Its convergence and integrability are proved
above, and no density or boundary smoothness assumption is made. -/
theorem dirichlet_weak_equation_localized_zero_boundary_test {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g x = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {F : Fin 2 → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ i : Fin 2, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2, F i z * dirD φ (coordDir i) z) =
        ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
      F i z * dirD (fun u => η u * g u) (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * (η z * g z) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let v  := fun z => η z * g z
  let vε  := fun ε z => dirichletNormalCutoff ε z * v z
  obtain ⟨htest, hvalue, hgradient⟩ :=
    dirichlet_localized_zero_boundary_test_approximation hb η hη hc hs hz hm hg
  have hvg (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  have hεg (i : Fin 2) : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      MemLp (dirD (vε ε) (coordDir i)) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((htest ε hε).dirD (coordDir i)).memLp' 2
  have hleft (i : Fin 2) : Tendsto
      (fun ε  => ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z, F i z * dirD v (coordDir i) z ∂μ)) :=
    dirichlet_pairing_tendsto_of_energy_approximation (hF i) (hvg i) (hεg i) (hgradient i)
  have heq : (fun ε  => ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      =ᶠ[𝓝[>] 0] (fun ε  => ∫ z, G z * vε ε z ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hisum : (∫ z, ∑ i : Fin 2, F i z * dirD (vε ε) (coordDir i) z ∂μ) =
        ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ := by
      apply integral_finset_sum
      intro i _
      exact (hF i).integrable_mul (((htest ε hε).dirD (coordDir i)).memLp' 2)
    grind
  have hlim  := tendsto_nhds_unique (tendsto_finset_sum Finset.univ (fun i _ => hleft i)) ((dirichlet_pairing_tendsto_of_energy_approximation hG (dirichlet_localized_memLp η hm) (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (htest ε hε).memLp' 2) hvalue).congr' heq.symm)
  have hisum : (∫ z, ∑ i : Fin 2, F i z * dirD v (coordDir i) z ∂μ) =
      ∑ i : Fin 2, ∫ z, F i z * dirD v (coordDir i) z ∂μ := by
    apply integral_finset_sum
    intro i _
    exact (hF i).integrable_mul (hvg i)
  grind

theorem dirichlet_halfBox_isBounded {a b : ℝ} :
    Bornology.IsBounded (smoothDirichletHalfBox a b) := by
  apply (isBounded_closedBall  ).subset
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ a + b := add_le_add hz.1.le (by rw [abs_of_pos hz.2.1]; exact hz.2.2.le)

/-- The actual tangential difference quotient, with ordinary real
translation and the physical complex scalar normalization. -/
def dirichletTangentialDifference (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (u (z + (h : ℂ)) - u z) / (h : ℂ)

theorem dirichlet_continuousOn_memLp_Ioc {a b : ℝ} {v : ℝ → ℂ}
    (hv : ContinuousOn v (Icc a b)) :
    MemLp v 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((hv.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
  exact (hv.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The difference quotient of an actual differentiable interval
function has an L² bound independent of the step. This is an
ordinary FTC/Cauchy--Schwarz/Fubini estimate, with no derivative
assumed at a physical boundary. -/
theorem dirichlet_interval_difference_energy_le {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) {v dv : ℝ → ℂ}
    (hv : ContinuousOn v (Icc (-a) (a + h)))
    (hdv : ContinuousOn dv (Icc (-a) (a + h)))
    (hd : ∀ x ∈ Icc (-a) (a + h), HasDerivAt v (dv x) x) :
    (∫ x in (-a)..a, ‖(v (x + h) - v x) / h‖ ^ 2) ≤
      ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2 := by
  have haa : -a ≤ a := by linarith
  have hmap (x : ℝ) (hx : x ∈ Icc (-a) a) :
      MapsTo (fun s  => x + s) (Icc 0 h) (Icc (-a) (a + h)) := by
    intro s hs
    grind
  have hpoint (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖(v (x + h) - v x) / h‖ ^ 2 ≤
        h⁻¹ * ∫ s in 0..h, ‖dv (x + s)‖ ^ 2 := by
    have hds (s : ℝ) (hs : s ∈ Ioo 0 h) :
        HasDerivAt (fun t  => v (x + t) - v x) (dv (x + s)) s := by
      simpa only [one_smul, Function.comp_apply] using
        ((hd (x + s) (hmap x hx (Ioo_subset_Icc_self hs))).scomp s
          ((hasDerivAt_id s).const_add x)).sub_const (v x)
    have hp := dirichlet_zero_endpoint_norm_sq_le ((hv.comp (continuous_const.add continuous_id).continuousOn (hmap x hx)).sub
        continuousOn_const)
      (by simp) hds (dirichlet_continuousOn_memLp_Ioc (hdv.comp (continuous_const.add continuous_id).continuousOn (hmap x hx)))
      (⟨hh, le_rfl⟩)
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_pow] at hp ⊢
    apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
    calc
      ‖v (x + h) - v x‖ ^ 2 ≤ h * ∫ s in 0..h, ‖dv (x + s)‖ ^ 2 := hp
      _ = (h⁻¹ * ∫ s in 0..h, ‖dv (x + s)‖ ^ 2) * h ^ 2 := by
        field_simp 
  let E : ℝ × ℝ → ℝ := fun p => ‖dv (p.1 + p.2)‖ ^ 2
  have hiE : Integrable E
      ((volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc 0 h))) := by
    rw [Measure.prod_restrict]
    exact (((hdv.norm.pow 2).comp (continuous_fst.add continuous_snd).continuousOn
      (fun p hp => hmap p.1 hp.1 hp.2)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hq : ContinuousOn (fun x  => ‖(v (x + h) - v x) / h‖ ^ 2)
      (Icc (-a) a) := by
    have hx : MapsTo (fun x  => x + h) (Icc (-a) a) (Icc (-a) (a + h)) := by
      intro x hx
      grind
    exact (((hv.comp (continuous_id.add continuous_const).continuousOn hx).sub
      (hv.mono (Icc_subset_Icc le_rfl (by linarith)))).div_const h).norm.pow 2
  have hswap : (∫ x in (-a)..a, ∫ s in 0..h, E (x, s)) =
      ∫ s in 0..h, ∫ x in (-a)..a, E (x, s) := by
    simp only [intervalIntegral.integral_of_le haa, intervalIntegral.integral_of_le hh.le]
    exact integral_integral_swap hiE
  calc
    _ ≤ h⁻¹ * ∫ x in (-a)..a, ∫ s in 0..h, E (x, s) := (by
    rw [intervalIntegral.integral_of_le haa,
      intervalIntegral.integral_of_le haa, ← integral_const_mul]
    apply integral_mono_ae (hq.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (by
    simpa only [intervalIntegral.integral_of_le hh.le] using hiE.integral_prod_left.const_mul h⁻¹)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    grind)
    _ = h⁻¹ * ∫ s in 0..h, ∫ x in (-a)..a, E (x, s) := by simp_all
    _ ≤ h⁻¹ * (h * ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by
    have hi : IntervalIntegrable (fun s  => ∫ x in (-a)..a, E (x, s))
        volume 0 h := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
      simpa only [IntegrableOn, intervalIntegral.integral_of_le haa] using hiE.integral_prod_right
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo hh.le hi
      (intervalIntegrable_const )
      (fun s hs => by
        rw [intervalIntegral.integral_comp_add_right
          (f := fun x  => ‖dv x‖ ^ 2) s]
        apply intervalIntegral.integral_mono_interval (by grind)
          (by linarith) (by grind)
          (Eventually.of_forall fun x => sq_nonneg _) ((hdv.norm.pow 2).intervalIntegrable_of_Icc (by linarith)))
    simp_all) (inv_nonneg.mpr hh.le)
    _ = _ := by field_simp

/-- Translation preserves actual L² membership on a smaller half
box. The image inclusion is proved from the true horizontal margin,
and the composition uses an actual isometric homeomorphism. -/
theorem dirichlet_halfBox_translation_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (fun z => u (z + h)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let T : ℂ ≃ₜ ℂ := Homeomorph.addRight h
  have hT : Isometry T := by
    apply Isometry.of_dist_eq
    continuity
  have hTi : Isometry T.symm := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (z + -h) (w + -h) = dist z w
    norm_num
  exact memLp_comp_bilip'   (isOpen_smoothDirichletHalfBox a b)
    (by norm_num) hT.lipschitz.lipschitzOnWith hTi.lipschitz.lipschitzOnWith (hm.mono_measure (Measure.restrict_mono_set volume (by
    rintro w ⟨z, hz, rfl⟩
    have hx  :=
      (abs_add_le z.re h).trans_lt
        ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
    simp_all [T, smoothDirichletHalfBox])))

theorem dirichletTangentialDifference_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifference h u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hq := ((dirichlet_halfBox_translation_memLp hmargin hm).sub (hm.mono_measure (Measure.restrict_mono_set volume (by
    intro z hz
    exact ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩)))).const_smul ((h : ℂ)⁻¹)
  have he : ((h : ℂ)⁻¹ • ((fun z => u (z + h)) - u)) =
      dirichletTangentialDifference h u := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, dirichletTangentialDifference]
    ring
  simp_all

/-- The same actual area integral, with horizontal slices first.
The real-coordinate measure has exactly Jacobian one. -/
theorem dirichlet_halfBox_sq_integral_eq_horizontal_real_prod {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ y in Ioo 0 b, ∫ x in (-a)..a,
        ‖g (x + y * Complex.I)‖ ^ 2 := by
  rw [dirichlet_halfBox_sq_integral_eq_real_prod hb hg]
  simp_rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
  rw [integral_integral_swap (dirichlet_halfBox_sq_integrable_real_prod hg)]
  simp [intervalIntegral.integral_of_le (show -a ≤ a by linarith), integral_Ioc_eq_integral_Ioo]

/-- Actual finite first-derivative energy gives a uniform L²
tangential difference-quotient estimate all the way to the flat
boundary. Smoothness is used only at interior horizontal segments;
there is no assumed second derivative at the boundary. -/
theorem dirichlet_halfBox_tangential_difference_energy_le {A a b h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hmargin : a + h < A)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hDx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖dirichletTangentialDifference h u z‖ ^ 2) ≤
      ∫ z in smoothDirichletHalfBox A b, ‖dirD u 1 z‖ ^ 2 := by
  have hA  := lt_trans ha (lt_trans (by linarith) hmargin)
  have hq := dirichletTangentialDifference_memLp
    (show a + |h| ≤ A by grind) hm
  have hprodD := dirichlet_halfBox_sq_integrable_real_prod hDx
  have hqi : Integrable (fun y : ℝ => ∫ x in (-a)..a,
      ‖dirichletTangentialDifference h u (x + y * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo 0 b)) := by
    simpa only [intervalIntegral.integral_of_le (show -a ≤ a by linarith),
      integral_Ioc_eq_integral_Ioo] using (dirichlet_halfBox_sq_integrable_real_prod hq).integral_prod_right
  have hdi : Integrable (fun y : ℝ => ∫ x in (-A)..A,
      ‖dirD u 1 (x + y * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo 0 b)) := by
    simpa only [intervalIntegral.integral_of_le (show -A ≤ A by linarith),
      integral_Ioc_eq_integral_Ioo] using hprodD.integral_prod_right
  rw [dirichlet_halfBox_sq_integral_eq_horizontal_real_prod ha hb hq,
    dirichlet_halfBox_sq_integral_eq_horizontal_real_prod hA hb hDx]
  exact integral_mono_ae hqi hdi (by
    filter_upwards [hprodD.prod_left_ae, ae_restrict_mem measurableSet_Ioo]
      with y hdy hy
    let L : ℝ → ℂ := fun x => x + y * Complex.I
    have hLc : Continuous L := Complex.ofRealCLM.continuous.add continuous_const
    have hmap : MapsTo L (Icc (-a) (a + h)) (smoothDirichletHalfBox A b) := by
      intro x hx
      have hxA  := abs_lt.mpr ⟨by grind, hx.2.trans_lt hmargin⟩
      simp_all [L, smoothDirichletHalfBox]
    have hd (x : ℝ) (hx : x ∈ Icc (-a) (a + h)) :
        HasDerivAt (u ∘ L) ((dirD u 1 ∘ L) x) x := ((hs.contDiffAt
        ((isOpen_smoothDirichletHalfBox A b).mem_nhds (hmap hx))).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt x (((hasDerivAt_id x).ofReal_comp).add_const (y * Complex.I))
    have hi := dirichlet_interval_difference_energy_le ha hh (hs.continuousOn.comp hLc.continuousOn hmap) ((dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs 1).continuousOn.comp hLc.continuousOn hmap) hd
    have hmono := intervalIntegral.integral_mono_interval
      (show -A ≤ -a by linarith) (by linarith) hmargin.le
      (Eventually.of_forall fun x => sq_nonneg _) (by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Ioc] using hdy)
    have hi' : (∫ x in (-a)..a,
        ‖dirichletTangentialDifference h u (L x)‖ ^ 2) ≤
        ∫ x in (-a)..(a + h), ‖dirD u 1 (L x)‖ ^ 2 := by
      simp_all [dirichletTangentialDifference, L, add_right_comm]
    linarith)

/-- Every fixed tangential difference quotient is a genuine H¹
function on the smaller half box. Its derivative is the difference
quotient of the actual first derivative; this is proved from the
ordinary chain rule, not from an assumed H² bound. -/
theorem dirichletTangentialDifference_dirD {h : ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ u z) (hzh : DifferentiableAt ℝ u (z + h)) (w : ℂ) :
    dirD (dirichletTangentialDifference h u) w z =
      dirichletTangentialDifference h (dirD u w) z := by
  have hT : HasFDerivAt (fun z : ℂ => z + h)
      (ContinuousLinearMap.id ℝ ℂ) z := (hasFDerivAt_id z).add_const (h : ℂ)
  have hq : HasFDerivAt (dirichletTangentialDifference h u)
      ((h : ℂ)⁻¹ • (fderiv ℝ u (z + h) - fderiv ℝ u z)) z := by
    have hfun : dirichletTangentialDifference h u =
        fun y => ((u ∘ fun z => z + h) - u) y * (h : ℂ)⁻¹ := by
      rfl
    rw [hfun]
    simpa only [ContinuousLinearMap.comp_id] using
      ((hzh.hasFDerivAt.comp z hT).sub hz.hasFDerivAt).mul_const (h⁻¹)
  change fderiv ℝ (dirichletTangentialDifference h u) z w = _
  rw [hq.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    dirichletTangentialDifference, dirD]
  ring

theorem dirichletTangentialDifference_continuousOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifference h u) (smoothDirichletClosedHalfBox a b) := ((hc.comp (continuous_id.add continuous_const).continuousOn (by
    intro z hz
    have hx  :=
      (abs_add_le z.re h).trans
        ((add_le_add hz.1 le_rfl).trans hmargin)
    simp_all [smoothDirichletClosedHalfBox])).sub
    (hc.mono (by
    intro z hz
    exact ⟨hz.1.trans (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩))).div_const h

theorem dirichletTangentialDifference_contDiffOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDifference h u)
      (smoothDirichletHalfBox a b) := ((hs.comp (contDiff_id.add contDiff_const).contDiffOn (by
    intro z hz
    have hx  :=
      (abs_add_le z.re h).trans_lt
        ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
    simp_all [smoothDirichletHalfBox])).sub
    (hs.mono (by
    intro z hz
    exact ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩))).div_const h

theorem dirichletTangentialDifference_zero_bottom {A a h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hz : ∀ x : ℝ, |x| < A → u x = 0) {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifference h u x = 0 := by
  simp [dirichletTangentialDifference, ← Complex.ofReal_add, hz x (hx.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin)), hz (x + h) ((abs_add_le x h).trans_lt       ((add_lt_add_of_lt_of_le hx le_rfl).trans_le hmargin))]

/-- The actual coefficient matrix at the shifted horizontal point,
acting on the gradient at the original point. -/
def dirichletShiftedFlux (f : ℝ → ℝ) (h : ℝ) (v : ℂ → ℂ)
    (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD v 1 z - dirichletGraphSlope f (z + (h : ℂ)) * dirD v Complex.I z,
    -dirichletGraphSlope f (z + (h : ℂ)) * dirD v 1 z +
      (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) * dirD v Complex.I z] i

private theorem dirichlet_energy_young {M : ℝ} (hM : 0 < M) (Y S : ℝ) :
    Y * S ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := by
  have hfourM : 0 < 4 * M := mul_pos (by norm_num) hM
  have hpoly : 4 * M * Y * S ≤ Y ^ 2 + 4 * M ^ 2 * S ^ 2 := by
    nlinarith only [sq_nonneg (Y - 2 * M * S)]
  calc
    Y * S = (4 * M * Y * S) / (4 * M) := by field_simp
    _ ≤ (Y ^ 2 + 4 * M ^ 2 * S ^ 2) / (4 * M) :=
      div_le_div_of_nonneg_right hpoly hfourM.le
    _ = _ := by field_simp

/-- The pointwise absorption estimate for a complex-valued
localized elliptic test. The coefficient coercivity and norm bounds
are algebraic inputs; the actual graph matrix supplies both below.
The cutoff is allowed to be complex, since its weight is `η·conj η`. -/
theorem dirichlet_localized_energy_absorption {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (η α β v x y F₀ F₁ C₀ C₁ G : ℂ)
    (hη : ‖η‖ ≤ 1) (hα : ‖α‖ ≤ B) (hβ : ‖β‖ ≤ B)
    (hcoer : (‖x‖ ^ 2 + ‖y‖ ^ 2) / M ≤ (F₀ * conj x + F₁ * conj y).re)
    (hF : ‖F₀‖ + ‖F₁‖ ≤ 2 * M * (‖x‖ + ‖y‖)) :
    let ρ := η * conj η
    let b₀ := α * conj η + η * conj α
    let b₁ := β * conj η + η * conj β
    let L := (F₀ + C₀) * (ρ * conj x + b₀ * conj v) +
      (F₁ + C₁) * (ρ * conj y + b₁ * conj v)
    ‖η‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * M) ≤
      (L - G * ρ * conj v).re + ‖G‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
  let ρ := η * conj η
  let b₀ := α * conj η + η * conj α
  let b₁ := β * conj η + η * conj β
  let L := (F₀ + C₀) * (ρ * conj x + b₀ * conj v) +
    (F₁ + C₁) * (ρ * conj y + b₁ * conj v)
  let X := ‖x‖ + ‖y‖
  let c := ‖C₀‖ + ‖C₁‖
  let Y := ‖η‖ * X
  let T := ‖η‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)
  let S := c + 4 * B * M * ‖v‖
  let main := ρ * (F₀ * conj x + F₁ * conj y)
  let err := (F₀ * b₀ + F₁ * b₁) * conj v +
    ρ * (C₀ * conj x + C₁ * conj y) +
    (C₀ * b₀ + C₁ * b₁) * conj v - G * ρ * conj v
  have hX₀ : 0 ≤ X := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hρnorm : ‖ρ‖ = ‖η‖ ^ 2 := by simp [ρ, pow_two]
  have hρ : ρ = (‖η‖ ^ 2 : ℝ) := by
    simpa only [← Complex.ofReal_pow] using Complex.mul_conj' η
  have hb₀ : ‖b₀‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ ‖α * conj η‖ + ‖η * conj α‖ := norm_add_le _ _
      _ = 2 * ‖α‖ * ‖η‖ := by simp ; ring
      _ ≤ _ := by gcongr
  have hb₁ : ‖b₁‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ ‖β * conj η‖ + ‖η * conj β‖ := norm_add_le _ _
      _ = 2 * ‖β‖ * ‖η‖ := by simp ; ring
      _ ≤ _ := by gcongr
  have hηsq : ‖η‖ ^ 2 ≤ ‖η‖ := by nlinarith only [hη, norm_nonneg η]
  have hAerr : ‖(F₀ * b₀ + F₁ * b₁) * conj v‖ ≤ 4 * B * M * Y * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (‖F₀ * b₀‖ + ‖F₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖F₀‖ * (2 * B * ‖η‖) + ‖F₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by
        simp 
        gcongr
      _ = 2 * B * ‖η‖ * (‖F₀‖ + ‖F₁‖) * ‖v‖ := by ring
      _ ≤ 2 * B * ‖η‖ * (2 * M * X) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hCmain : ‖ρ * (C₀ * conj x + C₁ * conj y)‖ ≤ c * Y := by
    rw [norm_mul, hρnorm]
    calc
      _ ≤ ‖η‖ ^ 2 * (c * X) := mul_le_mul_of_nonneg_left (by
    calc
      _ ≤ ‖C₀ * conj x‖ + ‖C₁ * conj y‖ := norm_add_le _ _
      _ = ‖C₀‖ * ‖x‖ + ‖C₁‖ * ‖y‖ := by simp 
      _ ≤ _ := by
        nlinarith only [mul_nonneg (norm_nonneg C₀) (norm_nonneg y),
          mul_nonneg (norm_nonneg C₁) (norm_nonneg x)]) (sq_nonneg _)
      _ ≤ ‖η‖ * (c * X) := mul_le_mul_of_nonneg_right hηsq (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hX₀)
      _ = _ := by ring
  have hCerr : ‖(C₀ * b₀ + C₁ * b₁) * conj v‖ ≤ 2 * B * c * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (‖C₀ * b₀‖ + ‖C₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖C₀‖ * (2 * B * ‖η‖) + ‖C₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by
        simp 
        gcongr
      _ = 2 * B * c * ‖η‖ * ‖v‖ := by ring
      _ ≤ 2 * B * c * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have hGerr : ‖G * ρ * conj v‖ ≤ ‖G‖ * ‖v‖ := by
    rw [norm_mul, norm_mul, hρnorm, norm_conj]
    have hηsq₁  := hηsq.trans hη
    calc
      _ ≤ ‖G‖ * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have herr : ‖err‖ ≤ Y * S + 2 * B * c * ‖v‖ + ‖G‖ * ‖v‖ := by
    calc
      _ ≤ ‖(F₀ * b₀ + F₁ * b₁) * conj v +
          ρ * (C₀ * conj x + C₁ * conj y) + (C₀ * b₀ + C₁ * b₁) * conj v‖ +
          ‖G * ρ * conj v‖ := norm_sub_le _ _
      _ ≤ ((‖(F₀ * b₀ + F₁ * b₁) * conj v‖ +
          ‖ρ * (C₀ * conj x + C₁ * conj y)‖) +
          ‖(C₀ * b₀ + C₁ * b₁) * conj v‖) + ‖G * ρ * conj v‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((4 * B * M * Y * ‖v‖ + c * Y) + 2 * B * c * ‖v‖) + ‖G‖ * ‖v‖ := by
        gcongr
      _ = _ := by ring
  have hYsq : Y ^ 2 ≤ 2 * T := by
    have hxy : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]
    nlinarith
  have hfourM : 0 < 4 * M := by positivity
  have hYoung' : Y * S ≤ T / (2 * M) + 2 * M * c ^ 2 +
      32 * B ^ 2 * M ^ 3 * ‖v‖ ^ 2 := by
    calc
      _ ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := dirichlet_energy_young hM Y S
      _ ≤ (2 * T) / (4 * M) + M *
          (2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2) :=
        add_le_add (div_le_div_of_nonneg_right hYsq hfourM.le)
          (mul_le_mul_of_nonneg_left (by
    nlinarith only [sq_nonneg (c - 4 * B * M * ‖v‖)]) hM.le)
      _ = _ := by ring
  have hBc : 2 * B * c * ‖v‖ ≤ B ^ 2 * c ^ 2 + ‖v‖ ^ 2 := by
    nlinarith only [sq_nonneg (B * c - ‖v‖)]
  have hGv : ‖G‖ * ‖v‖ ≤ ‖G‖ ^ 2 + ‖v‖ ^ 2 := by
    nlinarith 
  have hcsq : c ^ 2 ≤ 2 * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖C₀‖ - ‖C₁‖)]
  have herr' : ‖err‖ ≤ T / (2 * M) + ‖G‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
    have hcBound := mul_le_mul_of_nonneg_left hcsq
      (show 0 ≤ 2 * M + B ^ 2 by positivity)
    linarith 
  have hmain : T / M ≤ main.re := by
    rw [show main = (‖η‖ ^ 2 : ℝ) * (F₀ * conj x + F₁ * conj y) by grind]
    simp only [Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ = ‖η‖ ^ 2 * ((‖x‖ ^ 2 + ‖y‖ ^ 2) / M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoer (sq_nonneg _)
  have heq : L - G * ρ * conj v = main + err := by ring
  have hmainBound : main.re ≤ (L - G * ρ * conj v).re + ‖err‖ := by
    rw [heq, Complex.add_re]
    have h := Complex.re_le_norm (-err)
    simp  at h
    linarith 
  have hTsplit : T / M = T / (2 * M) + T / (2 * M) := by
    ring
  linarith 

/-- A genuine smooth compact weight, even for a complex cutoff. -/
def dirichletCutoffWeight (η : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => η z * conj (η z),
    ⟨η.property.1.mul (Complex.conjCLE.contDiff.comp η.property.1),
      η.property.2.1.mul_right, subset_univ _⟩⟩

theorem dirichlet_dirD_conj_at {u : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (w : ℂ) :
    dirD (fun z => conj (u z)) w z = conj (dirD u w z) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp z hu.hasFDerivAt).fderiv
  change fderiv ℝ (Complex.conjCLE ∘ u) z w = _
  continuity

theorem dirichletCutoffWeight_dirD (η : smoothTraceTests) (w z : ℂ) :
    dirD (dirichletCutoffWeight η) w z =
      dirD η w z * conj (η z) +
        η z * conj (dirD η w z) := by
  have hη := ((η.property.1.differentiable (by simp)) z).hasFDerivAt
  change fderiv ℝ ((η : ℂ → ℂ) * (Complex.conjCLE ∘ η)) z w = _
  rw [(hη.mul (Complex.conjCLE.hasFDerivAt.comp z hη)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_apply,
    Function.comp_apply, Complex.conjCLE_apply,
    dirD]
  ring

theorem dirichlet_cutoff_conj_product_dirD (η : smoothTraceTests)
    {v : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v z) (w : ℂ) :
    dirD (fun z => dirichletCutoffWeight η z * conj (v z)) w z =
      dirichletCutoffWeight η z * conj (dirD v w z) +
        (dirD η w z * conj (η z) +
          η z * conj (dirD η w z)) * conj (v z) := by
  change fderiv ℝ ((dirichletCutoffWeight η : ℂ → ℂ) * (Complex.conjCLE ∘ v)) z w = _
  rw [((((dirichletCutoffWeight η).property.1.differentiable (by simp)) z).hasFDerivAt.mul (Complex.conjCLE.hasFDerivAt.comp z hv.hasFDerivAt)).fderiv]
  change dirichletCutoffWeight η z * conj (dirD v w z) +
    conj (v z) * dirD (dirichletCutoffWeight η) w z = _
  rw [dirichletCutoffWeight_dirD]
  ring

/-- The genuine localized energy estimate for a zero-boundary H¹
solution of a weak elliptic equation with an L² flux commutator.
The boundary test is obtained by the proved normal-cutoff passage.
There is no assumed boundary test density or second-derivative gain. -/
theorem dirichlet_localized_boundary_energy_bound {a b M B : ℝ}
    (hb : 0 < b) (hM : 0 < M) (hB : 0 ≤ B)
    (η : smoothTraceTests)
    (hηsupp : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    (hη : ∀ z : ℂ, ‖η z‖ ≤ 1)
    (hηgrad : ∀ z : ℂ, ∀ i : Fin 2, ‖dirD η (coordDir i) z‖ ≤ B)
    {v : ℂ → ℂ} (hc : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v x = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {F C : Fin 2 → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ i : Fin 2, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hC : ∀ i : Fin 2, MemLp (C i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hcoer : ∀ z ∈ smoothDirichletHalfBox a b,
      (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / M ≤
        (F 0 z * conj (dirD v 1 z) + F 1 z * conj (dirD v Complex.I z)).re)
    (hFbound : ∀ z ∈ smoothDirichletHalfBox a b,
      ‖F 0 z‖ + ‖F 1 z‖ ≤ 2 * M * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
        (F i z + C i z) * dirD φ (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b,
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)) / (2 * M) ≤
      (∫ z in smoothDirichletHalfBox a b, ‖G z‖ ^ 2) +
        (4 * M + 2 * B ^ 2) *
          (∫ z in smoothDirichletHalfBox a b, ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) *
          (∫ z in smoothDirichletHalfBox a b, ‖v z‖ ^ 2) := by
  let U := smoothDirichletHalfBox a b
  let μ := volume.restrict U
  let φ  := fun z => dirichletCutoffWeight η z * conj (v z)
  let J  := fun z =>
    ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
  let R  := fun z =>
    (∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) - G z * φ z
  have hU  := isOpen_smoothDirichletHalfBox a b
  have hvc  :=
    Complex.conjCLE.continuous.comp_continuousOn hc
  have hvs  :=
    Complex.conjCLE.contDiff.comp_contDiffOn hs
  have hvz : ∀ x : ℝ, |x| < a → conj (v x) = 0 := by
    grind
  have hvg (i : Fin 2) : MemLp (dirD (fun z => conj (v z)) (coordDir i)) 2 μ := by
    apply (hg i).star.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    exact (dirichlet_dirD_conj_at
      ((hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)) _).symm
  have hweightSupp : tsupport (dirichletCutoffWeight η) ⊆
      {z : ℂ | |z.re| < a ∧ z.im < b} := tsupport_mul_subset_left.trans hηsupp
  have hφg (i : Fin 2) : MemLp (dirD φ (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp hU (dirichletCutoffWeight η) hvs hm.star (hvg i)
  have heq : (∫ z, ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z ∂μ) =
      ∫ z, G z * φ z ∂μ :=
    dirichlet_weak_equation_localized_zero_boundary_test hb
      (dirichletCutoffWeight η) hweightSupp hvc hvs hvz hm.star hvg
      (fun i => (hF i).add (hC i)) hG hweak
  have hFluxInt : Integrable
      (fun z => ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) μ :=
    integrable_finset_sum _ (fun i _ =>
      ((hF i).add (hC i)).integrable_mul (hφg i))
  have hLoadInt : Integrable (fun z => G z * φ z) μ := hG.integrable_mul (dirichlet_localized_memLp (dirichletCutoffWeight η) hm.star)
  have hRi : Integrable R μ := hFluxInt.sub hLoadInt
  have hRzero : (∫ z, (R z).re ∂μ) = 0 := by
    change (∫ z, RCLike.re (R z) ∂μ) = 0
    rw [integral_re hRi]
    have hR : (∫ z, R z ∂μ) = 0 := by
      rw [integral_sub hFluxInt hLoadInt, heq, sub_self]
    simp_all
  have hηDx := dirichlet_localized_memLp η
    (show MemLp (dirD v 1) 2 μ by continuity)
  have hJ : Integrable J μ := by
    apply ((hηDx.integrable_norm_pow (by norm_num)).add
      ((dirichlet_localized_memLp η
    (show MemLp (dirD v Complex.I) 2 μ by
      continuity)).integrable_norm_pow (by norm_num))).congr
    filter_upwards with z
    simp 
    ring
  have hGsq := hG.integrable_norm_pow (by norm_num)
  have hCsq : Integrable (fun z => ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) μ :=
    ((hC 0).integrable_norm_pow (by norm_num)).add
    ((hC 1).integrable_norm_pow (by norm_num))
  have hvsq := hm.integrable_norm_pow (by norm_num)
  have hRre : Integrable (fun z => (R z).re) μ := hRi.re
  have hRG : Integrable (fun z => (R z).re + ‖G z‖ ^ 2) μ := hRre.add hGsq
  have hRGC : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2)) μ :=
    hRG.add (hCsq.const_mul (4 * M + 2 * B ^ 2))
  have hright : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2) μ :=
    hRGC.add (hvsq.const_mul (32 * B ^ 2 * M ^ 3 + 2))
  have hmono : (∫ z, J z / (2 * M) ∂μ) ≤
      ∫ z, (R z).re + ‖G z‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2 ∂μ := by
    apply integral_mono_ae (hJ.div_const (2 * M)) hright
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    have hdv := (hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    have hp := dirichlet_localized_energy_absorption hM hB (η z)
      (dirD η 1 z) (dirD η Complex.I z)
      (v z) (dirD v 1 z) (dirD v Complex.I z) (F 0 z) (F 1 z) (C 0 z) (C 1 z) (G z)
      (hη z) (by simp_all [coordDir])
      (by simp_all [coordDir, Matrix.cons_val_one])
      (hcoer z hzU) (hFbound z hzU)
    have hRpoint : R z =
        (F 0 z + C 0 z) * (dirichletCutoffWeight η z * conj (dirD v 1 z) +
          (dirD η 1 z * conj (η z) +
            η z * conj (dirD η 1 z)) * conj (v z)) +
        (F 1 z + C 1 z) * (dirichletCutoffWeight η z * conj (dirD v Complex.I z) +
          (dirD η Complex.I z * conj (η z) +
            η z * conj (dirD η Complex.I z)) * conj (v z)) -
        G z * dirichletCutoffWeight η z * conj (v z) := by
      dsimp only [R]
      rw [Fin.sum_univ_two]
      simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [dirichlet_cutoff_conj_product_dirD η hdv 1,
        dirichlet_cutoff_conj_product_dirD η hdv Complex.I]
      ring
    rwa [hRpoint]
  rw [integral_add hRGC (hvsq.const_mul _),
    integral_add hRG (hCsq.const_mul _), integral_add hRre hGsq,
    hRzero, zero_add, integral_const_mul, integral_const_mul] at hmono
  simpa only [div_eq_mul_inv, integral_mul_const] using hmono

theorem dirichlet_graph_flux_conj_pair (d : ℝ) (x y : ℂ) :
    ((x - d * y) * conj x +
      (-d * x + (1 + d ^ 2) * y) * conj y).re =
      ‖x - d * y‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]
  simp 
  ring

theorem dirichletShiftedFlux_coercive {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / (2 * (1 + K ^ 2)) ≤
      (dirichletShiftedFlux f h v 0 z * conj (dirD v 1 z) +
        dirichletShiftedFlux f h v 1 z * conj (dirD v Complex.I z)).re := by
  simp only [dirichletShiftedFlux, Matrix.cons_val_zero, Matrix.cons_val_one, dirichletGraphSlope]
  rw [dirichlet_graph_flux_conj_pair]
  exact (smoothDirichletGraph_complex_energy_bounds hLip (z + h).re _ _).1

theorem dirichletShiftedFlux_norm_sum_bound {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    ‖dirichletShiftedFlux f h v 0 z‖ + ‖dirichletShiftedFlux f h v 1 z‖ ≤
      2 * (2 * (1 + K ^ 2)) * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖) := by
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let d := dirichletGraphSlope f (z + h)
  let x := dirD v 1 z
  let y := dirD v Complex.I z
  have hd : ‖d‖ ≤ K := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip 
  have h₁ : 1 ≤ M := by nlinarith 
  have hK : K ≤ M := by nlinarith 
  have ha : ‖1 + d ^ 2‖ ≤ 1 + K ^ 2 := by
    calc
      _ ≤ ‖1‖ + ‖d ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖d‖ ^ 2 := by norm_num
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hd 2)
  have hdM  := hd.trans hK
  have hx : ‖x - d * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ ‖x‖ + ‖d * y‖ := norm_sub_le _ _
      _ ≤ M * ‖x‖ + M * ‖y‖ := by
        rw [norm_mul]
        exact add_le_add (by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (norm_nonneg x)])
          (mul_le_mul_of_nonneg_right hdM (norm_nonneg y))
      _ = _ := by ring
  have hy : ‖-d * x + (1 + d ^ 2) * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ ‖-d * x‖ + ‖(1 + d ^ 2) * y‖ := norm_add_le _ _
      _ ≤ M * ‖x‖ + M * ‖y‖ := by
        simp 
        exact add_le_add (mul_le_mul_of_nonneg_right hdM (norm_nonneg x))
          (mul_le_mul_of_nonneg_right (ha.trans (by nlinarith)) (norm_nonneg y))
      _ = _ := by ring
  change ‖x - d * y‖ + ‖-d * x + (1 + d ^ 2) * y‖ ≤ 2 * M * (‖x‖ + ‖y‖)
  linarith

theorem dirichletShiftedFlux_memLp {U : Set ℂ} {f : ℝ → ℝ} {K : NNReal}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hLip : LipschitzWith K f) (h : ℝ) {v : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict U)) (i : Fin 2) :
    MemLp (dirichletShiftedFlux f h v i) 2 (volume.restrict U) := by
  let d  := fun z => dirichletGraphSlope f (z + h)
  have hd : Continuous d := (dirichletGraphSlope_contDiff hf).continuous.comp
    (continuous_id.add continuous_const)
  have hdb (z : ℂ) : ‖d z‖ ≤ K := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip 
  have hdx : MemLp (dirD v 1) 2 (volume.restrict U) := by
    continuity
  have hdy : MemLp (dirD v Complex.I) 2 (volume.restrict U) := by
    continuity
  have hab (z : ℂ) : ‖1 + d z ^ 2‖ ≤ 1 + K ^ 2 := by
    calc
      _ ≤ ‖1‖ + ‖d z ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖d z‖ ^ 2 := by norm_num
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hdb z) 2)
  fin_cases i
  · exact hdx.sub (dirichlet_bounded_mul_memLp hd.aestronglyMeasurable hdb hdy)
  · exact (dirichlet_bounded_mul_memLp hd.neg.aestronglyMeasurable
    (fun z => by rw [Pi.neg_apply, norm_neg]; exact hdb z) hdx).add (dirichlet_bounded_mul_memLp
    (continuous_const.add (hd.pow 2)).aestronglyMeasurable hab hdy)

/-- A compact smooth test has a genuine bound for both actual coordinate
derivatives. Keeping the test abstract avoids unfolding a concrete bump
inside the compact-support derivative estimates. -/
theorem exists_dirichlet_smoothTraceTest_gradient_bound (η : smoothTraceTests) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ, ∀ i : Fin 2, ‖dirD η (coordDir i) z‖ ≤ B := by
  have h₀ := η.property.dirD 1
  have h₁ := η.property.dirD Complex.I
  obtain ⟨B₀, hB₀⟩ := h₀.2.1.exists_bound_of_continuous h₀.1.continuous
  obtain ⟨B₁, hB₁⟩ := h₁.2.1.exists_bound_of_continuous h₁.1.continuous
  let B := max 0 (max B₀ B₁)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro z i
  fin_cases i
  all_goals continuity

/-- The actual complex-valued smooth test associated with a real bump. -/
def dirichletComplexBumpTest (κ : ContDiffBump (0 : ℂ)) : smoothTraceTests :=
  ⟨fun z => (κ z : ℂ),
    ⟨Complex.ofRealCLM.contDiff.comp κ.contDiff,
      κ.hasCompactSupport.comp_left
        (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero,
      subset_univ _⟩⟩

theorem dirichletComplexBumpTest_apply (κ : ContDiffBump 0) (z : ℂ) :
    dirichletComplexBumpTest κ z = κ z := rfl

theorem dirichletComplexBumpTest_tsupport_subset (κ : ContDiffBump 0) :
    tsupport (dirichletComplexBumpTest κ) ⊆
      closedBall 0 κ.rOut := by
  rw [← κ.tsupport_eq]
  exact tsupport_comp_subset  Complex.ofReal_zero κ

theorem dirichletComplexBumpTest_norm_le_one (κ : ContDiffBump 0) (z : ℂ) :
    ‖dirichletComplexBumpTest κ z‖ ≤ 1 := by
  rw [dirichletComplexBumpTest_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (κ.nonneg' z)]
  exact κ.le_one

theorem dirichletComplexBumpTest_eq_one (κ : ContDiffBump 0) {z : ℂ}
    (hz : z ∈ closedBall 0 κ.rIn) : dirichletComplexBumpTest κ z = 1 := by
  rw [dirichletComplexBumpTest_apply, κ.one_of_mem_closedBall hz, Complex.ofReal_one]

/-- A genuine cutoff equal to one on a smaller boundary half box,
with support avoiding the sides and top, is supplied by an actual
smooth bump. Its derivative bound follows from compact support. -/
theorem exists_dirichlet_boundary_energy_cutoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < a ∧ r < b ∧ ∃ (η : smoothTraceTests) (B : ℝ),
      0 ≤ B ∧ tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} ∧
      (∀ z : ℂ, ‖η z‖ ≤ 1) ∧
      (∀ z : ℂ, ∀ i : Fin 2, ‖dirD η (coordDir i) z‖ ≤ B) ∧
      ∀ z ∈ smoothDirichletHalfBox (r / 2) (r / 2), η z = 1 := by
  let r := min a b / 8
  have hr : 0 < r := div_pos (lt_min ha hb) (by norm_num)
  let κ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr, by linarith⟩
  let η := dirichletComplexBumpTest κ
  have hηsupp : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} := by
    intro z hz
    have hzκ  :=
      dirichletComplexBumpTest_tsupport_subset κ hz
    have hzn : ‖z‖ ≤ 2 * r := by continuity
    exact ⟨((Complex.abs_re_le_norm z).trans hzn).trans_lt (by
    grind),
      ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzn)).trans_lt (by
    grind)⟩
  have hη (z : ℂ) : ‖η z‖ ≤ 1 := dirichletComplexBumpTest_norm_le_one κ z
  have hηone (z : ℂ) (hz : z ∈ smoothDirichletHalfBox (r / 2) (r / 2)) : η z = 1 := by
    have hzn : ‖z‖ ≤ r := by
      calc
        _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ r := by rw [abs_of_pos hz.2.1]; linarith [hz.1, hz.2.2]
    exact dirichletComplexBumpTest_eq_one κ
      (by continuity)
  obtain ⟨B, hB, hg⟩ := exists_dirichlet_smoothTraceTest_gradient_bound η
  grind

theorem dirichlet_dirD_comm {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hu := hs.contDiffAt (hU.mem_nhds hz)
  have hD (v w : ℂ) : dirD (dirD u v) w z = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    simp [fderiv_clm_apply ((hu.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiableAt (by simp)) (differentiableAt_const v)]
  rw [hD, hD]
  exact (hu.isSymmSndFDerivAt (by
    norm_num)).eq w v

end PolyaNeumann

end
