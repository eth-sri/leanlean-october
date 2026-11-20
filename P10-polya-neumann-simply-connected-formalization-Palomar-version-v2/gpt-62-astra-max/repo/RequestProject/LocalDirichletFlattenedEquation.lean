module

public import RequestProject.LocalDirichletBoundaryRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import RequestProject.PlanarNotation

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

section

variable (f : ℝ → ℝ) (u : ℂ → ℂ) (i : Fin 2) (z : ℂ)

/-- Real bilinearity alone gives invariance of the trace under a
unit rotation. Symmetry of the bilinear map is not needed. -/
theorem dirichlet_bilinear_rotated_trace (T : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)
    {e : ℂ} (he : ‖e‖ = 1) :
    T e e + T (Complex.I * e) (Complex.I * e) = T 1 1 + T Complex.I Complex.I := by
  let a := e.re
  let b := e.im
  have hE : e = a • (1 : ℂ) + b • Complex.I := by
    apply Complex.ext <;> simp [a, b]
  have hIE : Complex.I * e = (-b) • (1 : ℂ) + a • Complex.I := by
    apply Complex.ext <;> simp [a, b, Complex.mul_re, Complex.mul_im]
  
  have hsC : a ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast (by
    have h := congrArg (fun r : ℝ => r ^ 2) he

    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    simpa [a, b, pow_two] using h)
  have hT  := congrArg (fun w => T w w) hE
  have hTI  :=
    congrArg (fun w => T w w) hIE
  rw [hT, hTI]
  simp only [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  grind

theorem dirichlet_rotated_lap {v : ℂ → ℂ} {z e : ℂ}
    (hv : ContDiffAt ℝ 2 v z) (he : ‖e‖ = 1) :
    dirD (dirD v e) e z + dirD (dirD v (Complex.I * e)) (Complex.I * e) z = lap v z := by
  have hd  :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD (w : ℂ) : dirD (dirD v w) w z = fderiv ℝ (fderiv ℝ v) z w w := by
    change fderiv ℝ (fun u => fderiv ℝ v u w) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [hD, hD, lap, hD, hD]
  exact dirichlet_bilinear_rotated_trace _ he

include f z in
/-- The actual real graph slope, regarded as a complex scalar. -/
def dirichletGraphSlope : ℂ := ((deriv f z.re : ℝ) : ℂ)

theorem dirichletGraphSlope_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirichletGraphSlope f) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_infty_iff_deriv.mp hf).2.comp Complex.reCLM.contDiff)

@[simp] theorem dirD_dirichletGraphSlope_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    dirD (dirichletGraphSlope f) Complex.I z = 0 := by
  
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z Complex.I = 0
  rw [hs.fderiv]
  simp

include f i u z in
/-- The flux of the actual graph coefficient matrix. -/
def dirichletFlattenedFlux : ℂ :=
  ![dirD u 1 z - dirichletGraphSlope f z * dirD u Complex.I z,
    -dirichletGraphSlope f z * dirD u 1 z +
      (1 + dirichletGraphSlope f z ^ 2) * dirD u Complex.I z] i

include f u z in
def dirichletFlattenedDivergence : ℂ :=
  dirD (dirichletFlattenedFlux f u 0) 1 z +
    dirD (dirichletFlattenedFlux f u 1) Complex.I z

end

theorem dirichletFlattenedFlux_pullback (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 0 z = dirD v (1 / c) (Ψ z)) ∧
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 1 z =
       dirD v (Complex.I / c) (Ψ z) - dirichletGraphSlope f z * dirD v (1 / c) (Ψ z)) := by
  have h := smoothDirichletGraphChart_pullback_gradient p c hc hf hv
  constructor
  · exact h.1
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
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {v : ℂ → ℂ}
    (hv : ContDiffOn ℝ ∞ v Ω) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    dirichletFlattenedDivergence f
      (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) z =
      lap v (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := v ∘ Ψ
  let g₀ := dirD v (1 / c)
  let g₁ := dirD v (Complex.I / c)
  have hvc := hv.contDiffAt (hΩ.mem_nhds hz)
  have hv₂ : ContDiffAt ℝ 2 v (Ψ z) := hvc.of_le ((by simp))
  have hdg (w : ℂ) : DifferentiableAt ℝ (dirD v w) (Ψ z) :=
    ((hvc.fderiv_right (m := ∞) le_rfl).clm_apply contDiffAt_const).differentiableAt
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
    
    have he := sub_eq_iff_eq_add.mp ((smoothDirichletGraphChart_pullback_gradient p c hc hf hg).1)
    rw [hcompI g hg] at he
    exact he
  have hD₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD g₀ (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    change fderiv ℝ (dirichletFlattenedFlux f u 0) z 1 = _
    rw [h₀.fderiv_eq ]
    exact hcompOne g₀ (hdg _)
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
    rw [hcompI g₁ (hdg _), hcompI g₀ (hdg _), dirD_dirichletGraphSlope_I hf]
    ring
  have he : ‖c⁻¹‖ = 1 := by simp [*]
  calc
    _ = dirD g₀ (1 / c) (Ψ z) + dirD g₁ (Complex.I / c) (Ψ z) := by
      rw [dirichletFlattenedDivergence, hD₀, hD₁]
      ring
    _ = _ := by
      simpa only [g₀, g₁, one_div, div_eq_mul_inv, one_mul] using dirichlet_rotated_lap hv₂ he

/-- Total directional derivatives of a function smooth on an open
set are again smooth on that same open set. -/
theorem dirichlet_contDiffOn_dirD {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (w : ℂ) :
    ContDiffOn ℝ ∞ (dirD g w) U := by
  intro z hz
  exact (((hg.contDiffAt (hU.mem_nhds hz)).fderiv_right
     le_rfl).clm_apply contDiffAt_const).contDiffWithinAt

/-- Local smoothness plus a genuine compact test suffices for this
integrability statement. No global second-derivative energy is used. -/
theorem dirichlet_local_smooth_mul_test_integrable {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) (hφ : TestFunction U φ) :
    IntegrableOn (fun z => g z * φ z) U := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have heq : (fun z => g z * φ z) = (fun z => G z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  rw [heq]
  exact (hG.memLp' 2).integrable_mul (hφ.memLp' 2)

theorem dirichlet_local_smooth_field_test_eq_neg_dirD {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) (hφ : TestFunction U φ)
    (i : Fin 2) :
    (∫ z in U, g z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD g (coordDir i) z * φ z) := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have hu := hG.memLp' 2 (μ := volume.restrict U)
  have hgrad (j : Fin 2) := (hG.dirD (coordDir j)).memLp' 2 (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth hG.1 hu hgrad φ hφ i
  have hl : (fun z => (hu.toLp G) z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => g z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp only [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz,
        ContinuousLinearMap.zero_apply, mul_zero]
  have hr : (fun z => ((hgrad i).toLp _) z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD g (coordDir i) z * φ z) := by
    filter_upwards [(hgrad i).coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD g (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i))
          ((hGg z hz).fderiv_eq )]
    · simp [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  change (∫ z in U, (hu.toLp G : L2 U) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hgrad i).toLp _ : L2 U) z * φ z) at hw
  rw [integral_congr_ae hl, integral_congr_ae hr] at hw
  exact hw

theorem dirichletFlattenedFlux_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (dirichletFlattenedFlux f u i) U := by
  have hx := dirichlet_contDiffOn_dirD hU hu 1
  have hy := dirichlet_contDiffOn_dirD hU hu Complex.I
  have hd := (dirichletGraphSlope_contDiff hf).contDiffOn (s := U)
  fin_cases i
  · exact hx.sub (hd.mul hy)
  · exact (hd.neg.mul hx).add ((contDiffOn_const.add (hd.pow 2)).mul hy)

theorem riemannMappingDirichletRemainder_contDiffOn {Ω : Set ℂ}
    {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    (d : smoothTraceTests) :
    ContDiffOn ℝ ∞ (riemannMappingDirichletRemainder F d) Ω :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hΦ)).sub
      d.property.1.contDiffOn

/-- Every actual smooth datum gives this physical Laplacian identity;
the selected datum is needed only for the separately proved zero
boundary values. -/
theorem riemannMappingDirichletRemainder_lap {Ω : Set ℂ}
    {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    (d : smoothTraceTests) {z : ℂ} (hz : z ∈ Ω) :
    lap (riemannMappingDirichletRemainder F d) z = -lap (d : ℂ → ℂ) z := by
  have hharm := (riemannMappingGreenCorrection_harmonicOnNhd hΦ).comp_CLM
    Complex.ofRealCLM
  have hh := (hharm z hz).1
  
  exact (lap_sub_of_contDiffAt hh (d.property.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))).trans (by
    rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds, Pi.zero_apply, zero_sub])

/-! ### Actual zero-boundary test approximation -/

theorem dirichlet_bounded_mul_memLp {μ : Measure ℂ} {a g : ℂ → ℂ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hbound : ∀ z, ‖a z‖ ≤ C)
    (hg : MemLp g 2 μ) : MemLp (fun z => a z * g z) 2 μ := by
  apply hg.of_le_mul (c := C) (ha.mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖a z * g z‖ ≤ C * ‖g z‖
    rw [norm_mul]
    bound

theorem dirichlet_localized_memLp {μ : Measure ℂ} (η : smoothTraceTests) {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) : MemLp (fun z => η z * g z) 2 μ := by
  obtain ⟨C, hC⟩ := η.property.2.1.exists_bound_of_continuous η.property.1.continuous
  exact dirichlet_bounded_mul_memLp η.property.1.continuous.aestronglyMeasurable hC hg

theorem dirichlet_localized_dirD {U : Set ℂ} (hU : IsOpen U) (η : smoothTraceTests)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) {z : ℂ} (hz : z ∈ U) (w : ℂ) :
    dirD (fun u => η u * g u) w z = η z * dirD g w z + dirD (η : ℂ → ℂ) w z * g z := by
  
  
  change fderiv ℝ ((η : ℂ → ℂ) * g) z w = _
  rw [fderiv_mul ((η.property.1.differentiable (by simp)) z) ((hg.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz))]
  simp [dirD] <;> ring

theorem dirichlet_localized_gradient_memLp {U : Set ℂ} (hU : IsOpen U)
    (η : smoothTraceTests) {g : ℂ → ℂ} (hs : ContDiffOn ℝ ∞ g U)
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
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    (let v := fun z => η z * g z
     (∀ ε : ℝ, 0 < ε → TestFunction (smoothDirichletHalfBox a b)
       (fun z => dirichletNormalCutoff ε z * v z)) ∧
     Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
       ‖dirichletNormalCutoff ε z * v z - v z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
     ∀ i : Fin 2, Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
       ‖dirD (fun u => dirichletNormalCutoff ε u * v u) (coordDir i) z -
         dirD v (coordDir i) z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  let v  := fun z => η z * g z
  
  have hvS  :=
    η.property.1.contDiffOn.mul hs
  have hvz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0 := by
    grind
  have hvm := dirichlet_localized_memLp η hm
  have hvg (i : Fin 2) := dirichlet_localized_gradient_memLp
    (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have htest := dirichletNormalCutoff_testFunction hε η hη hs
    grind
  · have h := dirichletNormalCutoff_weight_error_energy_tendsto_zero hb hvm
    apply h.congr'
    exact Eventually.of_forall fun ε => by
      ring
  · intro i
    fin_cases i
    · apply dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero hb hvS
      exact hvg 0
    · apply dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero hb (η.property.1.continuous.continuousOn.mul hc) hvS hvz hvm
      exact hvg 1

/-- Actual L² energy convergence gives convergence of pairing
against any fixed actual L² function. This is the Cauchy–Schwarz
step needed to pass genuine interior tests to the boundary. -/
theorem dirichlet_pairing_tendsto_zero_of_energy {μ : Measure ℂ}
    {g : ℂ → ℂ} (hg : MemLp g 2 μ) {e : ℝ → ℂ → ℂ}
    (he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (e ε) 2 μ)
    (hE : Tendsto (fun ε : ℝ => ∫ z, ‖e ε z‖ ^ 2 ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ z, g z * e ε z ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hE
  have hup : Tendsto (fun ε : ℝ => (eLpNorm g 2 μ).toReal *
      Real.sqrt (∫ z, ‖e ε z‖ ^ 2 ∂μ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using tendsto_const_nhds.mul hsqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · simp
  · filter_upwards [he] with ε hε
    simpa only [toReal_eLpNorm, lpNorm_two_eq hε] using
      norm_integral_mul_le_eLpNorm hg hε

theorem dirichlet_pairing_tendsto_of_energy_approximation {μ : Measure ℂ}
    {g k : ℂ → ℂ} (hg : MemLp g 2 μ) (hk : MemLp k 2 μ) {kε : ℝ → ℂ → ℂ}
    (hmem : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (kε ε) 2 μ)
    (hE : Tendsto (fun ε : ℝ => ∫ z, ‖kε ε z - k z‖ ^ 2 ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ z, g z * kε ε z ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, g z * k z ∂μ)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (fun z => kε ε z - k z) 2 μ :=
    hmem.mono fun _ h => h.sub hk
  have hp := dirichlet_pairing_tendsto_zero_of_energy hg he hE
  have hplus := hp.add (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ∫ z, g z * k z ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, g z * k z ∂μ)))
  have hplus' : Tendsto (fun ε : ℝ =>
      (∫ z, g z * (kε ε z - k z) ∂μ) + ∫ z, g z * k z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, g z * k z ∂μ)) := by
    simpa only [zero_add] using hplus
  apply hplus'.congr'
  filter_upwards [hmem] with ε hε
  simp_rw [mul_sub]
  have hiε : Integrable (fun z => g z * kε ε z) μ := hg.integrable_mul hε
  have hik : Integrable (fun z => g z * k z) μ := hg.integrable_mul hk
  rw [integral_sub hiε hik]
  ring

/-- The passage from actual compact interior tests to a localized
zero-boundary H¹ test. Its convergence and integrability are proved
above, and no density or boundary smoothness assumption is made. -/
theorem dirichlet_weak_equation_localized_zero_boundary_test {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
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
  
  have hvg (i : Fin 2)  :=
    dirichlet_localized_gradient_memLp (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  
  have hεg (i : Fin 2) : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      MemLp (dirD (vε ε) (coordDir i)) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((htest ε hε).dirD (coordDir i)).memLp' 2
  have hleft (i : Fin 2)  :=
    dirichlet_pairing_tendsto_of_energy_approximation (hF i) (hvg i) (hεg i) (hgradient i)
  have hright  :=
    dirichlet_pairing_tendsto_of_energy_approximation hG (dirichlet_localized_memLp η hm) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (htest ε hε).memLp' 2) hvalue
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hleft i)
  have heq : (fun ε : ℝ => ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      =ᶠ[𝓝[>] 0] (fun ε : ℝ => ∫ z, G z * vε ε z ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hisum : (∫ z, ∑ i : Fin 2, F i z * dirD (vε ε) (coordDir i) z ∂μ) =
        ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ := by
      apply integral_finset_sum
      intro i _
      exact (hF i).integrable_mul (((htest ε hε).dirD (coordDir i)).memLp' 2)
    rw [← hisum]
    exact hweak _ (htest ε hε)
  
  
  have hisum : (∫ z, ∑ i : Fin 2, F i z * dirD v (coordDir i) z ∂μ) =
      ∑ i : Fin 2, ∫ z, F i z * dirD v (coordDir i) z ∂μ := by
    apply integral_finset_sum
    intro i _
    exact (hF i).integrable_mul (hvg i)
  rw [hisum]
  exact tendsto_nhds_unique hsum (hright.congr' heq.symm)

theorem dirichlet_halfBox_isBounded {a b : ℝ} :
    Bornology.IsBounded (smoothDirichletHalfBox a b) := by
  apply (isBounded_closedBall  (r := a + b)).subset
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  calc
    _ ≤ _ := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add hz.1.le (by rw [abs_of_pos hz.2.1]; exact hz.2.2.le)

/-- The actual tangential difference quotient, with ordinary real
translation and the physical complex scalar normalization. -/
def dirichletTangentialDifference (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (u (z + (h : ℂ)) - u z) / (h : ℂ)

/-- Every intermediate horizontal translation lies inside the wider rectangle. -/
lemma halfBox_add_mem {a b A t : ℝ} (h : a + |t| ≤ A) {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) :
    z + (t : ℂ) ∈ smoothDirichletHalfBox A b := by
  simpa [smoothDirichletHalfBox] using
    And.intro ((abs_add_le z.re t).trans_lt ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le h)) hz.2

private lemma halfBox_map_add_le {a b A t : ℝ} (h : a + |t| ≤ A) :
    (volume.restrict (smoothDirichletHalfBox a b)).map (· + (t : ℂ)) ≤ volume.restrict (smoothDirichletHalfBox A b) := by
  rw [((measurePreserving_add_right volume (t : ℂ)).restrict_image_emb (MeasurableEquiv.addRight (t : ℂ)).measurableEmbedding _).map_eq]
  exact Measure.restrict_mono_set _ (image_subset_iff.mpr fun _ hz => halfBox_add_mem h hz)

theorem dirichletTangentialDifference_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ} (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifference h u) 2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hs := (hm.mono_measure (halfBox_map_add_le hmargin)).comp_of_map (by fun_prop)
  have hr := hm.mono_measure (Measure.restrict_mono_set volume (halfBox_mono (a := a) (by linarith [abs_nonneg h]) le_rfl))
  unfold dirichletTangentialDifference; simp_rw [div_eq_mul_inv]
  exact (hs.sub hr).mul_const ((h : ℂ)⁻¹)

/-- The difference quotient is the average of the tangential derivative along
 an interior segment. Cauchy–Schwarz and Fubini bound its energy by the energy
 on the wider rectangle: each translation preserves area and lands inside it. -/
theorem dirichlet_halfBox_tangential_difference_energy_le {A a b h : ℝ} (hh : 0 < h) (hmargin : a + h ≤ A)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hDx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    halfBoxEnergy a b (dirichletTangentialDifference h u) ≤ halfBoxEnergy A b (dirD u 1) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let ρ := volume.restrict (Ioc 0 h)
  let G := fun (t : ℝ) (z : ℂ) => ‖dirD u 1 (z + (t : ℂ))‖ ^ 2
  have hG : Measurable (Function.uncurry G) :=
    ((measurable_fderiv_apply_const ℝ u (1 : ℂ)).comp (measurable_snd.add (Complex.measurable_ofReal.comp measurable_fst))).norm.pow_const 2
  have hpos t z : 0 ≤ G t z := sq_nonneg _
  have hreach {t : ℝ} (ht : t ∈ Icc 0 h) : a + |t| ≤ A := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  have hslice t (ht : t ∈ Ioc 0 h) := halfBox_map_add_le (b := b) (hreach (Ioc_subset_Icc_self ht))
  have hI t (ht : t ∈ Ioc 0 h) : Integrable (G t) μ :=
    ((hDx.mono_measure (hslice t ht)).comp_of_map (by fun_prop)).norm.integrable_sq
  have hle t (ht : t ∈ Ioc 0 h) : (∫ z, G t z ∂μ) ≤ halfBoxEnergy A b (dirD u 1) := by
    exact ((MeasurableEquiv.addRight (t : ℂ)).measurableEmbedding.integral_map _).symm.trans_le
      (integral_mono_measure (hslice t ht) (.of_forall fun _ => sq_nonneg _) hDx.norm.integrable_sq)
  have hprod : Integrable (Function.uncurry G) (ρ.prod μ) := by
    refine (integrable_prod_iff hG.aestronglyMeasurable).2 ⟨(ae_restrict_mem measurableSet_Ioc).mono hI, ?_⟩
    simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (hpos _ _)]
    refine (integrable_const (halfBoxEnergy A b (dirD u 1))).mono' hG.aestronglyMeasurable.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_of_nonneg (integral_nonneg (hpos t))] using hle t ht
  have hq := dirichletTangentialDifference_memLp (by rwa [abs_of_pos hh] : a + |h| ≤ A) hm
  calc _ ≤ ∫ z, (∫ t, G t z ∂ρ) / h ∂μ := by
          apply integral_mono_ae hq.norm.integrable_sq (hprod.integral_prod_right.div_const h)
          filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz
          let L := fun t : ℝ => z + (t : ℂ)
          have hL : MapsTo L (Icc 0 h) (smoothDirichletHalfBox A b) := fun _ ht => halfBox_add_mem (hreach ht) hz
          have hdL : ContinuousOn (dirD u 1 ∘ L) (Icc 0 h) :=
            (dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs 1).continuousOn.comp (by fun_prop : Continuous L).continuousOn hL
          have hd t (ht : t ∈ uIcc 0 h) : HasDerivAt (u ∘ L) ((dirD u 1 ∘ L) t) t := by
            have := (hs.contDiffAt ((isOpen_smoothDirichletHalfBox A b).mem_nhds (hL (uIcc_of_le hh.le ▸ ht)))).differentiableAt (by simp)
            exact this.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).ofReal_comp.const_add z)
          have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hdL.intervalIntegrable_of_Icc hh.le)
          have hlp : MemLp (dirD u 1 ∘ L) 2 ρ := (memLp_two_iff_integrable_sq_norm
            ((hdL.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).2
              ((hdL.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          have hsq := norm_sq_intervalIntegral_le hh.le hlp
          rw [hft, intervalIntegral.integral_of_le hh.le] at hsq
          simp only [Function.comp_apply, L, Complex.ofReal_zero, add_zero, sub_zero] at hsq
          simp only [dirichletTangentialDifference, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_pow]
          field_simp
          exact hsq
       _ = (∫ t, ∫ z, G t z ∂μ ∂ρ) / h := by rw [integral_div, ← integral_integral_swap hprod]
       _ ≤ (∫ _ : ℝ, halfBoxEnergy A b (dirD u 1) ∂ρ) / h := by
         exact div_le_div_of_nonneg_right (integral_mono_ae hprod.integral_prod_left (integrable_const _)
           ((ae_restrict_mem measurableSet_Ioc).mono hle)) hh.le
       _ = _ := by simp [ρ, Measure.real, hh.le]; field_simp

/-- Every fixed tangential difference quotient is a genuine H¹
function on the smaller half box. Its derivative is the difference
quotient of the actual first derivative; this is proved from the
ordinary chain rule, not from an assumed H² bound. -/
theorem dirichletTangentialDifference_dirD {h : ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ u z) (hzh : DifferentiableAt ℝ u (z + (h : ℂ))) (w : ℂ) :
    dirD (dirichletTangentialDifference h u) w z =
      dirichletTangentialDifference h (dirD u w) z := by
  have hT : HasFDerivAt (fun z : ℂ => z + (h : ℂ))
      (ContinuousLinearMap.id ℝ ℂ) z := (hasFDerivAt_id z).add_const (h : ℂ)
  have hq : HasFDerivAt (dirichletTangentialDifference h u)
      ((h : ℂ)⁻¹ • (fderiv ℝ u (z + (h : ℂ)) - fderiv ℝ u z)) z := by
    exact ((hzh.hasFDerivAt.comp z hT).sub hz.hasFDerivAt).mul_const ((h : ℂ)⁻¹)
  simp [hq.fderiv, smul_eq_mul, dirichletTangentialDifference, dirD, div_eq_mul_inv] <;> ring

theorem dirichletTangentialDifference_continuousOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifference h u) (smoothDirichletClosedHalfBox a b) := by
  
  have hsub : smoothDirichletClosedHalfBox a b ⊆ smoothDirichletClosedHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans ((by grind)), hz.2⟩
  refine ((hc.comp (continuous_id.add continuous_const).continuousOn ?_).sub
    (hc.mono hsub)).div_const (h : ℂ)
  intro z hz
  have hx  :=
    (abs_add_le z.re h).trans
      ((show |z.re| + |h| ≤ a + |h| from
        add_le_add hz.1 le_rfl).trans hmargin)
  simpa [smoothDirichletClosedHalfBox] using
    (show |z.re + h| ≤ A ∧ 0 ≤ z.im ∧ z.im ≤ b from ⟨hx, hz.2⟩)

theorem dirichletTangentialDifference_contDiffOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ ∞ (dirichletTangentialDifference h u)
      (smoothDirichletHalfBox a b) := by
  
  have hsub : smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans_le ((by grind)), hz.2⟩
  refine ((hs.comp (contDiff_id.add contDiff_const).contDiffOn ?_).sub
    (hs.mono hsub)).div_const (h : ℂ)
  intro z hz
  have hx  :=
    (abs_add_le z.re h).trans_lt
      ((show |z.re| + |h| < a + |h| from
        add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
  simpa [smoothDirichletHalfBox] using
    (show |z.re + h| < A ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)

theorem dirichletTangentialDifference_zero_bottom {A a h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0) {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifference h u (x : ℂ) = 0 := by
  have hxA  :=
    hx.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin)
  have hxh  :=
    (abs_add_le x h).trans_lt
      ((show |x| + |h| < a + |h| from
        add_lt_add_of_lt_of_le hx le_rfl).trans_le hmargin)
  simp [dirichletTangentialDifference, ← Complex.ofReal_add, hz x hxA, hz (x + h) hxh, sub_self, zero_div]

/-- The actual coefficient matrix at the shifted horizontal point,
acting on the gradient at the original point. -/
def dirichletShiftedFlux (f : ℝ → ℝ) (h : ℝ) (v : ℂ → ℂ)
    (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD v 1 z - dirichletGraphSlope f (z + (h : ℂ)) * dirD v Complex.I z,
    -dirichletGraphSlope f (z + (h : ℂ)) * dirD v 1 z +
      (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) * dirD v Complex.I z] i

section

variable (η : smoothTraceTests) (κ : ContDiffBump (0 : ℂ)) (w z : ℂ)

private theorem dirichlet_energy_young {M : ℝ} (hM : 0 < M) (Y S : ℝ) :
    Y * S ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := by
  
  
  calc
    _ = (4 * M * Y * S) / (4 * M) := by field_simp [hM.ne']
    _ ≤ (Y ^ 2 + 4 * M ^ 2 * S ^ 2) / (4 * M) :=
      div_le_div_of_nonneg_right (by
        nlinarith only [sq_nonneg (Y - 2 * M * S)]) (mul_pos (by norm_num) hM).le
    _ = _ := by field_simp [hM.ne']

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
  have hX₀ : 0 ≤ X := (by positivity)
  have hc₀ : 0 ≤ c := (by positivity)
  have hρnorm : ‖ρ‖ = ‖η‖ ^ 2 := by simp [ρ, norm_mul, norm_conj, pow_two]
  have hρ : ρ = ((‖η‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [← Complex.ofReal_pow] using Complex.mul_conj' η
  have hb₀ : ‖b₀‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ ‖α * conj η‖ + ‖η * conj α‖ := norm_add_le _ _
      _ = 2 * ‖α‖ * ‖η‖ := by simp only [norm_mul, norm_conj]; ring
      _ ≤ _ := by gcongr
  have hb₁ : ‖b₁‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ ‖β * conj η‖ + ‖η * conj β‖ := norm_add_le _ _
      _ = 2 * ‖β‖ * ‖η‖ := by simp only [norm_mul, norm_conj]; ring
      _ ≤ _ := by gcongr
  have hηsq : ‖η‖ ^ 2 ≤ ‖η‖ := by nlinarith only [hη, norm_nonneg η]
  have hAerr : ‖(F₀ * b₀ + F₁ * b₁) * conj v‖ ≤ 4 * B * M * Y * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (‖F₀ * b₀‖ + ‖F₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖F₀‖ * (2 * B * ‖η‖) + ‖F₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by
        simp only [norm_mul]
        gcongr
      _ = 2 * B * ‖η‖ * (‖F₀‖ + ‖F₁‖) * ‖v‖ := by ring
      _ ≤ 2 * B * ‖η‖ * (2 * M * X) * ‖v‖ := by gcongr
      _ = _ := by dsimp [Y]; ring
  have hCdot : ‖C₀ * conj x + C₁ * conj y‖ ≤ c * X := by
    calc
      _ ≤ _ := norm_add_le _ _
      _ = ‖C₀‖ * ‖x‖ + ‖C₁‖ * ‖y‖ := by simp
      _ ≤ _ := by
        nlinarith only [mul_nonneg (norm_nonneg C₀) (norm_nonneg y),
          mul_nonneg (norm_nonneg C₁) (norm_nonneg x)]
  have hCmain : ‖ρ * (C₀ * conj x + C₁ * conj y)‖ ≤ c * Y := by
    rw [norm_mul, hρnorm]
    calc
      _ ≤ ‖η‖ ^ 2 * (c * X) := mul_le_mul_of_nonneg_left hCdot (sq_nonneg _)
      _ ≤ ‖η‖ * (c * X) := mul_le_mul_of_nonneg_right hηsq (mul_nonneg hc₀ hX₀)
      _ = _ := by dsimp [Y]; ring
  have hCerr : ‖(C₀ * b₀ + C₁ * b₁) * conj v‖ ≤ 2 * B * c * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (‖C₀ * b₀‖ + ‖C₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖C₀‖ * (2 * B * ‖η‖) + ‖C₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by
        simp only [norm_mul]
        gcongr
      _ = 2 * B * c * ‖η‖ * ‖v‖ := by dsimp [c]; ring
      _ ≤ 2 * B * c * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have hGerr : ‖G * ρ * conj v‖ ≤ ‖G‖ * ‖v‖ := by
    rw [norm_mul, norm_mul, hρnorm, norm_conj]
    have hηsq₁ : ‖η‖ ^ 2 ≤ 1 := hηsq.trans hη
    calc
      _ ≤ ‖G‖ * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have herr : ‖err‖ ≤ Y * S + 2 * B * c * ‖v‖ + ‖G‖ * ‖v‖ := by
    calc
      _ ≤ _ := norm_sub_le _ _
      _ ≤ ((‖(F₀ * b₀ + F₁ * b₁) * conj v‖ +
          ‖ρ * (C₀ * conj x + C₁ * conj y)‖) +
          ‖(C₀ * b₀ + C₁ * b₁) * conj v‖) + ‖G * ρ * conj v‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((4 * B * M * Y * ‖v‖ + c * Y) + 2 * B * c * ‖v‖) + ‖G‖ * ‖v‖ := by
        gcongr
      _ = _ := by ring
  have hYsq : Y ^ 2 ≤ 2 * T := by
    dsimp [T]
    have hxy : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]
    convert mul_le_mul_of_nonneg_left hxy (sq_nonneg ‖η‖) using 1 <;> ring
  
  have hfourM : 0 < 4 * M := by positivity
  
  have hYoung' : Y * S ≤ T / (2 * M) + 2 * M * c ^ 2 +
      32 * B ^ 2 * M ^ 3 * ‖v‖ ^ 2 := by
    calc
      _ ≤ _ := (dirichlet_energy_young hM Y S)
      _ ≤ (2 * T) / (4 * M) + M *
          (2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2) :=
        add_le_add (div_le_div_of_nonneg_right hYsq hfourM.le)
          (mul_le_mul_of_nonneg_left (by
            nlinarith only [sq_nonneg (c - 4 * B * M * ‖v‖)]) hM.le)
      _ = _ := by ring
  have hBc : 2 * B * c * ‖v‖ ≤ B ^ 2 * c ^ 2 + ‖v‖ ^ 2 := by
    nlinarith only [sq_nonneg (B * c - ‖v‖)]
  have hGv : ‖G‖ * ‖v‖ ≤ ‖G‖ ^ 2 + ‖v‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖G‖ - ‖v‖), sq_nonneg ‖G‖, sq_nonneg ‖v‖]
  have hcsq : c ^ 2 ≤ 2 * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖C₀‖ - ‖C₁‖)]
  have herr' : ‖err‖ ≤ T / (2 * M) + ‖G‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
    have hcBound := mul_le_mul_of_nonneg_left hcsq
      (show 0 ≤ 2 * M + B ^ 2 by positivity)
    linarith only [herr, hYoung', hBc, hGv, hcBound]
  have hmain : T / M ≤ main.re := by
    rw [show main = ((‖η‖ ^ 2 : ℝ) : ℂ) * (F₀ * conj x + F₁ * conj y) by rw [← hρ]]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ = ‖η‖ ^ 2 * ((‖x‖ ^ 2 + ‖y‖ ^ 2) / M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoer (sq_nonneg _)
  have heq : L - G * ρ * conj v = main + err := by ring
  have hmainBound : main.re ≤ (L - G * ρ * conj v).re + ‖err‖ := by
    rw [heq, Complex.add_re]
    have h := Complex.re_le_norm (-err)
    simp only [Complex.neg_re, norm_neg] at h
    linarith only [h]
  have hTsplit : T / M = T / (2 * M) + T / (2 * M) := by
    ring
  linarith only [hmain, hmainBound, herr', hTsplit]

include η in
/-- A genuine smooth compact weight, even for a complex cutoff. -/
def dirichletCutoffWeight : smoothTraceTests :=
  ⟨fun z => η z * conj (η z),
    ⟨η.property.1.mul (Complex.conjCLE.contDiff.comp η.property.1),
      η.property.2.1.mul_right, subset_univ _⟩⟩

theorem dirichlet_dirD_conj_at {u : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (w : ℂ) :
    dirD (fun z => conj (u z)) w z = conj (dirD u w z) := by
  
  change fderiv ℝ (Complex.conjCLE ∘ u) z w = _
  rw [((Complex.conjCLE.hasFDerivAt.comp z hu.hasFDerivAt).fderiv)]
  rfl

theorem dirichletCutoffWeight_dirD :
    dirD (dirichletCutoffWeight η : ℂ → ℂ) w z =
      dirD (η : ℂ → ℂ) w z * conj (η z) +
        η z * conj (dirD (η : ℂ → ℂ) w z) := by
  have hη := ((η.property.1.differentiable (by simp)) z).hasFDerivAt
  
  have hd := (hη.mul (Complex.conjCLE.hasFDerivAt.comp z hη)).fderiv
  change fderiv ℝ ((η : ℂ → ℂ) * (Complex.conjCLE ∘ (η : ℂ → ℂ))) z w = _
  rw [hd]
  simp [smul_eq_mul, dirD] <;> ring

theorem dirichlet_cutoff_conj_product_dirD
    {v : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v z) (w : ℂ) :
    dirD (fun z => dirichletCutoffWeight η z * conj (v z)) w z =
      dirichletCutoffWeight η z * conj (dirD v w z) +
        (dirD (η : ℂ → ℂ) w z * conj (η z) +
          η z * conj (dirD (η : ℂ → ℂ) w z)) * conj (v z) := by
  
  
  have hd := (((((dirichletCutoffWeight η).property.1.differentiable (by simp)) z)).hasFDerivAt.mul (Complex.conjCLE.hasFDerivAt.comp z hv.hasFDerivAt)).fderiv
  change fderiv ℝ ((dirichletCutoffWeight η : ℂ → ℂ) * (Complex.conjCLE ∘ v)) z w = _
  rw [hd]
  simp
  change dirichletCutoffWeight η z * conj (dirD v w z) +
    conj (v z) * dirD (dirichletCutoffWeight η : ℂ → ℂ) w z = _
  rw [dirichletCutoffWeight_dirD]
  ring

/-- The genuine localized energy estimate for a zero-boundary H¹
solution of a weak elliptic equation with an L² flux commutator.
The boundary test is obtained by the proved normal-cutoff passage.
There is no assumed boundary test density or second-derivative gain. -/
theorem dirichlet_localized_boundary_energy_bound {a b M B : ℝ}
    (hb : 0 < b) (hM : 0 < M) (hB : 0 ≤ B)
    (η : smoothTraceTests)
    (hηsupp : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    (hη : ∀ z : ℂ, ‖η z‖ ≤ 1)
    (hηgrad : ∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B)
    {v : ℂ → ℂ} (hc : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
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
  
  let μ := volume.restrict (smoothDirichletHalfBox a b)
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
    intro x hx
    simp [*]
  have hvg (i : Fin 2) : MemLp (dirD (fun z => conj (v z)) (coordDir i)) 2 μ := by
    apply (hg i).star.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    exact (dirichlet_dirD_conj_at
      ((hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)) _).symm
  have hweightSupp : tsupport (dirichletCutoffWeight η : ℂ → ℂ) ⊆
      {z : ℂ | |z.re| < a ∧ z.im < b} := tsupport_mul_subset_left.trans hηsupp
  
  have hφg (i : Fin 2)  :=
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
    simp [hR]
  
  
  have hJ : Integrable J μ := by
    apply (((dirichlet_localized_memLp η
      (show MemLp (dirD v 1) 2 μ by exact hg 0)).integrable_norm_pow (by positivity)).add
      ((dirichlet_localized_memLp η
        (show MemLp (dirD v Complex.I) 2 μ by
          exact hg 1)).integrable_norm_pow (by positivity))).congr
    filter_upwards with z
    
    simp [norm_mul, mul_pow]
    ring
  have hGsq := hG.integrable_norm_pow (by positivity)
  have hCsq : Integrable (fun z => ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) μ :=
    ((hC 0).integrable_norm_pow (by positivity)).add
    ((hC 1).integrable_norm_pow (by positivity))
  have hvsq := hm.integrable_norm_pow (by positivity)
  have hRre : Integrable (fun z => (R z).re) μ := hRi.re
  have hRG : Integrable (fun z => (R z).re + ‖G z‖ ^ 2) μ := hRre.add hGsq
  have hRGC : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2)) μ :=
    hRG.add (hCsq.const_mul (4 * M + 2 * B ^ 2))
  
  have hmono : (∫ z, J z / (2 * M) ∂μ) ≤
      ∫ z, (R z).re + ‖G z‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2 ∂μ := by
    apply integral_mono_ae (hJ.div_const (2 * M)) (hRGC.add (hvsq.const_mul (32 * B ^ 2 * M ^ 3 + 2)))
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    have hdv := (hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    have hp := dirichlet_localized_energy_absorption hM hB (η z)
      (dirD η 1 z) (dirD η Complex.I z)
      (v z) (dirD v 1 z) (dirD v Complex.I z) (F 0 z) (F 1 z) (C 0 z) (C 1 z) (G z)
      (hη z) (hηgrad z 0)
      (hηgrad z 1)
      (hcoer z hzU) (hFbound z hzU)
    have hRpoint : R z =
        (F 0 z + C 0 z) * (dirichletCutoffWeight η z * conj (dirD v 1 z) +
          (dirD η 1 z * conj (η z) +
            η z * conj (dirD η 1 z)) * conj (v z)) +
        (F 1 z + C 1 z) * (dirichletCutoffWeight η z * conj (dirD v Complex.I z) +
          (dirD η Complex.I z * conj (η z) +
            η z * conj (dirD η Complex.I z)) * conj (v z)) -
        G z * dirichletCutoffWeight η z * conj (v z) := by
      dsimp [R]
      rw [Fin.sum_univ_two]
      simp [coordDir]
      rw [dirichlet_cutoff_conj_product_dirD η hdv 1,
        dirichlet_cutoff_conj_product_dirD η hdv Complex.I]
      ring
    change J z / (2 * M) ≤ (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2
    rw [hRpoint]
    exact hp
  rw [integral_add hRGC (hvsq.const_mul _),
    integral_add hRG (hCsq.const_mul _), integral_add hRre hGsq,
    hRzero, zero_add, integral_const_mul, integral_const_mul] at hmono
  simpa [J, div_eq_mul_inv, integral_mul_const] using hmono

theorem dirichlet_graph_flux_conj_pair (d : ℝ) (x y : ℂ) :
    ((x - (d : ℂ) * y) * conj x +
      (-(d : ℂ) * x + (1 + (d : ℂ) ^ 2) * y) * conj y).re =
      ‖x - (d : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

theorem dirichletShiftedFlux_coercive {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      (dirichletShiftedFlux f h v 0 z * conj (dirD v 1 z) +
        dirichletShiftedFlux f h v 1 z * conj (dirD v Complex.I z)).re := by
  simp only [dirichletShiftedFlux, Matrix.cons_val_zero, Matrix.cons_val_one, dirichletGraphSlope]
  rw [dirichlet_graph_flux_conj_pair]
  exact (smoothDirichletGraph_complex_energy_bounds hLip (z + h).re _ _).1

theorem dirichletShiftedFlux_norm_sum_bound {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    ‖dirichletShiftedFlux f h v 0 z‖ + ‖dirichletShiftedFlux f h v 1 z‖ ≤
      2 * (2 * (1 + (K : ℝ) ^ 2)) * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖) := by
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let d := dirichletGraphSlope f (z + h)
  let x := dirD v 1 z
  let y := dirD v Complex.I z
  have hd : ‖d‖ ≤ (K : ℝ) := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have h₁ : 1 ≤ M := by nlinarith [sq_nonneg K]
  have hK : (K : ℝ) ≤ M := by nlinarith [sq_nonneg ((K : ℝ) - 1)]
  have hKK : 1 + (K : ℝ) ^ 2 ≤ M := by nlinarith [sq_nonneg (K : ℝ)]
  have ha  := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖d ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖d‖ ^ 2 := by simp
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hd 2)
  have hdM  := hd.trans hK
  have haM  := ha.trans hKK
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
        simp only [norm_mul, norm_neg]
        exact add_le_add (mul_le_mul_of_nonneg_right hdM (norm_nonneg x))
          (mul_le_mul_of_nonneg_right haM (norm_nonneg y))
      _ = _ := by ring
  change ‖x - d * y‖ + ‖-d * x + (1 + d ^ 2) * y‖ ≤ 2 * M * (‖x‖ + ‖y‖)
  linarith

theorem dirichletShiftedFlux_memLp {U : Set ℂ} {f : ℝ → ℝ} {K : NNReal}
    (hf : ContDiff ℝ ∞ f) (hLip : LipschitzWith K f) (h : ℝ) {v : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict U)) (i : Fin 2) :
    MemLp (dirichletShiftedFlux f h v i) 2 (volume.restrict U) := by
  let d  := fun z => dirichletGraphSlope f (z + h)
  have hd : Continuous d := (dirichletGraphSlope_contDiff hf).continuous.comp
    (continuous_id.add continuous_const)
  have hdb (z : ℂ) : ‖d z‖ ≤ (K : ℝ) := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have hdx := hg 0
  have hdy := hg 1
  
  have hndX := dirichlet_bounded_mul_memLp hd.neg.aestronglyMeasurable
    (fun z => by aesop) hdx
  have hab (z : ℂ)  := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖d z ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖d z‖ ^ 2 := by simp
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hdb z) 2)
  have haY := dirichlet_bounded_mul_memLp
    (by fun_prop) hab hdy
  fin_cases i
  · exact hdx.sub (dirichlet_bounded_mul_memLp hd.aestronglyMeasurable hdb hdy)
  · exact hndX.add haY

/-- A compact smooth test has a genuine bound for both actual coordinate
derivatives. Keeping the test abstract avoids unfolding a concrete bump
inside the compact-support derivative estimates. -/
theorem exists_dirichlet_smoothTraceTest_gradient_bound :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B := by
  have h₀ := η.property.dirD 1
  have h₁ := η.property.dirD Complex.I
  obtain ⟨B₀, hB₀⟩ := h₀.2.1.exists_bound_of_continuous h₀.1.continuous
  obtain ⟨B₁, hB₁⟩ := h₁.2.1.exists_bound_of_continuous h₁.1.continuous
  
  refine ⟨(max 0 (max B₀ B₁)), le_max_left _ _, ?_⟩
  intro z i
  fin_cases i
  · aesop
  · aesop

include κ in
/-- The actual complex-valued smooth test associated with a real bump. -/
def dirichletComplexBumpTest : smoothTraceTests :=
  ⟨fun z => (κ z : ℂ),
    ⟨Complex.ofRealCLM.contDiff.comp κ.contDiff,
      κ.hasCompactSupport.comp_left
         Complex.ofReal_zero,
      subset_univ _⟩⟩

theorem dirichletComplexBumpTest_apply :
    dirichletComplexBumpTest κ z = (κ z : ℂ) := rfl

theorem dirichletComplexBumpTest_tsupport_subset :
    tsupport (dirichletComplexBumpTest κ : ℂ → ℂ) ⊆
      closedBall (0 : ℂ) κ.rOut := by
  
  rw [← κ.tsupport_eq]
  exact tsupport_comp_subset  Complex.ofReal_zero κ

theorem dirichletComplexBumpTest_norm_le_one :
    ‖dirichletComplexBumpTest κ z‖ ≤ 1 := by
  rw [dirichletComplexBumpTest_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (κ.nonneg' z)]
  exact κ.le_one

theorem dirichletComplexBumpTest_eq_one {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) κ.rIn) : dirichletComplexBumpTest κ z = 1 := by
  rw [dirichletComplexBumpTest_apply, κ.one_of_mem_closedBall hz, Complex.ofReal_one]

end

/-- A genuine cutoff equal to one on a smaller boundary half box,
with support avoiding the sides and top, is supplied by an actual
smooth bump. Its derivative bound follows from compact support. -/
theorem exists_dirichlet_boundary_energy_cutoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < a ∧ r < b ∧ ∃ (η : smoothTraceTests) (B : ℝ),
      0 ≤ B ∧ tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} ∧
      (∀ z : ℂ, ‖η z‖ ≤ 1) ∧
      (∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B) ∧
      ∀ z ∈ smoothDirichletHalfBox (r / 2) (r / 2), η z = 1 := by
  let r := min a b / 8
  have hr : 0 < r := (by positivity)
  have h2a : 2 * r < a := by
    grind
  have h2b : 2 * r < b := by
    grind
  let κ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr, by linarith⟩
  let η := dirichletComplexBumpTest κ
  
  have hη (z : ℂ) := dirichletComplexBumpTest_norm_le_one κ z
  have hηone (z : ℂ) (hz : z ∈ smoothDirichletHalfBox (r / 2) (r / 2)) : η z = 1 := by
    have hzn  := calc
        _ ≤ _ := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ r := by rw [abs_of_pos hz.2.1]; linarith [hz.1, hz.2.2]
    exact dirichletComplexBumpTest_eq_one κ
      (by simpa only [mem_closedBall, dist_zero_right] using hzn)
  obtain ⟨B, hB, hg⟩ := exists_dirichlet_smoothTraceTest_gradient_bound η
  refine ⟨r, hr, by linarith, by linarith, η, B, hB, ?_, hη, hg, hηone⟩
  intro z hz
  have hzκ  :=
    dirichletComplexBumpTest_tsupport_subset κ hz
  have hzn : ‖z‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_zero_right] using hzκ
  exact ⟨((Complex.abs_re_le_norm z).trans hzn).trans_lt h2a,
    ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzn)).trans_lt h2b⟩

theorem dirichlet_dirD_comm {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ ∞ u U) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hu := hs.contDiffAt (hU.mem_nhds hz)
  
  have hD (v w : ℂ) : dirD (dirD u v) w z = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    rw [fderiv_clm_apply ((hu.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)) (differentiableAt_const v)]
    simp
  rw [hD, hD]
  exact (hu.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

end PolyaNeumann

end
