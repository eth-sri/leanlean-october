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


noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff ComplexConjugate

variable {μ : Measure ℂ} {g : ℂ → ℂ}

/-- Real bilinearity alone gives invariance of the trace under a
unit rotation. Symmetry of the bilinear map is not needed. -/
theorem dirichlet_bilinear_rotated_trace (T : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)
    {e : ℂ} (he : ‖e‖ = 1) :
    T e e + T (Complex.I * e) (Complex.I * e) = T 1 1 + T Complex.I Complex.I := by
  let a := e.re
  let b := e.im
  rw [congrArg (fun w => T w w) (show e = a • 1 + b • Complex.I by
    apply Complex.ext <;> simp [a, b]), (congrArg (fun w => T w w) (show Complex.I * e = (-b) • 1 + a • Complex.I by
    apply Complex.ext <;> simp [a, b]))]
  simp only [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  calc
    _ = ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (T 1 1 + T Complex.I Complex.I) := by ring
    _ = _ := by rw [show a ^ 2 + (b : ℂ) ^ 2 = 1 by
      exact_mod_cast (by
      have h := congrArg (fun r => r ^ 2) he
      change ‖e‖ ^ 2 = 1 ^ 2 at h
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
      simpa [a, b, pow_two] using h), one_mul]

theorem dirichlet_rotated_lap {v : ℂ → ℂ} 
    (hv : ContDiffAt ℝ 2 v z) (he : ‖e‖ = 1) :
    dirD (dirD v e) e z + dirD (dirD v (Complex.I * e)) (Complex.I * e) z = lap v z := by
  have hD w : dirD (dirD v w) w z = fderiv ℝ (fderiv ℝ v) z w w := by
    change fderiv ℝ (fun u => fderiv ℝ v u w) z w = _
    rw [fderiv_clm_apply ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) (differentiableAt_const w)]
    simp [fderiv_const_apply]
  rw [hD, hD, lap, hD, hD]
  exact dirichlet_bilinear_rotated_trace _ he

/-- The actual real graph slope, regarded as a complex scalar. -/
def dirichletGraphSlope (f : ℝ → ℝ) (z : ℂ) : ℂ := ((deriv f z.re : ℝ) : ℂ)

theorem dirichletGraphSlope_contDiff 
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirichletGraphSlope f) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_infty_iff_deriv.mp hf).2.comp Complex.reCLM.contDiff)

@[simp] theorem dirD_dirichletGraphSlope_I 
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    dirD (dirichletGraphSlope f) Complex.I z = 0 := by
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z Complex.I = 0
  rw [(Complex.ofRealCLM.hasFDerivAt.comp z ((((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)).fderiv]
  simp

/-- The flux of the actual graph coefficient matrix. -/
local notation "Φ0" => Fin 2

def dirichletFlattenedFlux (f : ℝ → ℝ) (u : ℂ → ℂ) (i : Φ0) (z : ℂ) : ℂ :=
  ![dirD u 1 z - dirichletGraphSlope f z * dirD u Complex.I z,
    -dirichletGraphSlope f z * dirD u 1 z +
      (1 + dirichletGraphSlope f z ^ 2) * dirD u Complex.I z] i

def dirichletFlattenedDivergence (f : ℝ → ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletFlattenedFlux f u 0) 1 z +
    dirD (dirichletFlattenedFlux f u 1) Complex.I z

theorem dirichletFlattenedFlux_pullback (p c : ℂ) hc
     (hf : ContDiff ℝ ∞ f)  
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 0 z = dirD v (1 / c) (Ψ z)) ∧
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 1 z =
       dirD v (Complex.I / c) (Ψ z) - dirichletGraphSlope f z * dirD v (1 / c) (Ψ z)) := by
  have h := smoothDirichletGraphChart_pullback_gradient p c hc hf hv
  constructor
  · simpa [dirichletFlattenedFlux, dirichletGraphSlope, dirD]
      using h.1
  · let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
    let u := v ∘ Ψ
    let d := dirichletGraphSlope f z
    have hX : dirD u 1 z - d * dirD u Complex.I z = dirD v (1 / c) (Ψ z) := h.1
    have hY : dirD u Complex.I z = dirD v (Complex.I / c) (Ψ z) := h.2
    change -d * dirD u 1 z + (1 + d ^ 2) * dirD u Complex.I z = _
    calc
      _ = dirD u Complex.I z - d * (dirD u 1 z - d * dirD u Complex.I z) := by ring
      _ = _ := by rw [hX, hY]

/-- This is a pointwise identity for the actual physical function
and the actual graph chart. In particular, the resulting divergence
equation is not an additional assumption about the flattened solution. -/
theorem dirichletFlattenedDivergence_pullback {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) hc (hc₁ : ‖c‖ = 1)
     (hf : ContDiff ℝ ∞ f) 
    (hv : ContDiffOn ℝ ∞ v Ω) 
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    dirichletFlattenedDivergence f
      (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) z =
      lap v (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := v ∘ Ψ
  let g₀ := dirD v (1 / c)
  let g₁ := dirD v (Complex.I / c)
  have hvc := hv.contDiffAt (hΩ.mem_nhds hz)
  have hv₂ : ContDiffAt ℝ 2 v (Ψ z) := hvc.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdg w : DifferentiableAt ℝ (dirD v w) (Ψ z) :=
    ((hvc.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hn : ∀ᶠ w in 𝓝 z, Ψ w ∈ Ω := Ψ.continuous.continuousAt.eventually (hΩ.mem_nhds hz)
  have h₁ : dirichletFlattenedFlux f u 1 =ᶠ[𝓝 z]
      (fun w => g₁ (Ψ w) - dirichletGraphSlope f w * g₀ (Ψ w)) := by
    filter_upwards [hn] with w hw
    exact (dirichletFlattenedFlux_pullback p c hc hf
      ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).2
  have hcompI g (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) Complex.I z = dirD g (Complex.I / c) (Ψ z) :=
    (smoothDirichletGraphChart_pullback_gradient p c hc hf hg).2
  have hcompOne g (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) 1 z = dirD g (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g (Complex.I / c) (Ψ z) := by
    have he := sub_eq_iff_eq_add.mp ((smoothDirichletGraphChart_pullback_gradient p c hc hf hg).1)
    rw [hcompI g hg] at he
    exact he
  have hD₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD g₀ (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    change fderiv ℝ (dirichletFlattenedFlux f u 0) z 1 = _
    rw [(show dirichletFlattenedFlux f u 0 =ᶠ[𝓝 z] g₀ ∘ Ψ by
      filter_upwards [hn] with w hw
      exact (dirichletFlattenedFlux_pullback p c hc hf
        ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).1).fderiv_eq (𝕜 := ℝ)]
    exact hcompOne g₀ (hdg _)
  have he : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc₁, inv_one]
  calc
    _ = dirD g₀ (1 / c) (Ψ z) + dirD g₁ (Complex.I / c) (Ψ z) := by
      rw [dirichletFlattenedDivergence, hD₀, show dirD (dirichletFlattenedFlux f u 1) Complex.I z = dirD g₁ (Complex.I / c) (Ψ z) - dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) by
        have hgs := (dirichletGraphSlope_contDiff hf).differentiable (by simp)
        have hd₀ : DifferentiableAt ℝ (g₀ ∘ Ψ) z := (hdg (1 / c)).comp z hdΨ
        change fderiv ℝ (dirichletFlattenedFlux f u 1) z Complex.I = _
        rw [h₁.fderiv_eq (𝕜 := ℝ)]
        change fderiv ℝ ((g₁ ∘ Ψ) - (dirichletGraphSlope f * (g₀ ∘ Ψ))) z Complex.I = _
        rw [fderiv_sub ((hdg (Complex.I / c)).comp z hdΨ) ((hgs z).mul hd₀), fderiv_mul (hgs z) hd₀]
        simp
        change dirD (g₁ ∘ Ψ) Complex.I z -
          (dirichletGraphSlope f z * dirD (g₀ ∘ Ψ) Complex.I z +
            g₀ (Ψ z) * dirD (dirichletGraphSlope f) Complex.I z) = _
        rw [hcompI g₁ (hdg _), hcompI g₀ (hdg _), dirD_dirichletGraphSlope_I hf]
        ring]
      ring
    _ = lap v (Ψ z) := by
      simpa [g₀, g₁, div_eq_mul_inv] using dirichlet_rotated_lap hv₂ he

/-- Total directional derivatives of a function smooth on an open
set are again smooth on that same open set. -/
theorem dirichlet_contDiffOn_dirD  (hU : IsOpen U) 
    (hg : ContDiffOn ℝ ∞ g U) w :
    ContDiffOn ℝ ∞ (dirD g w) U := by
  intro z hz
  exact (((hg.contDiffAt (hU.mem_nhds hz)).fderiv_right
    (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).contDiffWithinAt

/-- Local smoothness plus a genuine compact test suffices for this
integrability statement. No global second-derivative energy is used. -/
theorem dirichlet_local_smooth_mul_test_integrable  (hU : IsOpen U)
     (hg : ContDiffOn ℝ ∞ g U) (hφ : TestFunction U φ) :
    IntegrableOn (fun z => g z * φ z) U := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  rw [show (fun z => g z * φ z) = (fun z => G z * φ z) by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hz]]
  exact (hG.memLp' 2).integrable_mul (hφ.memLp' 2)

theorem dirichlet_local_smooth_field_test_eq_neg_dirD  (hU : IsOpen U)
     (hg : ContDiffOn ℝ ∞ g U) (hφ : TestFunction U φ)
    i :
    (∫ z in U, g z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD g (coordDir i) z * φ z) := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have hu := hG.memLp' 2 (μ := volume.restrict U)
  have hgrad j := (hG.dirD (coordDir j)).memLp' 2 (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth hG.1 hu hgrad φ hφ i
  change (∫ z in U, (hu.toLp G) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hgrad i).toLp _) z * φ z) at hw
  rw [integral_congr_ae (show (fun z => (hu.toLp G) z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U] (fun z => g z * dirD φ (coordDir i) z) by
    filter_upwards [hu.coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]), integral_congr_ae (show (fun z => ((hgrad i).toLp _) z * φ z) =ᵐ[volume.restrict U] (fun z => dirD g (coordDir i) z * φ z) by
    filter_upwards [(hgrad i).coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD g (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i))
          ((hGg z hz).fderiv_eq (𝕜 := ℝ))]
    · simp [image_eq_zero_of_notMem_tsupport hz])] at hw
  exact hw

theorem dirichletFlattenedFlux_contDiffOn  (hU : IsOpen U)
     (hf : ContDiff ℝ ∞ f) 
    (hu : ContDiffOn ℝ ∞ u U) i :
    ContDiffOn ℝ ∞ (dirichletFlattenedFlux f u i) U := by
  have hx := dirichlet_contDiffOn_dirD hU hu 1
  have hy := dirichlet_contDiffOn_dirD hU hu Complex.I
  have hd := (dirichletGraphSlope_contDiff hf).contDiffOn (s := U)
  fin_cases i
  · exact hx.sub (hd.mul hy)
  · exact (hd.neg.mul hx).add ((contDiffOn_const.add (hd.pow 2)).mul hy)

local notation "Φ2" => ball 0 1

theorem riemannMappingDirichletRemainder_contDiffOn 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F (Φ2))
    (hinj : InjOn F (Φ2)) (himage : F '' Φ2 = Ω)
    d :
    ContDiffOn ℝ ∞ (riemannMappingDirichletRemainder F d) Ω :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)).sub
      d.property.1.contDiffOn

/-- Every actual smooth datum gives this physical Laplacian identity;
the selected datum is needed only for the separately proved zero
boundary values. -/
theorem riemannMappingDirichletRemainder_lap 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F (Φ2))
    (hinj : InjOn F (Φ2)) (himage : F '' Φ2 = Ω)
    d  (hz : z ∈ Ω) :
    lap (riemannMappingDirichletRemainder F d) z = -lap (d : ℂ → ℂ) z := by
  have hharm := (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
    Complex.ofRealCLM
  have hh := (hharm z hz).1
  exact (lap_sub_of_contDiffAt hh (d.property.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))).trans (by
    rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds, Pi.zero_apply, zero_sub])

/-! ### Actual zero-boundary test approximation -/

theorem dirichlet_bounded_mul_memLp  {a g : ℂ → ℂ} 
    (ha : AEStronglyMeasurable a μ) (hbound : ∀ z, ‖a z‖ ≤ C)
    (hg : MemLp g 2 μ) : MemLp (fun z => a z * g z) 2 μ := by
  apply hg.of_le_mul (c := C) (ha.mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖a z * g z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _)

theorem dirichlet_localized_memLp  (η : smoothTraceTests) 
    (hg : MemLp g 2 μ) : MemLp (fun z => η z * g z) 2 μ := by
  obtain ⟨C, hC⟩ := η.property.2.1.exists_bound_of_continuous η.property.1.continuous
  exact dirichlet_bounded_mul_memLp η.property.1.continuous.aestronglyMeasurable hC hg

theorem dirichlet_localized_gradient_memLp  (hU : IsOpen U)
    (η : smoothTraceTests)  (hs : ContDiffOn ℝ ∞ g U)
    (hm : MemLp g 2 (volume.restrict U)) {i : Φ0}
    (hg : MemLp (dirD g (coordDir i)) 2 (volume.restrict U)) :
    MemLp (dirD (fun z => η z * g z) (coordDir i)) 2 (volume.restrict U) := by
  apply ((dirichlet_localized_memLp η hg).add (dirichlet_localized_memLp ⟨dirD η (coordDir i), η.property.dirD (coordDir i)⟩ hm)).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  exact (show dirD (fun u => η u * g u) (coordDir i) z = η z * dirD g (coordDir i) z + dirD (η : ℂ → ℂ) (coordDir i) z * g z by
    change fderiv ℝ ((η : ℂ → ℂ) * g) z (coordDir i) = _
    rw [fderiv_mul ((η.property.1.differentiable (by simp)) z) ((hs.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz))]
    simp [dirD]
    ring).symm

/-- These are genuine compact interior tests, with convergence in
all three actual H¹ energies. The localization can touch the flat
boundary; its sides and top remain inside the coordinate rectangle. -/
theorem dirichlet_localized_zero_boundary_test_approximation {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
     (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Φ0, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    (let v := fun z => η z * g z
     (∀ ε : ℝ, 0 < ε → TestFunction (smoothDirichletHalfBox a b)
       (fun z => dirichletNormalCutoff ε z * v z)) ∧
     Tendsto (fun ε => ∫ z in smoothDirichletHalfBox a b,
       ‖dirichletNormalCutoff ε z * v z - v z‖ ^ 2) (𝓝[>] 0) (𝓝 0) ∧
     ∀ i : Φ0, Tendsto (fun ε => ∫ z in smoothDirichletHalfBox a b,
       ‖dirD (fun u => dirichletNormalCutoff ε u * v u) (coordDir i) z -
         dirD v (coordDir i) z‖ ^ 2) (𝓝[>] 0) (𝓝 0)) := by
  let v : ℂ → ℂ := fun z => η z * g z
  have hv : ContinuousOn v (smoothDirichletClosedHalfBox a b) :=
    η.property.1.continuous.continuousOn.mul hc
  have hvS : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b) :=
    η.property.1.contDiffOn.mul hs
  have hvm := dirichlet_localized_memLp η hm
  have hvg i := dirichlet_localized_gradient_memLp
    (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have heq : (fun z => dirichletNormalCutoff ε z * v z) =
        (fun z => η z * dirichletNormalCutoff ε z * g z) := by
      funext z
      dsimp only [v]
      ring
    rw [heq]
    exact dirichletNormalCutoff_testFunction hε η hη hs
  · have h := dirichletNormalCutoff_weight_error_energy_tendsto_zero hvm
    apply h.congr'
    exact Eventually.of_forall fun ε => by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change ‖(dirichletNormalCutoff ε z - 1) * v z‖ ^ 2 = _
        have heq : (dirichletNormalCutoff ε z - 1) * v z =
            dirichletNormalCutoff ε z * v z - v z := by ring
        rw [heq]
  · intro i
    fin_cases i
    · apply dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero hvS
      simpa [coordDir] using hvg 0
    · apply dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero hb hv hvS (by
      intro x hx
      simp [v, hz x hx]) hvm
      simpa [coordDir] using hvg 1

theorem dirichlet_eLpNorm_toReal_eq_sqrt_energy  
    (hg : MemLp g 2 μ) :
    (eLpNorm g 2 μ).toReal = Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂μ) := by
  rw [← Lp.norm_toLp g hg, ← norm_sq_toLp_eq_integral hg,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Actual L² energy convergence gives convergence of pairing
against any fixed actual L² function. This is the Cauchy–Schwarz
step needed to pass genuine interior tests to the boundary. -/
theorem dirichlet_pairing_tendsto_zero_of_energy 
     (hg : MemLp g 2 μ) {e : ℝ → ℂ → ℂ}
    (he : ∀ᶠ ε : ℝ in 𝓝[>] 0, MemLp (e ε) 2 μ)
    (hE : Tendsto (fun ε => ∫ z, ‖e ε z‖ ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ z, g z * e ε z ∂μ) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (show Tendsto (fun ε => (eLpNorm g 2 μ).toReal * Real.sqrt (∫ z, ‖e ε z‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) by
    simpa using tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hE))
  · exact Eventually.of_forall fun ε => norm_nonneg _
  · filter_upwards [he] with ε hε
    simpa [dirichlet_eLpNorm_toReal_eq_sqrt_energy hε] using
      norm_integral_mul_le_eLpNorm hg hε

theorem dirichlet_pairing_tendsto_of_energy_approximation 
    {g k : ℂ → ℂ} (hg : MemLp g 2 μ) (hk : MemLp k 2 μ) {kε : ℝ → ℂ → ℂ}
    (hmem : ∀ᶠ ε : ℝ in 𝓝[>] 0, MemLp (kε ε) 2 μ)
    (hE : Tendsto (fun ε => ∫ z, ‖kε ε z - k z‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ z, g z * kε ε z ∂μ) (𝓝[>] 0)
      (𝓝 (∫ z, g z * k z ∂μ)) := by
  apply (show Tendsto (fun ε => (∫ z, g z * (kε ε z - k z) ∂μ) + ∫ z, g z * k z ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z * k z ∂μ)) by
    simpa using ((dirichlet_pairing_tendsto_zero_of_energy hg (hmem.mono fun _ h => h.sub hk) hE).add (tendsto_const_nhds : Tendsto (fun _ : ℝ => ∫ z, g z * k z ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z * k z ∂μ))))).congr'
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
    (hη : tsupport η ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
     (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Φ0, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {F : Φ0 → ℂ → ℂ} 
    (hF : ∀ i : Φ0, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Φ0, F i z * dirD φ (coordDir i) z) =
        ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Φ0,
      F i z * dirD (fun u => η u * g u) (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * (η z * g z) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let v : ℂ → ℂ := fun z => η z * g z
  let vε : ℝ → ℂ → ℂ := fun ε z => dirichletNormalCutoff ε z * v z
  obtain ⟨htest, hvalue, hgradient⟩ :=
    dirichlet_localized_zero_boundary_test_approximation hb η hη hc hs hz hm hg
  have hvg i : MemLp (dirD v (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  have hεg i : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      MemLp (dirD (vε ε) (coordDir i)) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((htest ε hε).dirD (coordDir i)).memLp' 2
  have hleft i : Tendsto
      (fun ε => ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z, F i z * dirD v (coordDir i) z ∂μ)) :=
    dirichlet_pairing_tendsto_of_energy_approximation (hF i) (hvg i) (hεg i) (hgradient i)
  have hright :=
    dirichlet_pairing_tendsto_of_energy_approximation hG (dirichlet_localized_memLp η hm) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (htest ε hε).memLp' 2) hvalue
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hleft i)
  have heq : (fun ε => ∑ i : Φ0, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      =ᶠ[𝓝[>] 0] (fun ε => ∫ z, G z * vε ε z ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hisum : (∫ z, ∑ i : Φ0, F i z * dirD (vε ε) (coordDir i) z ∂μ) =
        ∑ i : Φ0, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ := by
      apply integral_finset_sum
      intro i _
      exact (hF i).integrable_mul (((htest ε hε).dirD (coordDir i)).memLp' 2)
    rw [← hisum]
    exact hweak _ (htest ε hε)
  change (∫ z, ∑ i : Φ0, F i z * dirD v (coordDir i) z ∂μ) = _
  rw [show (∫ z, ∑ i : Φ0, F i z * dirD v (coordDir i) z ∂μ) = ∑ i : Φ0, ∫ z, F i z * dirD v (coordDir i) z ∂μ by
    apply integral_finset_sum
    intro i _
    exact (hF i).integrable_mul (hvg i)]
  exact tendsto_nhds_unique hsum (hright.congr' heq.symm)

theorem dirichlet_halfBox_isBounded  :
    Bornology.IsBounded (smoothDirichletHalfBox a b) := by
  apply (isBounded_closedBall (x := 0) (r := a + b)).subset
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  calc
    _ ≤ _ := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add hz.1.le (by rw [abs_of_pos hz.2.1]; exact hz.2.2.le)

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
theorem dirichlet_interval_difference_energy_le 
    (ha : 0 < a) (hh : 0 < h) {v dv : ℝ → ℂ}
    (hv : ContinuousOn v (Icc (-a) (a + h)))
    (hdv : ContinuousOn dv (Icc (-a) (a + h)))
    (hd : ∀ x ∈ Icc (-a) (a + h), HasDerivAt v (dv x) x) :
    (∫ x in (-a)..a, ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2) ≤
      ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2 := by
  have haa : -a ≤ a := by linarith
  have hmap x (hx : x ∈ Icc (-a) a) :
      MapsTo (fun s => x + s) (Icc 0 h) (Icc (-a) (a + h)) := by
    intro s hs
    constructor <;> linarith [hx.1, hx.2, hs.1, hs.2]
  have hpoint x (hx : x ∈ Icc (-a) a) :
      ‖(v (x + h) - v x) / h‖ ^ 2 ≤
        h⁻¹ * ∫ s in 0..h, ‖dv (x + s)‖ ^ 2 := by
    have hds s (hs : s ∈ Ioo 0 h) :
        HasDerivAt (fun t => v (x + t) - v x) (dv (x + s)) s := by
      simpa using
        ((hd (x + s) (hmap x hx (Ioo_subset_Icc_self hs))).scomp s
          ((hasDerivAt_id s).const_add x)).sub_const (v x)
    have hp := dirichlet_zero_endpoint_norm_sq_le ((hv.comp (continuous_const.add continuous_id).continuousOn (hmap x hx)).sub continuousOn_const)
      (by simp) hds (dirichlet_continuousOn_memLp_Ioc (hdv.comp (continuous_const.add continuous_id).continuousOn (hmap x hx)))
      (⟨hh, le_rfl⟩)
    simp [abs_of_pos hh, div_pow] at hp ⊢
    apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
    calc
      _ ≤ _ := hp
      _ = _ := by
        field_simp [hh.ne']
  let E : ℝ × ℝ → ℝ := fun p => ‖dv (p.1 + p.2)‖ ^ 2
  have hiE : Integrable E
      ((volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc 0 h))) := by
    rw [Measure.prod_restrict]
    exact (((hdv.norm.pow 2).comp (continuous_fst.add continuous_snd).continuousOn (fun p hp => hmap p.1 hp.1 hp.2)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  calc
    _ ≤ _ := show (∫ x in (-a)..a, ‖(v (x + h) - v x) / h‖ ^ 2) ≤ h⁻¹ * ∫ x in (-a)..a, ∫ s in 0..h, E (x, s) by
      rw [intervalIntegral.integral_of_le haa,
        intervalIntegral.integral_of_le haa, ← integral_const_mul]
      apply integral_mono_ae ((show ContinuousOn (fun x => ‖(v (x + h) - v x) / h‖ ^ 2) (Icc (-a) a) by
        have hx : MapsTo (fun x => x + h) (Icc (-a) a) (Icc (-a) (a + h)) := by
          intro x hx
          constructor <;> linarith [hx.1, hx.2]
        exact (((hv.comp (continuous_id.add continuous_const).continuousOn hx).sub
          (hv.mono (Icc_subset_Icc le_rfl (by linarith)))).div_const h).norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        ((show Integrable (fun x => ∫ s in 0..h, E (x, s)) (volume.restrict (Ioc (-a) a)) by
          simpa [intervalIntegral.integral_of_le hh.le] using hiE.integral_prod_left).const_mul h⁻¹)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hpoint x (Ioc_subset_Icc_self hx)
    _ = _ := by rw [show (∫ x in (-a)..a, ∫ s in 0..h, E (x, s)) = ∫ s in 0..h, ∫ x in (-a)..a, E (x, s) by
      simp [intervalIntegral.integral_of_le haa, intervalIntegral.integral_of_le hh.le]
      exact integral_integral_swap hiE]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (by
        have hi : IntervalIntegrable (fun s => ∫ x in (-a)..a, E (x, s))
            volume 0 h := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
          simpa [IntegrableOn, intervalIntegral.integral_of_le haa] using hiE.integral_prod_right
        have hm := intervalIntegral.integral_mono_on_of_le_Ioo hh.le hi
          (intervalIntegrable_const (c := ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2))
          (fun s hs => by
            change (∫ x in (-a)..a, ‖dv (x + s)‖ ^ 2) ≤ _
            rw [intervalIntegral.integral_comp_add_right
              (f := fun x => ‖dv x‖ ^ 2) s]
            apply intervalIntegral.integral_mono_interval (by linarith [hs.1])
              (by linarith) (by linarith [hs.2])
              (Eventually.of_forall fun x => sq_nonneg _) ((hdv.norm.pow 2).intervalIntegrable_of_Icc (by linarith)))
        simpa using hm) (inv_nonneg.mpr hh.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

theorem dirichletTangentialDifference_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) 
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifference h u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hq := ((show MemLp (fun z => u (z + (h : ℂ))) 2 (volume.restrict (smoothDirichletHalfBox a b)) by
    let T := Homeomorph.addRight (h : ℂ)
    exact memLp_comp_bilip' (f := T) (K := 1) (isOpen_smoothDirichletHalfBox a b)
      (by norm_num) (show Isometry T by
        apply Isometry.of_dist_eq
        intro z w
        change dist (z + (h : ℂ)) (w + (h : ℂ)) = _
        simp only [dist_eq_norm]
        congr 1
        abel).lipschitz.lipschitzOnWith (show Isometry T.symm by
        apply Isometry.of_dist_eq
        intro z w
        change dist (z + -(h : ℂ)) (w + -(h : ℂ)) = _
        simp only [dist_eq_norm]
        congr 1
        abel).lipschitz.lipschitzOnWith (hm.mono_measure (Measure.restrict_mono_set volume (by
        rintro w ⟨z, hz, rfl⟩
        simpa [T, smoothDirichletHalfBox] using
          (⟨(abs_add_le z.re h).trans_lt ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin), hz.2⟩))))).sub (hm.mono_measure (Measure.restrict_mono_set volume (by
    intro z hz
    exact ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩)))).const_smul (h⁻¹)
  have he : h⁻¹ • ((fun z => u (z + h)) - u) =
      dirichletTangentialDifference h u := by
    funext z
    simp [dirichletTangentialDifference, div_eq_mul_inv]
    ring
  rw [he] at hq
  exact hq

/-- The same actual area integral, with horizontal slices first.
The real-coordinate measure has exactly Jacobian one. -/
theorem dirichlet_halfBox_sq_integral_eq_horizontal_real_prod 
    (ha : 0 < a) (hb : 0 < b) 
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ y in Ioo 0 b, ∫ x in (-a)..a,
        ‖g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
  rw [dirichlet_halfBox_sq_integral_eq_real_prod hb hg]
  simp_rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
  rw [integral_integral_swap (dirichlet_halfBox_sq_integrable_real_prod hg)]
  simp_rw [intervalIntegral.integral_of_le (show -a ≤ a by linarith),
    integral_Ioc_eq_integral_Ioo]

/-- Actual finite first-derivative energy gives a uniform L²
tangential difference-quotient estimate all the way to the flat
boundary. Smoothness is used only at interior horizontal segments;
there is no assumed second derivative at the boundary. -/
theorem dirichlet_halfBox_tangential_difference_energy_le {A a b h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hmargin : a + h < A)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hDx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖dirichletTangentialDifference h u z‖ ^ 2) ≤
      ∫ z in smoothDirichletHalfBox A b, ‖dirD u 1 z‖ ^ 2 := by
  have hq := dirichletTangentialDifference_memLp
    (by rw [abs_of_pos hh]; exact hmargin.le) hm
  have hprodD := dirichlet_halfBox_sq_integrable_real_prod hDx
  rw [dirichlet_halfBox_sq_integral_eq_horizontal_real_prod ha hb hq,
    dirichlet_halfBox_sq_integral_eq_horizontal_real_prod (lt_trans ha (lt_trans (by linarith : a < a + h) hmargin)) hb hDx]
  exact integral_mono_ae (by
    simpa [intervalIntegral.integral_of_le (show -a ≤ a by linarith), integral_Ioc_eq_integral_Ioo] using (dirichlet_halfBox_sq_integrable_real_prod hq).integral_prod_right) (by
    simpa [intervalIntegral.integral_of_le (show -A ≤ A by linarith), integral_Ioc_eq_integral_Ioo] using hprodD.integral_prod_right) (by
    filter_upwards [hprodD.prod_left_ae, ae_restrict_mem measurableSet_Ioo]
      with y hdy hy
    let L : ℝ → ℂ := fun x => x + y * Complex.I
    have hLc : Continuous L := Complex.ofRealCLM.continuous.add continuous_const
    have hmap : MapsTo L (Icc (-a) (a + h)) (smoothDirichletHalfBox A b) := by
      intro x hx
      simpa [L, smoothDirichletHalfBox] using
        ⟨abs_lt.mpr ⟨by linarith [hx.1], hx.2.trans_lt hmargin⟩, hy⟩
    have hd x (hx : x ∈ Icc (-a) (a + h)) :
        HasDerivAt (u ∘ L) ((dirD u 1 ∘ L) x) x := by
      exact (((hs.contDiffAt ((isOpen_smoothDirichletHalfBox A b).mem_nhds (hmap hx))).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt x (((hasDerivAt_id x).ofReal_comp).add_const (y * Complex.I))
    have hi := dirichlet_interval_difference_energy_le ha hh (hs.continuousOn.comp hLc.continuousOn hmap) ((dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs 1).continuousOn.comp hLc.continuousOn hmap) hd
    exact (show (∫ x in (-a)..a, ‖dirichletTangentialDifference h u (L x)‖ ^ 2) ≤ ∫ x in (-a)..(a + h), ‖dirD u 1 (L x)‖ ^ 2 by
      simpa [dirichletTangentialDifference, L, add_right_comm] using hi).trans (intervalIntegral.integral_mono_interval (by linarith) (by linarith) hmargin.le (Eventually.of_forall fun x => sq_nonneg _) (by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      simpa [IntegrableOn, L, restrict_Ioo_eq_restrict_Ioc] using hdy)))

/-- Every fixed tangential difference quotient is a genuine H¹
function on the smaller half box. Its derivative is the difference
quotient of the actual first derivative; this is proved from the
ordinary chain rule, not from an assumed H² bound. -/
theorem dirichletTangentialDifference_dirD {h : ℝ}  
    (hz : DifferentiableAt ℝ u z) (hzh : DifferentiableAt ℝ u (z + (h : ℂ))) w :
    dirD (dirichletTangentialDifference h u) w z =
      dirichletTangentialDifference h (dirD u w) z := by
  change fderiv ℝ (dirichletTangentialDifference h u) z w = _
  rw [(show HasFDerivAt (dirichletTangentialDifference h u) ((h : ℂ)⁻¹ • (fderiv ℝ u (z + h) - fderiv ℝ u z)) z by
    rw [show dirichletTangentialDifference h u = fun y => ((u ∘ fun z => z + (h : ℂ)) - u) y * (h : ℂ)⁻¹ by
      funext y
      simp [dirichletTangentialDifference, div_eq_mul_inv]]
    simpa using
      ((hzh.hasFDerivAt.comp z ((hasFDerivAt_id z).add_const (h : ℂ))).sub hz.hasFDerivAt).mul_const ((h : ℂ)⁻¹)).fderiv]
  simp [dirichletTangentialDifference, dirD, div_eq_mul_inv]
  ring

theorem dirichletTangentialDifference_continuousOn 
    (hmargin : a + |h| ≤ A) 
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifference h u) (smoothDirichletClosedHalfBox a b) := by
  exact ((hc.comp (continuous_id.add continuous_const).continuousOn (by
    intro z hz
    simpa [smoothDirichletClosedHalfBox] using
      (⟨(abs_add_le z.re h).trans ((add_le_add hz.1 le_rfl).trans hmargin), hz.2⟩))).sub
    (hc.mono (by
      intro z hz
      exact ⟨hz.1.trans (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩))).div_const h

theorem dirichletTangentialDifference_contDiffOn 
    (hmargin : a + |h| ≤ A) 
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ ∞ (dirichletTangentialDifference h u)
      (smoothDirichletHalfBox a b) := by
  exact ((hs.comp (contDiff_id.add contDiff_const).contDiffOn (by
    intro z hz
    simpa [smoothDirichletHalfBox] using
      (⟨(abs_add_le z.re h).trans_lt ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin), hz.2⟩))).sub
    (hs.mono (by
      intro z hz
      exact ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩))).div_const h

theorem dirichletTangentialDifference_zero_bottom {A a h : ℝ}
    (hmargin : a + |h| ≤ A) 
    (hz : ∀ x : ℝ, |x| < A → u x = 0)  (hx : |x| < a) :
    dirichletTangentialDifference h u (x : ℂ) = 0 := by
  simp [dirichletTangentialDifference, ← Complex.ofReal_add, hz x (hx.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin)), hz (x + h) ((abs_add_le x h).trans_lt ((add_lt_add_of_lt_of_le hx le_rfl).trans_le hmargin))]

/-- The actual coefficient matrix at the shifted horizontal point,
acting on the gradient at the original point. -/
def dirichletShiftedFlux (f : ℝ → ℝ) (h : ℝ) (v : ℂ → ℂ)
    (i : Φ0) (z : ℂ) : ℂ :=
  ![dirD v 1 z - dirichletGraphSlope f (z + (h : ℂ)) * dirD v Complex.I z,
    -dirichletGraphSlope f (z + (h : ℂ)) * dirD v 1 z +
      (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) * dirD v Complex.I z] i

/-- The pointwise absorption estimate for a complex-valued
localized elliptic test. The coefficient coercivity and norm bounds
are algebraic inputs; the actual graph matrix supplies both below.
The cutoff is allowed to be complex, since its weight is `η·conj η`. -/
theorem dirichlet_localized_energy_absorption 
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
  have hρnorm : ‖ρ‖ = ‖η‖ ^ 2 := by simp only [ρ, norm_mul, norm_conj, pow_two]
  have hb₀ : ‖b₀‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ _ := norm_add_le _ _
      _ = 2 * ‖α‖ * ‖η‖ := by simp only [norm_mul, norm_conj]; ring
      _ ≤ _ := by gcongr
  have hb₁ : ‖b₁‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ _ := norm_add_le _ _
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
  have hCmain : ‖ρ * (C₀ * conj x + C₁ * conj y)‖ ≤ c * Y := by
    rw [norm_mul, hρnorm]
    calc
      _ ≤ ‖η‖ ^ 2 * (c * X) := mul_le_mul_of_nonneg_left (by
        calc
          _ ≤ _ := norm_add_le _ _
          _ = ‖C₀‖ * ‖x‖ + ‖C₁‖ * ‖y‖ := by simp only [norm_mul, norm_conj]
          _ ≤ _ := by
            dsimp [c, X]
            nlinarith only [mul_nonneg (norm_nonneg C₀) (norm_nonneg y),
              mul_nonneg (norm_nonneg C₁) (norm_nonneg x)]) (sq_nonneg _)
      _ ≤ ‖η‖ * (c * X) := mul_le_mul_of_nonneg_right hηsq (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
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
    have hηsq₁ := hηsq.trans hη
    calc
      _ ≤ ‖G‖ * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have hYoung' : Y * S ≤ T / (2 * M) + 2 * M * c ^ 2 +
      32 * B ^ 2 * M ^ 3 * ‖v‖ ^ 2 := by
    calc
      _ ≤ _ := (show Y * S ≤ Y ^ 2 / (4 * M) + M * S ^ 2 by
        calc
          Y * S = 4 * M * Y * S / (4 * M) := by field_simp [hM.ne']
          _ ≤ (Y ^ 2 + 4 * M ^ 2 * S ^ 2) / (4 * M) :=
            div_le_div_of_nonneg_right (by
              nlinarith only [sq_nonneg (Y - 2 * M * S)]) (mul_pos (by norm_num) hM).le
          _ = _ := by field_simp [hM.ne'])
      _ ≤ 2 * T / (4 * M) + M *
          (2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2) :=
        add_le_add (div_le_div_of_nonneg_right (by
          dsimp [Y, X, T]
          convert mul_le_mul_of_nonneg_left (show (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) by
            nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]) (sq_nonneg ‖η‖) using 1 <;> ring) (show 0 < 4 * M by positivity).le)
          (mul_le_mul_of_nonneg_left (by
            dsimp [S]
            nlinarith only [sq_nonneg (c - 4 * B * M * ‖v‖)]) hM.le)
      _ = _ := by field_simp [hM.ne']; ring
  have herr' : ‖err‖ ≤ T / (2 * M) + ‖G‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
    linarith only [show ‖err‖ ≤ Y * S + 2 * B * c * ‖v‖ + ‖G‖ * ‖v‖ by
      calc
        _ ≤ _ := norm_sub_le _ _
        _ ≤ ((‖(F₀ * b₀ + F₁ * b₁) * conj v‖ +
            ‖ρ * (C₀ * conj x + C₁ * conj y)‖) +
            ‖(C₀ * b₀ + C₁ * b₁) * conj v‖) + ‖G * ρ * conj v‖ := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (4 * B * M * Y * ‖v‖ + c * Y) + 2 * B * c * ‖v‖ + ‖G‖ * ‖v‖ := by
          gcongr
        _ = _ := by dsimp [S]; ring, hYoung', show 2 * B * c * ‖v‖ ≤ B ^ 2 * c ^ 2 + ‖v‖ ^ 2 by
      nlinarith only [sq_nonneg (B * c - ‖v‖)], show ‖G‖ * ‖v‖ ≤ ‖G‖ ^ 2 + ‖v‖ ^ 2 by
      nlinarith only [sq_nonneg (‖G‖ - ‖v‖), sq_nonneg ‖G‖, sq_nonneg ‖v‖], (mul_le_mul_of_nonneg_left (show c ^ 2 ≤ 2 * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) by
      dsimp [c]
      nlinarith only [sq_nonneg (‖C₀‖ - ‖C₁‖)]) (show 0 ≤ 2 * M + B ^ 2 by positivity))]
  change T / (2 * M) ≤ _
  linarith only [show T / M ≤ main.re by
    rw [show main = (‖η‖ ^ 2 : ℝ) * (F₀ * conj x + F₁ * conj y) by rw [← (show ρ = (‖η‖ ^ 2 : ℝ) by
      simpa only [← Complex.ofReal_pow] using Complex.mul_conj' η)]]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ = ‖η‖ ^ 2 * ((‖x‖ ^ 2 + ‖y‖ ^ 2) / M) := by dsimp [T]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoer (sq_nonneg _), show main.re ≤ (L - G * ρ * conj v).re + ‖err‖ by
    rw [show L - G * ρ * conj v = main + err by dsimp [L, main, err]; ring, Complex.add_re]
    have h := Complex.re_le_norm (-err)
    simp only [Complex.neg_re, norm_neg] at h
    linarith only [h], herr', show T / M = T / (2 * M) + T / (2 * M) by
    field_simp [hM.ne']; ring]

/-- A genuine smooth compact weight, even for a complex cutoff. -/
def dirichletCutoffWeight (η : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => η z * conj (η z),
    ⟨η.property.1.mul (Complex.conjCLE.contDiff.comp η.property.1),
      η.property.2.1.mul_right, subset_univ _⟩⟩

theorem dirichlet_dirD_conj_at  
    (hu : DifferentiableAt ℝ u z) w :
    dirD (fun z => conj (u z)) w z = conj (dirD u w z) := by
  change fderiv ℝ (Complex.conjCLE ∘ u) z w = _
  rw [(Complex.conjCLE.hasFDerivAt.comp z hu.hasFDerivAt).fderiv]
  rfl

theorem dirichletCutoffWeight_dirD η w z :
    dirD (dirichletCutoffWeight η : ℂ → ℂ) w z =
      dirD (η : ℂ → ℂ) w z * conj (η z) +
        η z * conj (dirD (η : ℂ → ℂ) w z) := by
  have hη := ((η.property.1.differentiable (by simp)) z).hasFDerivAt
  change fderiv ℝ ((η : ℂ → ℂ) * (Complex.conjCLE ∘ η)) z w = _
  rw [(hη.mul (Complex.conjCLE.hasFDerivAt.comp z hη)).fderiv]
  simp [ContinuousLinearEquiv.coe_apply, Complex.conjCLE_apply, dirD]
  ring

theorem dirichlet_cutoff_conj_product_dirD η
      (hv : DifferentiableAt ℝ v z) w :
    dirD (fun z => dirichletCutoffWeight η z * conj (v z)) w z =
      dirichletCutoffWeight η z * conj (dirD v w z) +
        (dirD (η : ℂ → ℂ) w z * conj (η z) +
          η z * conj (dirD (η : ℂ → ℂ) w z)) * conj (v z) := by
  change fderiv ℝ ((dirichletCutoffWeight η : ℂ → ℂ) * (Complex.conjCLE ∘ v)) z w = _
  rw [((((dirichletCutoffWeight η).property.1.differentiable (by simp)) z).hasFDerivAt.mul (Complex.conjCLE.hasFDerivAt.comp z hv.hasFDerivAt)).fderiv]
  simp [Complex.conjCLE_apply]
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
    (hηgrad : ∀ z : ℂ, ∀ i : Φ0, ‖dirD η (coordDir i) z‖ ≤ B)
     (hc : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Φ0, MemLp (dirD v (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {F C : Φ0 → ℂ → ℂ} 
    (hF : ∀ i : Φ0, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hC : ∀ i : Φ0, MemLp (C i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hcoer : ∀ z ∈ smoothDirichletHalfBox a b,
      (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / M ≤
        (F 0 z * conj (dirD v 1 z) + F 1 z * conj (dirD v Complex.I z)).re)
    (hFbound : ∀ z ∈ smoothDirichletHalfBox a b,
      ‖F 0 z‖ + ‖F 1 z‖ ≤ 2 * M * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Φ0,
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
  let φ : ℂ → ℂ := fun z => dirichletCutoffWeight η z * conj (v z)
  let J : ℂ → ℝ := fun z =>
    ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
  let R : ℂ → ℂ := fun z =>
    (∑ i : Φ0, (F i z + C i z) * dirD φ (coordDir i) z) - G z * φ z
  have hU := isOpen_smoothDirichletHalfBox a b
  have hvs :=
    Complex.conjCLE.contDiff.comp_contDiffOn hs
  have hvg i : MemLp (dirD (fun z => conj (v z)) (coordDir i)) 2 μ := by
    apply (hg i).star.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    exact (dirichlet_dirD_conj_at
      ((hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)) _).symm
  have hφ := dirichlet_localized_memLp (dirichletCutoffWeight η) hm.star
  have hφg i : MemLp (dirD φ (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp hU (dirichletCutoffWeight η) hvs hm.star (hvg i)
  have heq : (∫ z, ∑ i : Φ0, (F i z + C i z) * dirD φ (coordDir i) z ∂μ) =
      ∫ z, G z * φ z ∂μ :=
    dirichlet_weak_equation_localized_zero_boundary_test hb
      (dirichletCutoffWeight η) (tsupport_mul_subset_left.trans hηsupp) (Complex.conjCLE.continuous.comp_continuousOn hc) hvs (by
        intro x hx
        simp [hz x hx]) hm.star hvg
      (fun i => (hF i).add (hC i)) hG hweak
  have hFluxInt : Integrable
      (fun z => ∑ i : Φ0, (F i z + C i z) * dirD φ (coordDir i) z) μ :=
    integrable_finset_sum _ (fun i _ =>
      ((hF i).add (hC i)).integrable_mul (hφg i))
  have hLoadInt : Integrable (fun z => G z * φ z) μ := hG.integrable_mul hφ
  have hRi : Integrable R μ := hFluxInt.sub hLoadInt
  have hηDy := dirichlet_localized_memLp η
    (by
      simpa [coordDir] using hg 1)
  have hGsq := hG.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hCsq : Integrable (fun z => ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) μ :=
    ((hC 0).integrable_norm_pow (by norm_num : 2 ≠ 0)).add
    ((hC 1).integrable_norm_pow (by norm_num : 2 ≠ 0))
  have hvsq := hm.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hRre : Integrable (fun z => (R z).re) μ := hRi.re
  have hRG : Integrable (fun z => (R z).re + ‖G z‖ ^ 2) μ := hRre.add hGsq
  have hRGC : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2)) μ :=
    hRG.add (hCsq.const_mul (4 * M + 2 * B ^ 2))
  have hmono : (∫ z, J z / (2 * M) ∂μ) ≤
      ∫ z, (R z).re + ‖G z‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2 ∂μ := by
    apply integral_mono_ae ((show Integrable J μ by
      apply (((dirichlet_localized_memLp η (by simpa [coordDir] using hg 0)).integrable_norm_pow (by norm_num : 2 ≠ 0)).add
        (hηDy.integrable_norm_pow (by norm_num : 2 ≠ 0))).congr
      filter_upwards with z
      change ‖η z * dirD v 1 z‖ ^ 2 + ‖η z * dirD v Complex.I z‖ ^ 2 = _
      simp [mul_pow]
      ring).div_const (2 * M)) (hRGC.add (hvsq.const_mul (32 * B ^ 2 * M ^ 3 + 2)))
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    have hdv := (hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    change J z / (2 * M) ≤ (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2
    rw [show R z = (F 0 z + C 0 z) * (dirichletCutoffWeight η z * conj (dirD v 1 z) + (dirD η 1 z * conj (η z) + η z * conj (dirD η 1 z)) * conj (v z)) + (F 1 z + C 1 z) * (dirichletCutoffWeight η z * conj (dirD v Complex.I z) + (dirD η Complex.I z * conj (η z) + η z * conj (dirD η Complex.I z)) * conj (v z)) - G z * dirichletCutoffWeight η z * conj (v z) by
      dsimp only [R]
      rw [Fin.sum_univ_two]
      simp [coordDir]
      rw [dirichlet_cutoff_conj_product_dirD η hdv 1,
        dirichlet_cutoff_conj_product_dirD η hdv Complex.I]
      dsimp only [φ]
      ring]
    exact dirichlet_localized_energy_absorption hM hB (η z) (dirD η 1 z) (dirD η Complex.I z) (v z) (dirD v 1 z) (dirD v Complex.I z) (F 0 z) (F 1 z) (C 0 z) (C 1 z) (G z) (hη z) (by simpa [coordDir] using hηgrad z 0) (by simpa [coordDir] using hηgrad z 1) (hcoer z hzU) (hFbound z hzU)
  rw [integral_add hRGC (hvsq.const_mul _),
    integral_add hRG (hCsq.const_mul _), integral_add hRre hGsq,
    show (∫ z, (R z).re ∂μ) = 0 by
      change (∫ z, RCLike.re (R z) ∂μ) = 0
      rw [integral_re hRi]
      have hR : (∫ z, R z ∂μ) = 0 := by
        dsimp only [R]
        rw [integral_sub hFluxInt hLoadInt, heq, sub_self]
      simp [hR, RCLike.zero_re], zero_add, integral_const_mul, integral_const_mul] at hmono
  simpa only [J, div_eq_mul_inv, integral_mul_const] using hmono

theorem dirichlet_graph_flux_conj_pair (d : ℝ) x y :
    ((x - (d : ℂ) * y) * conj x +
      (-(d : ℂ) * x + (1 + (d : ℂ) ^ 2) * y) * conj y).re =
      ‖x - (d : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

theorem dirichletShiftedFlux_coercive  
    (hLip : LipschitzWith K f) h v z :
    (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      (dirichletShiftedFlux f h v 0 z * conj (dirD v 1 z) +
        dirichletShiftedFlux f h v 1 z * conj (dirD v Complex.I z)).re := by
  simp only [dirichletShiftedFlux, Matrix.cons_val_zero, Matrix.cons_val_one, dirichletGraphSlope]
  rw [dirichlet_graph_flux_conj_pair]
  exact (smoothDirichletGraph_complex_energy_bounds hLip (z + h).re _ _).1

theorem dirichletShiftedFlux_norm_sum_bound  
    (hLip : LipschitzWith K f) h v z :
    ‖dirichletShiftedFlux f h v 0 z‖ + ‖dirichletShiftedFlux f h v 1 z‖ ≤
      2 * (2 * (1 + (K : ℝ) ^ 2)) * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖) := by
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let d := dirichletGraphSlope f (z + (h : ℂ))
  let x := dirD v 1 z
  let y := dirD v Complex.I z
  have hd : ‖d‖ ≤ (K : ℝ) := by
    simpa [d, dirichletGraphSlope] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have hdM := hd.trans (show (K : ℝ) ≤ M by dsimp [M]; nlinarith [sq_nonneg ((K : ℝ) - 1)])
  have hx : ‖x - d * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ _ := norm_sub_le _ _
      _ ≤ M * ‖x‖ + M * ‖y‖ := by
        rw [norm_mul]
        exact add_le_add (by nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ M by dsimp [M]; nlinarith [sq_nonneg (K : ℝ)])) (norm_nonneg x)])
          (mul_le_mul_of_nonneg_right hdM (norm_nonneg y))
      _ = _ := by ring
  have hy : ‖-d * x + (1 + d ^ 2) * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ M * ‖x‖ + M * ‖y‖ := by
        simp
        exact add_le_add (mul_le_mul_of_nonneg_right hdM (norm_nonneg x))
          (mul_le_mul_of_nonneg_right ((show ‖(1 : ℂ) + d ^ 2‖ ≤ 1 + (K : ℝ) ^ 2 by
            calc
              _ ≤ _ := norm_add_le _ _
              _ = _ := by rw [norm_one, norm_pow]
              _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hd 2)).trans (by dsimp [M]; nlinarith [sq_nonneg K])) (norm_nonneg y))
      _ = _ := by ring
  change ‖x - d * y‖ + ‖-d * x + (1 + d ^ 2) * y‖ ≤ _
  linarith

theorem dirichletShiftedFlux_memLp {U : Set ℂ}  
    (hf : ContDiff ℝ ∞ f) (hLip : LipschitzWith K f) h 
    (hg : ∀ i : Φ0, MemLp (dirD v (coordDir i)) 2 (volume.restrict U)) (i : Φ0) :
    MemLp (dirichletShiftedFlux f h v i) 2 (volume.restrict U) := by
  let d : ℂ → ℂ := fun z => dirichletGraphSlope f (z + h)
  have hd : Continuous d := (dirichletGraphSlope_contDiff hf).continuous.comp
    (continuous_id.add continuous_const)
  have hdb z : ‖d z‖ ≤ K := by
    simpa [d, dirichletGraphSlope] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + h).re)
  have hdx : MemLp (dirD v 1) 2 (volume.restrict U) := by
    simpa [coordDir] using hg 0
  have hdy : MemLp (dirD v Complex.I) 2 (volume.restrict U) := by
    simpa [coordDir] using hg 1
  have hndX := dirichlet_bounded_mul_memLp hd.neg.aestronglyMeasurable
    (fun z => by rw [Pi.neg_apply, norm_neg]; exact hdb z) hdx
  have hab z : ‖1 + d z ^ 2‖ ≤ 1 + K ^ 2 := by
    calc
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [norm_one, norm_pow]
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hdb z) 2)
  fin_cases i
  · exact hdx.sub (dirichlet_bounded_mul_memLp hd.aestronglyMeasurable hdb hdy)
  · exact hndX.add (dirichlet_bounded_mul_memLp (continuous_const.add (hd.pow 2)).aestronglyMeasurable hab hdy)

/-- The actual complex-valued smooth test associated with a real bump. -/
def dirichletComplexBumpTest (κ : ContDiffBump (0 : ℂ)) : smoothTraceTests :=
  ⟨fun z => (κ z : ℂ),
    ⟨Complex.ofRealCLM.contDiff.comp κ.contDiff,
      κ.hasCompactSupport.comp_left
        (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero,
      subset_univ _⟩⟩

theorem dirichletComplexBumpTest_apply κ z :
    dirichletComplexBumpTest κ z = (κ z : ℂ) := rfl

/-- A genuine cutoff equal to one on a smaller boundary half box,
with support avoiding the sides and top, is supplied by an actual
smooth bump. Its derivative bound follows from compact support. -/
theorem exists_dirichlet_boundary_energy_cutoff  (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < a ∧ r < b ∧ ∃ (η : smoothTraceTests) (B : ℝ),
      0 ≤ B ∧ tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} ∧
      (∀ z : ℂ, ‖η z‖ ≤ 1) ∧
      (∀ z : ℂ, ∀ i : Φ0, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B) ∧
      ∀ z ∈ smoothDirichletHalfBox (r / 2) (r / 2), η z = 1 := by
  let r := min a b / 8
  have hr : 0 < r := div_pos (lt_min ha hb) (by norm_num)
  have h2a : 2 * r < a := by
    dsimp only [r]
    linarith [min_le_left a b, lt_min ha hb]
  have h2b : 2 * r < b := by
    dsimp only [r]
    linarith [min_le_right a b, lt_min ha hb]
  let κ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr, by linarith⟩
  let η := dirichletComplexBumpTest κ
  have hηsupp : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} := by
    intro z hz
    have hzn : ‖z‖ ≤ 2 * r := by simpa using ((show tsupport (dirichletComplexBumpTest κ) ⊆ closedBall 0 κ.rOut by
      change tsupport (fun z => (κ z : ℂ)) ⊆ closedBall 0 κ.rOut
      rw [← κ.tsupport_eq]
      exact tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero κ) hz)
    exact ⟨((Complex.abs_re_le_norm z).trans hzn).trans_lt h2a,
      ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzn)).trans_lt h2b⟩
  have hη (z : ℂ) : ‖η z‖ ≤ 1 := by
    exact (by
      rw [dirichletComplexBumpTest_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (κ.nonneg' z)]
      exact κ.le_one)
  have hηone (z : ℂ) (hz : z ∈ smoothDirichletHalfBox (r / 2) (r / 2)) : η z = 1 := by
    have hzn : ‖z‖ ≤ r := by
      calc
        _ ≤ _ := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ r := by rw [abs_of_pos hz.2.1]; linarith [hz.1, hz.2.2]
    exact (by
      rw [dirichletComplexBumpTest_apply, κ.one_of_mem_closedBall (by simpa using hzn), Complex.ofReal_one])
  obtain ⟨B, hB, hg⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, ∀ i : Φ0, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B := by
    have h₀ := η.property.dirD 1
    have h₁ := η.property.dirD Complex.I
    obtain ⟨B₀, hB₀⟩ := h₀.2.1.exists_bound_of_continuous h₀.1.continuous
    obtain ⟨B₁, hB₁⟩ := h₁.2.1.exists_bound_of_continuous h₁.1.continuous
    let B := max 0 (max B₀ B₁)
    refine ⟨B, le_max_left _ _, ?_⟩
    intro z i
    fin_cases i
    · change ‖dirD η 1 z‖ ≤ B
      exact (hB₀ z).trans ((le_max_left B₀ B₁).trans (le_max_right 0 (max B₀ B₁)))
    · change ‖dirD η Complex.I z‖ ≤ B
      exact (hB₁ z).trans ((le_max_right B₀ B₁).trans (le_max_right 0 (max B₀ B₁)))
  exact ⟨r, hr, by linarith, by linarith, η, B, hB, hηsupp, hη, hg, hηone⟩

theorem dirichlet_dirD_comm  (hU : IsOpen U) 
    (hs : ContDiffOn ℝ ∞ u U)  (hz : z ∈ U) v w :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hu := hs.contDiffAt (hU.mem_nhds hz)
  have hD (v w : ℂ) : dirD (dirD u v) w z = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    rw [fderiv_clm_apply ((hu.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiableAt (by simp)) (differentiableAt_const v)]
    simp
  rw [hD, hD]
  exact (hu.isSymmSndFDerivAt (by
    simpa using
      (WithTop.coe_le_coe.mpr le_top))).eq w v

end PolyaNeumann

end
