module

public import RequestProject.RiemannMappingBoundaryDerivative
public import RequestProject.LocalDirichletGenuineChart
public import RequestProject.PhysicalHardySupport
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Recovering the actual angular boundary parametrization

A smooth, nonstationary inverse boundary trace on the unit circle has a
genuine smooth local angular inverse.  Composing its physical graph curve
with that inverse proves regularity of the actual forward circle trace.
No smoothness of the forward trace or of a collar extension is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex
open scoped Topology

/-- The actual local angular coordinate of a normalized circle-valued curve. -/
def riemannMappingBoundaryPhase (α : ℝ → ℂ) (t₀ t : ℝ) : ℝ :=
  (Complex.log (α t / α t₀)).im

variable {α : ℝ → ℂ} {t₀ : ℝ} (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ)

theorem riemannMappingBoundaryPhase_zero {α : ℝ → ℂ} {t₀ : ℝ}
    (h₀ : α t₀ ≠ 0) : riemannMappingBoundaryPhase α t₀ t₀ = 0 := by
  simp [riemannMappingBoundaryPhase]

/-- The principal logarithm is only used in a neighborhood of the value one. -/
theorem riemannMappingBoundaryPhase_contDiffAt (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀) (h₀ : α t₀ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (riemannMappingBoundaryPhase α t₀) t₀ := Complex.imCLM.contDiff.contDiffAt.comp t₀ (((Complex.contDiffAt_log (by simp_all)).restrict_scalars ℝ).comp   t₀ (hα.div_const _))

/-- A unit-modulus value is exactly recovered from its normalized phase. -/
theorem riemannMappingBoundaryPhase_circle {t₀ t : ℝ}
    (h₀ : ‖α t₀‖ = 1) (ht : ‖α t‖ = 1) :
    α t = α t₀ * circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) := by
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simp_all
  have hratio : ‖α t / α t₀‖ = 1 := by simp_all
  have hre : (Complex.log (α t / α t₀)).re = 0 := by
    rw [Complex.log_re, hratio, Real.log_one]
  have hlog : Complex.log (α t / α t₀) =
      riemannMappingBoundaryPhase α t₀ t * Complex.I := by
    simpa only [riemannMappingBoundaryPhase, hre, Complex.ofReal_zero, zero_add]
      using (Complex.re_add_im (Complex.log (α t / α t₀))).symm
  have hexp : circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) = α t / α t₀ := by
    simp only [circleMap_zero, Complex.ofReal_one, one_mul]
    rw [← hlog]
    exact Complex.exp_log (by
    intro h
    simp_all)
  grind 

theorem riemannMappingBoundaryPhase_circle_eventually (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) :
    ∀ᶠ t in 𝓝 t₀,
      α t = α t₀ * circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) :=
  hcircle.mono fun _ ht => riemannMappingBoundaryPhase_circle hcircle.self_of_nhds ht

/-- Nonstationarity of the circle curve forces a nonzero real phase derivative. -/
theorem riemannMappingBoundaryPhase_deriv_ne_zero (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0) :
    deriv (riemannMappingBoundaryPhase α t₀) t₀ ≠ 0 := by
  simp_all [((((hasDerivAt_circleMap 0 1 _).scomp t₀ ((riemannMappingBoundaryPhase_contDiffAt hα (by
    intro h
    simpa [h] using hcircle.self_of_nhds)).differentiableAt (by simp)).hasDerivAt).const_mul (α t₀)).congr_of_eventuallyEq       (riemannMappingBoundaryPhase_circle_eventually hcircle)).deriv]

/-- A smooth inverse circle curve supplies the genuine local angular inverse.
The output is an actual function obtained from the real inverse function theorem. -/
theorem exists_riemannMappingBoundaryAngularInverse {α : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = circleMap 0 1 θ₀) :
    ∃ g : ℝ → ℝ, g θ₀ = t₀ ∧ ContDiffAt ℝ (⊤ : ℕ∞) g θ₀ ∧
      HasDerivAt g (deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ θ₀ ∧
      ∀ᶠ θ in 𝓝 θ₀, α (g θ) = circleMap 0 1 θ := by
  let φ := riemannMappingBoundaryPhase α t₀
  have hn₀ : α t₀ ≠ 0 := by
    simp_all
  have hφ : ContDiffAt ℝ (⊤ : ℕ∞) φ t₀ :=
    riemannMappingBoundaryPhase_contDiffAt hα hn₀
  have hc  := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hd
  have hdφ  :=
    (hφ.differentiableAt (by simp)).hasDerivAt
  have hfd := hdφ.hasFDerivAt_equiv hc
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e := hφ.toOpenPartialHomeomorph φ hfd hn
  have he : e = φ := rfl
  have hφ₀ : φ t₀ = 0 := riemannMappingBoundaryPhase_zero hn₀
  have ht : 0 ∈ e.target := by
    simpa only [hφ₀] using hφ.image_mem_toOpenPartialHomeomorph_target hfd hn
  have he₀ : e.symm 0 = t₀ := by
    simpa only [he, hφ₀] using e.left_inv (hφ.mem_toOpenPartialHomeomorph_source hfd hn)
  have hid : HasDerivAt e (deriv φ t₀) (e.symm 0) := by
    simp_all
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) e.symm 0 := by
    apply e.contDiffAt_symm_deriv hc ht hid
    simp_all
  let g  := fun θ => e.symm (θ - θ₀)
  have hg₀ : g θ₀ = t₀ := by grind
  have hgs : ContDiffAt ℝ (⊤ : ℕ∞) g θ₀ := by
    have hi' : ContDiffAt ℝ (⊤ : ℕ∞) e.symm (θ₀ - θ₀) := by
      simp_all
    fun_prop
  have hshift : Tendsto (fun θ  => θ - θ₀) (𝓝 θ₀) (𝓝 0) := by
    have ht : Tendsto (fun θ  => θ - θ₀) (𝓝 θ₀) (𝓝 (θ₀ - θ₀)) :=
      continuousAt_id.sub continuousAt_const.tendsto
    simp_all
  have hright : ∀ᶠ θ in 𝓝 θ₀, φ (g θ) = θ - θ₀ := by
    simpa only [he] using
      hshift.eventually (e.eventually_right_inverse ht)
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by
    simpa only [hg₀] using hgs.continuousAt.tendsto
  refine ⟨g, hg₀, hgs, by
    simpa only [mul_one, Function.comp_def, id] using
      (e.hasDerivAt_symm ht hc hid).comp_of_eq θ₀ ((hasDerivAt_id θ₀).sub_const θ₀) (by simp), ?_⟩
  filter_upwards [hright, hgt.eventually (riemannMappingBoundaryPhase_circle_eventually hcircle)] with θ hθ hrec
  change α (g θ) = α t₀ * circleMap 0 1 (φ (g θ)) at hrec
  simp [hrec, hcenter, hθ, circleMap_zero_mul]

/-- Genuine inverse parametrization regularizes the actual forward circle trace.
Only the inverse curve and the physical graph curve have regularity premises. -/
theorem physicalCircleTrace_contDiffAt_of_inverse_curve {F : ℂ → ℂ}
    {α β : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hdα : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = circleMap 0 1 θ₀)
    (hβ : ContDiffAt ℝ (⊤ : ℕ∞) β t₀) (hdβ : deriv β t₀ ≠ 0)
    (hforward : ∀ᶠ t in 𝓝 t₀, F (α t) = β t) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace F) θ₀ ∧
      deriv (physicalCircleTrace F) θ₀ ≠ 0 := by
  obtain ⟨g, hg₀, hgs, hgd, hcircleG⟩ :=
    exists_riemannMappingBoundaryAngularInverse hα hcircle hdα hcenter
  have hc := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hdα
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by
    simpa only [hg₀] using hgs.continuousAt.tendsto
  have heq : physicalCircleTrace F =ᶠ[𝓝 θ₀] β ∘ g := by
    filter_upwards [hcircleG, hgt.eventually hforward] with θ hcircleθ hforwardθ
    simp_all [physicalCircleTrace]
  have hβg : ContDiffAt ℝ (⊤ : ℕ∞) (β ∘ g) θ₀ := by
    have hβ' : ContDiffAt ℝ (⊤ : ℕ∞) β (g θ₀) := by simp_all
    fun_prop
  have hdβg : HasDerivAt (β ∘ g)
      ((deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ • deriv β t₀) θ₀ := by
    apply ((hβ.differentiableAt (by simp)).hasDerivAt).scomp_of_eq θ₀ hgd hg₀.symm
  refine ⟨hβg.congr_of_eventuallyEq heq, ?_⟩
  simp_all [(hdβg.congr_of_eventuallyEq heq).deriv]

/-- The actual physical graph, restricted to its bottom horizontal line. -/
def riemannMappingGraphBoundaryCurve (p c : ℂ) (hc : c ≠ 0)
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) : ℂ :=
  smoothDirichletGraphChart p c hc f hf (x : ℂ)

theorem riemannMappingGraphBoundaryCurve_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) :=
  (smoothDirichletGraphChart_contDiff p c hc hf).comp Complex.ofRealCLM.contDiff

theorem riemannMappingGraphBoundaryCurve_hasDerivAt :
    HasDerivAt (riemannMappingGraphBoundaryCurve p c hc f hf.continuous)
      (c⁻¹ * (1 + deriv f x * Complex.I)) x := by
  unfold riemannMappingGraphBoundaryCurve
  simpa only [Function.comp_def,
    Complex.ofRealCLM_apply, ContinuousLinearMap.smul_apply,
    smoothDirichletGraphDifferential_apply, Complex.ofReal_re,
    Complex.ofReal_one, Complex.one_re, mul_one, Complex.real_smul, smul_eq_mul] using (smoothDirichletGraphChart_hasFDerivAt p c hc hf x).comp_hasDerivAt
    x (Complex.ofRealCLM.hasDerivAt )

theorem riemannMappingGraphBoundaryCurve_deriv_ne_zero :
    deriv (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) x ≠ 0 := by
  rw [(riemannMappingGraphBoundaryCurve_hasDerivAt p c hc hf x).deriv]
  apply mul_ne_zero (inv_ne_zero hc)
  intro hz
  have hr := congrArg Complex.re hz
  norm_num  at hr

@[simp] theorem riemannMappingGraphBoundaryCurve_zero (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : f 0 = 0) :
    riemannMappingGraphBoundaryCurve p c hc f hf 0 = p := by
  simp [riemannMappingGraphBoundaryCurve, smoothDirichletGraphShear, hf₀]

section ActualInverseGraph

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)

include hb hS hsc hF hinj himage

variable {θ : ℝ} {p c : ℂ} (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)

/-- This interface uses the actual closed inverse and genuine bottom frontier.
The inverse graph smoothness and nonstationarity can be supplied by the Green
boundary-field and barrier theorems. -/
theorem riemannMapping_circleTrace_contDiffAt_of_inverse_graph
    (hf₀ : f 0 = 0)
    (hp : p = riemannMappingClosedExtension F (circleMap 0 1 θ))
    (hfront : ∀ᶠ x : ℝ in 𝓝 0,
      riemannMappingGraphBoundaryCurve p c hc f hf.continuous x ∈ frontier Ω)
    (hα : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x  => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0)
    (hdα : deriv (fun x  => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := physicalCircleTrace_contDiffAt_of_inverse_curve hα (hfront.mono fun _ hx =>
      riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hx) hdα (by
    rw [riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀, hp]
    exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage
      (circleMap_mem_closedBall 0 zero_le_one θ))
    (riemannMappingGraphBoundaryCurve_contDiff p c hc hf).contDiffAt
    (riemannMappingGraphBoundaryCurve_deriv_ne_zero p c hc hf 0) (hfront.mono fun _ hx =>
      (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage
        (frontier_subset_closure hx)).2)

/-- A genuine full-box membership chart supplies the bottom frontier premise;
mere mapping of the open upper half box is not used for that implication. -/
theorem riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
    (hf₀ : f 0 = 0)
    (hp : p = riemannMappingClosedExtension F (circleMap 0 1 θ))
    {a b : ℝ} (ha : 0 < a) (hb₀ : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
    (hα : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x  => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0)
    (hdα : deriv (fun x  => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  apply riemannMapping_circleTrace_contDiffAt_of_inverse_graph hb hS hsc F hF hinj himage
    hc hf hf₀ hp _ hα hdα
  have hI : ∀ᶠ x : ℝ in 𝓝 0, x ∈ Ioo (-a) a :=
    Ioo_mem_nhds (by linarith) ha
  exact hI.mono fun x hx =>
    smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous
      hb₀ hchart (abs_lt.mpr hx)

/-- All genuine inverse graph packets yield global smoothness and
nonstationarity of the actual angular trace of the closed extension. -/
theorem riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs
    (hgraphs : ∀ p ∈ frontier Ω,
      ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ),
        f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
        (∀ z : ℂ, |z.re| < a → |z.im| < b →
          (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x  => riemannMappingClosedInverse F
            (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
        deriv (fun x  => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) ∧
      ∀ θ : ℝ, deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  have hall (θ : ℝ) :
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
    let p := riemannMappingClosedExtension F (circleMap 0 1 θ)
    obtain ⟨c, hc, f, hf, a, b, hf₀, ha, hb₀, hchart, hα, hdα⟩ := hgraphs p (riemannMappingClosedExtension_mem_frontier hb hS.isLipschitzDomain hsc F hF hinj himage
        (by simp ))
    exact riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
      hb hS hsc F hF hinj himage hc hf hf₀ rfl ha hb₀ hchart hα hdα
  exact ⟨contDiff_iff_contDiffAt.mpr fun θ => (hall θ).1, fun θ => (hall θ).2⟩

end ActualInverseGraph

variable {Ω : Set ℂ}

/-- A small actual closed rectangle avoids a point avoided at its center. -/
theorem exists_riemannMapping_halfBox_avoiding {Ψ : ℂ → ℂ} {w : ℂ}
    (hΨ : ContinuousAt Ψ 0) (hne : Ψ 0 ≠ w) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∀ z ∈ smoothDirichletClosedHalfBox r r, Ψ z ≠ w := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΨ.eventually (eventually_ne_nhds hne))
  let r := min ρ (ε / 4)
  have hrε : r ≤ ε / 4 := min_le_right _ _
  refine ⟨r, lt_min hρ (by positivity), min_le_left _ _, ?_⟩
  intro z hz
  apply hball
  rw [mem_ball_zero_iff]
  have hzI : |z.im| ≤ r := by rw [abs_of_nonneg hz.2.1]; exact hz.2.2
  have hzN : ‖z‖ ≤ 2 * r := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * r := by linarith [hz.1]
  linarith

/-- The genuine original-domain gradient fields are transferred to Green
by its actual pole-subtracted datum.  The whole chosen closed rectangle
avoids the original pole; no boundary derivative of Green is assumed. -/
theorem exists_riemannMapping_genuine_green_smooth_boundary_fields (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (r : ℝ) (P Q : ℂ → ℂ),
      f 0 = 0 ∧ 0 < r ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let G := riemannMappingFlattenedGreen F Ψ
       let U := smoothDirichletHalfBox r r
       let V := smoothDirichletClosedHalfBox r r
       (∀ z : ℂ, |z.re| < r → |z.im| < r → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ U Ω ∧ (∀ z ∈ V, Ψ z ≠ F 0) ∧
       ContinuousOn (riemannMappingClosedInverse F ∘ Ψ) V ∧
       ContinuousOn G V ∧ ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
       ContinuousOn P V ∧ ContinuousOn Q V ∧
       EqOn P (dirD G 1) U ∧ EqOn Q (dirD G Complex.I) U ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => P x) 0 ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Q x) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hchart, hclosed, hmap, huc, hus, huz,
    hXc, hYc, hXu, hYu, hXsmooth, hYsmooth⟩ :=
    exists_riemannMapping_genuine_gradient_smooth_boundary_fields
      hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let L := riemannMappingGreenLogDatum F d Ψ
  have hΨ₀ : Ψ 0 = p := by
    simpa only [riemannMappingGraphBoundaryCurve, Complex.ofReal_zero] using
      riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀
  obtain ⟨r, hr, hrρ, hne⟩ := exists_riemannMapping_halfBox_avoiding
    Ψ.continuous.continuousAt (by rw [hΨ₀]; exact (by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    exact hp.2 (riemannMapping_pole_mem F himage))) hρ
  let U := smoothDirichletHalfBox r r
  let V := smoothDirichletClosedHalfBox r r
  have hrA : r < A := hrρ.trans_lt (hρA.trans (by linarith))
  have hrb  := hrρ.trans_lt hρb
  have hUρ : U ⊆ smoothDirichletHalfBox ρ ρ := by
    intro z hz
    exact ⟨hz.1.trans_le hrρ, hz.2.1, hz.2.2.trans_le hrρ⟩
  have hVρ : V ⊆ smoothDirichletClosedHalfBox ρ ρ := by
    intro z hz
    exact ⟨hz.1.trans hrρ, hz.2.1, hz.2.2.trans hrρ⟩
  have hUA : U ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans hrA, hz.2.1, hz.2.2.trans hrb⟩
  have hVA : V ⊆ smoothDirichletClosedHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans hrA.le, hz.2.1, hz.2.2.trans hrb.le⟩
  have hUV : U ⊆ V := by
    intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hclosed' : MapsTo Ψ V (closure Ω) := fun z hz => hclosed (hVA hz)
  have hmap' : MapsTo Ψ U Ω := fun z hz => hmap (hUA hz)
  have hLs (z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) L z :=
    riemannMappingGreenLogDatum_contDiffAt F d (smoothDirichletGraphChart_contDiff p c hc hf).contDiffAt (hne z hz)
  have hDs (w : ℂ) (z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) (dirD L w) z :=
    contDiffAt_infty_dirD (hLs z hz) w
  have hDc (w : ℂ) : ContinuousOn (dirD L w) V :=
    fun z hz => (hDs w z hz).continuousAt.continuousWithinAt
  have hLsmooth (w : ℂ) : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => dirD L w x) 0 :=
    (hDs w 0 (by
    change |(0 : ℂ).re| ≤ r ∧ 0 ≤ (0 : ℂ).im ∧ (0 : ℂ).im ≤ r
    simpa only [Complex.zero_re, abs_zero] using
      (⟨hr.le, le_rfl, hr.le⟩))).comp (f := fun x : ℝ => (x : ℂ))  0
      Complex.ofRealCLM.contDiff.contDiffAt
  let P  := fun z => X z + dirD L 1 z
  let Q  := fun z => Y z + dirD L Complex.I z
  let G := riemannMappingFlattenedGreen F Ψ
  have hsum : EqOn G (fun z => u z + L z) V := by
    intro z hz
    exact riemannMappingFlattenedGreen_eq_remainder_add_datum
      hb hS hsc F hF hinj himage d Ψ (hclosed' hz) (hne z hz)
  have hus'  := hus.mono hUA
  have hU  := isOpen_smoothDirichletHalfBox r r
  have hd (w : ℂ) : EqOn (dirD G w)
      (fun z => dirD u w z + dirD L w z) U := by
    intro z hz
    rw [dirichlet_bootstrap_dirD_eqOn hU (hsum.mono hUV) w hz]
    exact dirichlet_normal_dirD_add
      ((hus'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hLs z (hUV hz)).differentiableAt (by simp)) w
  refine ⟨c, hc, f, hf, r, P, Q, hf₀, hr, ?_, hmap', hne,
    (riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).comp
      Ψ.continuous.continuousOn hclosed',
    ((huc.mono hVA).add fun z hz => (hLs z hz).continuousAt.continuousWithinAt).congr hsum, (hus'.add fun z hz => (hLs z (hUV hz)).contDiffWithinAt).congr (hsum.mono hUV), (hXc.mono hVρ).add (hDc 1),
    (hYc.mono hVρ).add (hDc Complex.I), by
    intro z hz
    grind, by
    intro z hz
    grind, hXsmooth.add (hLsmooth 1),
    hYsmooth.add (hLsmooth Complex.I)⟩
  grind

/-- Genuine inverse graph regularity follows from the original physical
domain, its actual Green function and the proved finite-order boundary fields. -/
theorem exists_riemannMapping_genuine_regular_inverse_graph (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ),
      f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x  => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
      deriv (fun x  => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0 := by
  obtain ⟨c, hc, f, hf, r, P, Q, hf₀, hr, hchart, hmap, hne,
    hJ, hGc, hGs, hPc, hQc, hP, hQ, hPsmooth, hQsmooth⟩ :=
    exists_riemannMapping_genuine_green_smooth_boundary_fields hb hS hsc F hF hinj himage hp
  have hpole : ∀ z ∈ smoothDirichletHalfBox r r,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0 := by
    intro z hz
    exact hne z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  exact ⟨c, hc, f, hf, r, r, hf₀, hr, hr, hchart, riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    hb hS hsc F hF hinj himage p c hc hf hr hr hmap hpole hJ hPc hQc hP hQ hPsmooth hQsmooth, riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    hb hS hsc F hF hinj himage p c hc hf hf₀ hp hr hr hchart hmap hpole
      hJ hGc hGs hPc hQc hP hQ⟩

end PolyaNeumann

end
