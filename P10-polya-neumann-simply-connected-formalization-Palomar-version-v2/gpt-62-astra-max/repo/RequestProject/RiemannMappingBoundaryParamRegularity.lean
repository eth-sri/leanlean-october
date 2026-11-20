module

public import RequestProject.RiemannMappingBoundaryDerivative
public import RequestProject.LocalDirichletGenuineChart
public import RequestProject.PhysicalHardySupport
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open Set Metric Filter Complex
open scoped Topology

/-- The actual local angular coordinate of a normalized circle-valued curve. -/
def riemannMappingBoundaryPhase (α : ℝ → ℂ) (t₀ t : ℝ) : ℝ :=
  (Complex.log (α t / α t₀)).im

theorem riemannMappingBoundaryPhase_zero {α : ℝ → ℂ} {t₀ : ℝ}
    (h₀ : α t₀ ≠ 0) : riemannMappingBoundaryPhase α t₀ t₀ = 0 := by
  simp [riemannMappingBoundaryPhase]

/-- The principal logarithm is only used in a neighborhood of the value one. -/
theorem riemannMappingBoundaryPhase_contDiffAt {α : ℝ → ℂ} {t₀ : ℝ}
    (hα : ContDiffAt ℝ ∞ α t₀) (h₀ : α t₀ ≠ 0) :
    ContDiffAt ℝ ∞ (riemannMappingBoundaryPhase α t₀) t₀ := by
  
  have hslit : α t₀ / α t₀ ∈ Complex.slitPlane := by simp [h₀]
  
  have hlog  :=
    ((Complex.contDiffAt_log hslit).restrict_scalars ℝ).comp   t₀ (hα.div_const _)
  exact Complex.imCLM.contDiff.contDiffAt.comp t₀ hlog

/-- A unit-modulus value is exactly recovered from its normalized phase. -/
theorem riemannMappingBoundaryPhase_circle {α : ℝ → ℂ} {t₀ t : ℝ}
    (h₀ : ‖α t₀‖ = 1) (ht : ‖α t‖ = 1) :
    α t = α t₀ * unitCirclePt (riemannMappingBoundaryPhase α t₀ t) := by
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simp [h] at h₀
  have hratio : ‖α t / α t₀‖ = 1 := by simp [ht, h₀]
  
  have hre : (Complex.log (α t / α t₀)).re = 0 := by
    rw [Complex.log_re, hratio, Real.log_one]
  have hlog : Complex.log (α t / α t₀) =
      (riemannMappingBoundaryPhase α t₀ t : ℂ) * Complex.I := by
    simpa only [riemannMappingBoundaryPhase, hre, Complex.ofReal_zero, zero_add]
      using (Complex.re_add_im (Complex.log (α t / α t₀))).symm
  have hexp : unitCirclePt (riemannMappingBoundaryPhase α t₀ t) = α t / α t₀ := by
    simp [circleMap_zero]
    rw [← hlog]
    exact Complex.exp_log (by
        intro h
        simp [h] at hratio)
  rw [hexp]
  field_simp [hn₀]

theorem riemannMappingBoundaryPhase_circle_eventually {α : ℝ → ℂ} {t₀ : ℝ}
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) :
    ∀ᶠ t in 𝓝 t₀,
      α t = α t₀ * unitCirclePt (riemannMappingBoundaryPhase α t₀ t) :=
  hcircle.mono fun _ ht => riemannMappingBoundaryPhase_circle hcircle.self_of_nhds ht

/-- Nonstationarity of the circle curve forces a nonzero real phase derivative. -/
theorem riemannMappingBoundaryPhase_deriv_ne_zero {α : ℝ → ℂ} {t₀ : ℝ}
    (hα : ContDiffAt ℝ ∞ α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0) :
    deriv (riemannMappingBoundaryPhase α t₀) t₀ ≠ 0 := by
  
  
  
  have ha  :=
    (((hasDerivAt_circleMap 0 1 _).scomp t₀ (((riemannMappingBoundaryPhase_contDiffAt hα (by
      intro h
      simpa [h] using hcircle.self_of_nhds)).differentiableAt (by simp)).hasDerivAt)).const_mul (α t₀)).congr_of_eventuallyEq
      (riemannMappingBoundaryPhase_circle_eventually hcircle)
  intro hz
  apply hd
  simp [ha.deriv, hz]

/-- A smooth inverse circle curve supplies the genuine local angular inverse.
The output is an actual function obtained from the real inverse function theorem. -/
theorem exists_riemannMappingBoundaryAngularInverse {α : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ ∞ α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = unitCirclePt θ₀) :
    ∃ g : ℝ → ℝ, g θ₀ = t₀ ∧ ContDiffAt ℝ ∞ g θ₀ ∧
      HasDerivAt g (deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ θ₀ ∧
      ∀ᶠ θ in 𝓝 θ₀, α (g θ) = unitCirclePt θ := by
  let φ := riemannMappingBoundaryPhase α t₀
  have hn₀ : α t₀ ≠ 0 := by
    simp [*]
  have hφ : ContDiffAt ℝ ∞ φ t₀ :=
    riemannMappingBoundaryPhase_contDiffAt hα hn₀
  have hc  := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hd
  have hdφ  :=
    (hφ.differentiableAt (by simp)).hasDerivAt
  have hfd := hdφ.hasFDerivAt_equiv hc
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e := hφ.toOpenPartialHomeomorph φ hfd hn
  have he : e = φ := rfl
  have hs  := hφ.mem_toOpenPartialHomeomorph_source hfd hn
  have hφ₀ : φ t₀ = 0 := riemannMappingBoundaryPhase_zero hn₀
  have ht := hφ.image_mem_toOpenPartialHomeomorph_target hfd hn
  simp only [hφ₀] at ht
  have he₀ := e.left_inv hs
  simp only [he, hφ₀] at he₀
  have hid : HasDerivAt e (deriv φ t₀) (e.symm 0) := by
    simpa only [he₀, he] using hdφ
  have hi : ContDiffAt ℝ ∞ e.symm 0 := by
    apply e.contDiffAt_symm_deriv hc ht hid
    simpa [he₀, he] using hφ
  have hdi  :=
    e.hasDerivAt_symm ht hc hid
  let g  := fun θ => e.symm (θ - θ₀)
  have hg₀ : g θ₀ = t₀ := by simp [g, he₀]
  have hgs : ContDiffAt ℝ ∞ g θ₀ := by
    have hi' : ContDiffAt ℝ ∞ (e.symm : ℝ → ℝ) (θ₀ - θ₀) := by
      simpa only [sub_self] using hi
    fun_prop
  
  have hshift : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 0) := by
    have ht : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 (θ₀ - θ₀)) :=
      (continuousAt_id.sub continuousAt_const :
        ContinuousAt (fun θ : ℝ => θ - θ₀) θ₀).tendsto
    simpa using ht
  have hright : ∀ᶠ θ in 𝓝 θ₀, φ (g θ) = θ - θ₀ := by
    simpa only [g, he] using
      hshift.eventually (e.eventually_right_inverse ht)
  have hgt := hgs.continuousAt.tendsto
  simp only [hg₀] at hgt
  
  refine ⟨g, hg₀, hgs, (by
      simpa only [g, one_mul, mul_one, Function.comp_def, id] using
        hdi.comp_of_eq θ₀ ((hasDerivAt_id θ₀).sub_const θ₀) (by simp)), ?_⟩
  filter_upwards [hright, (hgt.eventually (riemannMappingBoundaryPhase_circle_eventually hcircle))] with θ hθ hrec
  change _ = α t₀ * unitCirclePt (φ (g θ)) at hrec
  rw [hrec, hcenter, hθ, circleMap_zero_mul]
  ring

/-- Genuine inverse parametrization regularizes the actual forward circle trace.
Only the inverse curve and the physical graph curve have regularity premises. -/
theorem physicalCircleTrace_contDiffAt_of_inverse_curve {F : ℂ → ℂ}
    {α β : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ ∞ α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hdα : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = unitCirclePt θ₀)
    (hβ : ContDiffAt ℝ ∞ β t₀) (hdβ : deriv β t₀ ≠ 0)
    (hforward : ∀ᶠ t in 𝓝 t₀, F (α t) = β t) :
    ContDiffAt ℝ ∞ (physicalCircleTrace F) θ₀ ∧
      deriv (physicalCircleTrace F) θ₀ ≠ 0 := by
  obtain ⟨g, hg₀, hgs, hgd, hcircleG⟩ :=
    exists_riemannMappingBoundaryAngularInverse hα hcircle hdα hcenter
  have hc := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hdα
  have hgt := hgs.continuousAt.tendsto
  simp only [hg₀] at hgt
  have heq : physicalCircleTrace F =ᶠ[𝓝 θ₀] β ∘ g := by
    filter_upwards [hcircleG, hgt.eventually hforward] with θ hcircleθ hforwardθ
    simpa [physicalCircleTrace, hcircleθ] using hforwardθ
  have hβg : ContDiffAt ℝ ∞ (β ∘ g) θ₀ := by
    have hβ' : ContDiffAt ℝ ∞ β (g θ₀) := by simp [*]
    exact hβ'.comp θ₀ hgs
  have hdβg : HasDerivAt (β ∘ g)
      ((deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ • deriv β t₀) θ₀ := by
    apply ((hβ.differentiableAt (by simp)).hasDerivAt).scomp_of_eq θ₀ hgd hg₀.symm
  refine ⟨hβg.congr_of_eventuallyEq heq, ?_⟩
  rw [(hdβg.congr_of_eventuallyEq heq).deriv]
  simp [*]

section

variable (p c : ℂ) (hc : c ≠ 0)
include hc p

/-- The actual physical graph, restricted to its bottom horizontal line. -/
def riemannMappingGraphBoundaryCurve
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) : ℂ :=
  smoothDirichletGraphChart p c hc f hf (x : ℂ)

theorem riemannMappingGraphBoundaryCurve_contDiff
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) :=
  (smoothDirichletGraphChart_contDiff p c hc hf).comp Complex.ofRealCLM.contDiff

theorem riemannMappingGraphBoundaryCurve_hasDerivAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt (riemannMappingGraphBoundaryCurve p c hc f hf.continuous)
      (c⁻¹ * (1 + ((deriv f x : ℝ) : ℂ) * Complex.I)) x := by
  
  unfold riemannMappingGraphBoundaryCurve
  simpa only [Function.comp_def,
    Complex.ofRealCLM_apply, ContinuousLinearMap.smul_apply,
    smoothDirichletGraphDifferential_apply, Complex.ofReal_re,
    Complex.ofReal_one, Complex.one_re, mul_one, Complex.real_smul, smul_eq_mul] using (smoothDirichletGraphChart_hasFDerivAt p c hc hf x).comp_hasDerivAt
      x (Complex.ofRealCLM.hasDerivAt (x := x))

theorem riemannMappingGraphBoundaryCurve_deriv_ne_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    deriv (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) x ≠ 0 := by
  rw [(riemannMappingGraphBoundaryCurve_hasDerivAt p c hc hf x).deriv]
  apply mul_ne_zero (inv_ne_zero hc)
  intro hz
  have hr := congrArg Complex.re hz
  norm_num [Complex.mul_re] at hr

@[simp] theorem riemannMappingGraphBoundaryCurve_zero
    {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : f 0 = 0) :
    riemannMappingGraphBoundaryCurve p c hc f hf 0 = p := by
  simp [riemannMappingGraphBoundaryCurve, smoothDirichletGraphShear, hf₀]

end

section ActualInverseGraph

variable {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)

include hΦ

/-- This interface uses the actual closed inverse and genuine bottom frontier.
The inverse graph smoothness and nonstationarity can be supplied by the Green
boundary-field and barrier theorems. -/
theorem riemannMapping_circleTrace_contDiffAt_of_inverse_graph
    {θ : ℝ} {p c : ℂ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf₀ : f 0 = 0)
    (hp : p = riemannMappingClosedExtension F (unitCirclePt θ))
    (hfront : ∀ᶠ x : ℝ in 𝓝 0,
      riemannMappingGraphBoundaryCurve p c hc f hf.continuous x ∈ frontier Ω)
    (hα : ContDiffAt ℝ ∞
      (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0)
    (hdα : deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiffAt ℝ ∞ (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  let β := riemannMappingGraphBoundaryCurve p c hc f hf.continuous
  let α  := fun x => riemannMappingClosedInverse F (β x)
  have hcircle  :=
    hfront.mono fun _ hx =>
      riemannMappingClosedInverse_norm_frontier hΦ hx
  have hcenter : α 0 = unitCirclePt θ := by
    change riemannMappingClosedInverse F
      (riemannMappingGraphBoundaryCurve p c hc f hf.continuous 0) = _
    rw [riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀, hp]
    exact riemannMappingClosedInverse_left hΦ
      (circleMap_mem_closedBall 0 zero_le_one θ)
  have hforward  :=
    hfront.mono fun _ hx =>
      (riemannMappingClosedInverse_mem_right hΦ
        (frontier_subset_closure hx)).2
  exact physicalCircleTrace_contDiffAt_of_inverse_curve hα hcircle hdα hcenter
    (riemannMappingGraphBoundaryCurve_contDiff p c hc hf).contDiffAt
    (riemannMappingGraphBoundaryCurve_deriv_ne_zero p c hc hf 0) hforward

/-- A genuine full-box membership chart supplies the bottom frontier premise;
mere mapping of the open upper half box is not used for that implication. -/
theorem riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
    {θ : ℝ} {p c : ℂ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf₀ : f 0 = 0)
    (hp : p = riemannMappingClosedExtension F (unitCirclePt θ))
    {a b : ℝ} (ha : 0 < a) (hb₀ : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
    (hα : ContDiffAt ℝ ∞
      (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0)
    (hdα : deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiffAt ℝ ∞ (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  apply riemannMapping_circleTrace_contDiffAt_of_inverse_graph hΦ
    hc hf hf₀ hp _ hα hdα
  have hI : ∀ᶠ x : ℝ in 𝓝 0, x ∈ Ioo (-a) a :=
    Ioo_mem_nhds (by linarith) ha
  exact hI.mono fun x hx =>
    smoothDirichletGraphChart_mem_frontier hΦ.smooth.1.1 p c hc f hf.continuous
      hb₀ hchart (abs_lt.mpr hx)

/-- All genuine inverse graph packets yield global smoothness and
nonstationarity of the actual angular trace of the closed extension. -/
theorem riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs
    (hgraphs : ∀ p ∈ frontier Ω,
      ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a b : ℝ),
        f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
        (∀ z : ℂ, |z.re| < a → |z.im| < b →
          (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
        ContDiffAt ℝ ∞
          (fun x : ℝ => riemannMappingClosedInverse F
            (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
        deriv (fun x : ℝ => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiff ℝ ∞ (physicalCircleTrace (riemannMappingClosedExtension F)) ∧
      ∀ θ : ℝ, deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  have hall (θ : ℝ) :
      ContDiffAt ℝ ∞ (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
    let p := riemannMappingClosedExtension F (unitCirclePt θ)
    have hp : p ∈ frontier Ω :=
      riemannMappingClosedExtension_mem_frontier hΦ.toLipschitz
        (by simp)
    obtain ⟨c, hc, f, hf, a, b, hf₀, ha, hb₀, hchart, hα, hdα⟩ := hgraphs p hp
    exact riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
      hΦ hc hf hf₀ rfl ha hb₀ hchart hα hdα
  exact ⟨contDiff_iff_contDiffAt.mpr fun θ => (hall θ).1, fun θ => (hall θ).2⟩

end ActualInverseGraph

/-- A small actual closed rectangle avoids a point avoided at its center. -/
theorem exists_riemannMapping_halfBox_avoiding {Ψ : ℂ → ℂ} {w : ℂ}
    (hΨ : ContinuousAt Ψ 0) (hne : Ψ 0 ≠ w) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∀ z ∈ smoothDirichletClosedHalfBox r r, Ψ z ≠ w := by
  
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΨ.eventually (eventually_ne_nhds hne))
  let r := min ρ (ε / 4)
  
  have hrε : r ≤ ε / 4 := min_le_right _ _
  refine ⟨r, (lt_min hρ (by positivity)), min_le_left _ _, ?_⟩
  intro z hz
  apply hball
  rw [mem_ball_zero_iff]
  have hzI : |z.im| ≤ r := by rw [abs_of_nonneg hz.2.1]; exact hz.2.2
  have hzN : ‖z‖ ≤ 2 * r := by
    calc
      _ ≤ _ := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ _ := by linarith [hz.1]
  linarith

/-- The genuine original-domain gradient fields are transferred to Green
by its actual pole-subtracted datum.  The whole chosen closed rectangle
avoids the original pole; no boundary derivative of Green is assumed. -/
theorem exists_riemannMapping_genuine_green_smooth_boundary_fields {Ω : Set ℂ}
    {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (r : ℝ) (P Q : ℂ → ℂ),
      f 0 = 0 ∧ 0 < r ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let G := riemannMappingFlattenedGreen F Ψ
       let U := smoothDirichletHalfBox r r
       let V := smoothDirichletClosedHalfBox r r
       (∀ z : ℂ, |z.re| < r → |z.im| < r → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ U Ω ∧ (∀ z ∈ V, Ψ z ≠ F 0) ∧
       ContinuousOn (riemannMappingClosedInverse F ∘ Ψ) V ∧
       ContinuousOn G V ∧ ContDiffOn ℝ ∞ G U ∧
       ContinuousOn P V ∧ ContinuousOn Q V ∧
       EqOn P (dirD G 1) U ∧ EqOn Q (dirD G Complex.I) U ∧
       ContDiffAt ℝ ∞ (fun x : ℝ => P (x : ℂ)) 0 ∧
       ContDiffAt ℝ ∞ (fun x : ℝ => Q (x : ℂ)) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hchart, hclosed, hmap, huc, hus, huz,
    hXc, hYc, hXu, hYu, hXsmooth, hYsmooth⟩ :=
    exists_riemannMapping_genuine_gradient_smooth_boundary_fields
      hΦ hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let L := riemannMappingGreenLogDatum F d Ψ
  have hΨ  :=
    smoothDirichletGraphChart_contDiff p c hc hf
  have hΨ₀ : Ψ 0 = p := by
    simpa only [riemannMappingGraphBoundaryCurve, Complex.ofReal_zero] using
      riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hΦ.smooth.1.1.frontier_eq] at hp
    exact hp.2 (hΦ.pole_mem)
  obtain ⟨r, hr, hrρ, hne⟩ := exists_riemannMapping_halfBox_avoiding
    Ψ.continuous.continuousAt (by rw [hΨ₀]; exact hpne) hρ
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
  have hLs (z : ℂ) (hz : z ∈ V)  :=
    riemannMappingGreenLogDatum_contDiffAt F d hΨ.contDiffAt (hne z hz)
  have hLc : ContinuousOn L V := fun z hz => (hLs z hz).continuousAt.continuousWithinAt
  have hDs (w z : ℂ) (hz : z ∈ V)  :=
    contDiffAt_infty_dirD (hLs z hz) w
  have hDc (w : ℂ) : ContinuousOn (dirD L w) V :=
    fun z hz => (hDs w z hz).continuousAt.continuousWithinAt
  have hV₀ : (0 : ℂ) ∈ V := by
    change |(0 : ℂ).re| ≤ r ∧ 0 ≤ (0 : ℂ).im ∧ (0 : ℂ).im ≤ r
    simpa using (show (0 : ℝ) ≤ r ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ r from ⟨hr.le, le_rfl, hr.le⟩)
  have hLsmooth (w : ℂ)  :=
    (hDs w 0 hV₀).comp (f := fun x : ℝ => (x : ℂ))  0
      Complex.ofRealCLM.contDiff.contDiffAt
  let P  := fun z => X z + dirD L 1 z
  let Q  := fun z => Y z + dirD L Complex.I z
  let G := riemannMappingFlattenedGreen F Ψ
  have hsum : EqOn G (fun z => u z + L z) V := by
    intro z hz
    exact riemannMappingFlattenedGreen_eq_remainder_add_datum
      hΦ d Ψ (hclosed' hz) (hne z hz)
  have hGc  := ((huc.mono hVA).add hLc).congr hsum
  have hus'  := hus.mono hUA
  have hLs' : ContDiffOn ℝ ∞ L U :=
    fun z hz => (hLs z (hUV hz)).contDiffWithinAt
  have hGs  :=
    (hus'.add hLs').congr (hsum.mono hUV)
  have hU  := isOpen_smoothDirichletHalfBox r r
  have hd (w : ℂ) : EqOn (dirD G w)
      (fun z => dirD u w z + dirD L w z) U := by
    intro z hz
    rw [dirichlet_bootstrap_dirD_eqOn hU (hsum.mono hUV) w hz]
    exact dirichlet_normal_dirD_add
      ((hus'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hLs z (hUV hz)).differentiableAt (by simp)) w
  have hP : EqOn P (dirD G 1) U := by
    intro z hz
    rw [hd 1 hz]
    change X z + dirD L 1 z = _
    rw [hXu (hUρ hz)]
  have hQ : EqOn Q (dirD G Complex.I) U := by
    intro z hz
    rw [hd Complex.I hz]
    change Y z + dirD L Complex.I z = _
    rw [hYu (hUρ hz)]
  refine ⟨c, hc, f, hf, r, P, Q, hf₀, hr, ?_, hmap', hne,
    (riemannMappingClosedInverse_continuousOn hΦ).comp
      Ψ.continuous.continuousOn hclosed',
    hGc, hGs, (hXc.mono hVρ).add (hDc 1),
    (hYc.mono hVρ).add (hDc Complex.I), hP, hQ, hXsmooth.add (hLsmooth 1),
    hYsmooth.add (hLsmooth Complex.I)⟩
  intro z hzre hzim
  exact hchart z (hzre.trans hrA) (hzim.trans hrb)

/-- Genuine inverse graph regularity follows from the original physical
domain, its actual Green function and the proved finite-order boundary fields. -/
theorem exists_riemannMapping_genuine_regular_inverse_graph {Ω : Set ℂ}
    {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a b : ℝ),
      f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
      ContDiffAt ℝ ∞
        (fun x : ℝ => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
      deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0 := by
  obtain ⟨c, hc, f, hf, r, P, Q, hf₀, hr, hchart, hmap, hne,
    hJ, hGc, hGs, hPc, hQc, hP, hQ, hPsmooth, hQsmooth⟩ :=
    exists_riemannMapping_genuine_green_smooth_boundary_fields hΦ hp
  have hpole : ∀ z ∈ smoothDirichletHalfBox r r,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0 := by
    intro z hz
    exact hne z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hα := riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    hΦ p c hc hf hr hr hmap hpole hJ hPc hQc hP hQ hPsmooth hQsmooth
  have hdα := riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    hΦ p c hc hf hf₀ hp hr hr hchart hmap hpole
      hJ hGc hGs hPc hQc hP hQ
  exact ⟨c, hc, f, hf, r, r, hf₀, hr, hr, hchart, hα, hdα⟩

end PolyaNeumann

end
