module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex
open scoped Topology

/-- The actual local angular coordinate of a normalized circle-valued curve. -/
def riemannMappingBoundaryPhase (α : ComplexCurve) t₀ t  :=
  (Complex.log (α t / α t₀)).im

section
variable {α : ComplexCurve}
include α

theorem riemannMappingBoundaryPhase_zero 
    : riemannMappingBoundaryPhase α t₀ t₀ = 0 := by
  simp [riemannMappingBoundaryPhase]

/-- The principal logarithm is only used in a neighborhood of the value one. -/
theorem riemannMappingBoundaryPhase_contDiffAt 
    (hα : RealSmoothAt α t₀) (h₀ : α t₀ ≠ 0) :
    RealSmoothAt (riemannMappingBoundaryPhase α t₀) t₀ := by
  have hratio : RealSmoothAt (fun t => α t / α t₀) t₀ :=
    hα.div_const _
  have hslit : α t₀ / α t₀ ∈ Complex.slitPlane := by simp [h₀]
  have hlogOuter : RealSmoothAt Complex.log (α t₀ / α t₀) :=
    (Complex.contDiffAt_log hslit).restrict_scalars ℝ
  have hlog  :=
    hlogOuter.comp (f := fun t : ℝ => α t / α t₀) (g := Complex.log) t₀ hratio
  exact Complex.imCLM.contDiff.contDiffAt.comp t₀ hlog

/-- A unit-modulus value is exactly recovered from its normalized phase. -/
theorem riemannMappingBoundaryPhase_circle 
    (h₀ : ‖α t₀‖ = 1) (ht : ‖α t‖ = 1) :
    α t = α t₀ * unitCircleMap (riemannMappingBoundaryPhase α t₀ t) := by
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simp [h] at h₀
  have hratio : ‖α t / α t₀‖ = 1 := by rw [norm_div, ht, h₀]; norm_num
  have hn : α t / α t₀ ≠ 0 := by
    intro h
    simp [h] at hratio
  have hre : (Complex.log (α t / α t₀)).re = 0 := by
    rw [Complex.log_re, hratio, Real.log_one]
  have hlog : Complex.log (α t / α t₀) =
      (riemannMappingBoundaryPhase α t₀ t : ℂ) * Complex.I := by
    simpa  [riemannMappingBoundaryPhase, hre]
      using (Complex.re_add_im (Complex.log (α t / α t₀))).symm
  have hexp : unitCircleMap (riemannMappingBoundaryPhase α t₀ t) = α t / α t₀ := by
    simp  [circleMap_zero, one_mul]
    rw [← hlog]
    exact Complex.exp_log hn
  rw [hexp]
  field_simp [hn₀]

theorem riemannMappingBoundaryPhase_circle_eventually 
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) :
    ∀ᶠ t in 𝓝 t₀,
      α t = α t₀ * unitCircleMap (riemannMappingBoundaryPhase α t₀ t) :=
  hcircle.mono fun _ ht => riemannMappingBoundaryPhase_circle hcircle.self_of_nhds ht

/-- Nonstationarity of the circle curve forces a nonzero real phase derivative. -/
theorem riemannMappingBoundaryPhase_deriv_ne_zero 
    (hα : RealSmoothAt α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0) :
    deriv (riemannMappingBoundaryPhase α t₀) t₀ ≠ 0 := by
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simpa [h] using hcircle.self_of_nhds
  have hphase := riemannMappingBoundaryPhase_contDiffAt hα hn₀
  have hp := (hphase.differentiableAt (by simp)).hasDerivAt
  have ha  :=
    (((hasDerivAt_circleMap 0 1 _).scomp t₀ hp).const_mul (α t₀)).congr_of_eventuallyEq
      (riemannMappingBoundaryPhase_circle_eventually hcircle)
  intro hz
  apply hd
  rw [ha.deriv, hz, zero_smul, mul_zero]

/-- A smooth inverse circle curve supplies the genuine local angular inverse.
The output is an actual function obtained from the real inverse function theorem. -/
theorem exists_riemannMappingBoundaryAngularInverse 
    (hα : RealSmoothAt α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = unitCircleMap θ₀) :
    ∃ g : RealMap, g θ₀ = t₀ ∧ RealSmoothAt g θ₀ ∧
      HasDerivAt g (deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ θ₀ ∧
      ∀ᶠ θ in 𝓝 θ₀, α (g θ) = unitCircleMap θ := by
  let φ := riemannMappingBoundaryPhase α t₀
  have hn₀ : α t₀ ≠ 0 := by
    simp_all
  have hφ : RealSmoothAt φ t₀ :=
    riemannMappingBoundaryPhase_contDiffAt hα hn₀
  have hc  := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hd
  have hdφ  :=
    (hφ.differentiableAt (by simp)).hasDerivAt
  have hfd := hdφ.hasFDerivAt_equiv hc
  have hn : ∞ ≠ 0 := by simp
  let e := hφ.toOpenPartialHomeomorph φ hfd hn
  have he : (e : RealMap) = φ := rfl
  have hs  := hφ.mem_toOpenPartialHomeomorph_source hfd hn
  have hφ₀ : φ t₀ = 0 := riemannMappingBoundaryPhase_zero
  have ht : (0 : ℝ) ∈ e.target := by
    simpa  [hφ₀] using hφ.image_mem_toOpenPartialHomeomorph_target hfd hn
  have he₀ : e.symm 0 = t₀ := by
    simpa  [he, hφ₀] using e.left_inv hs
  have hid : HasDerivAt (e : RealMap) (deriv φ t₀) (e.symm 0) := by
    simpa  [he₀, he] using hdφ
  have hi : RealSmoothAt (e.symm : RealMap) 0 := by
    apply e.contDiffAt_symm_deriv hc ht hid
    simpa only [he₀, he] using hφ
  have hdi  :=
    e.hasDerivAt_symm ht hc hid
  let g  := fun θ => e.symm (θ - θ₀)
  have hg₀ : g θ₀ = t₀ := by simp only [g, sub_self, he₀]
  have hgs : RealSmoothAt g θ₀ := by
    have hi' : RealSmoothAt (e.symm : RealMap) (θ₀ - θ₀) := by
      simpa only [sub_self] using hi
    fun_prop
  have hgd : HasDerivAt g (deriv φ t₀)⁻¹ θ₀ := by
    simpa only [g, one_mul, mul_one, Function.comp_def, id] using
      hdi.comp_of_eq θ₀ ((hasDerivAt_id θ₀).sub_const θ₀) (by simp)
  have hshift : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 0) := by
    have ht : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 (θ₀ - θ₀)) :=
      (continuousAt_id.sub continuousAt_const :
        ContinuousAt (fun θ : ℝ => θ - θ₀) θ₀).tendsto
    simpa only [sub_self] using ht
  have hright : ∀ᶠ θ in 𝓝 θ₀, φ (g θ) = θ - θ₀ := by
    simpa only [g, he] using
      hshift.eventually (e.eventually_right_inverse ht)
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by
    simpa only [hg₀] using hgs.continuousAt.tendsto
  have hrecover := hgt.eventually (riemannMappingBoundaryPhase_circle_eventually hcircle)
  refine ⟨g, hg₀, hgs, hgd, ?_⟩
  filter_upwards [hright, hrecover] with θ hθ hrec
  change α (g θ) = α t₀ * unitCircleMap (φ (g θ)) at hrec
  rw [hrec, hcenter, hθ, circleMap_zero_mul]
  simp only [one_mul]
  congr 1
  ring

end


/-- Genuine inverse parametrization regularizes the actual forward circle trace.
Only the inverse curve and the physical graph curve have regularity premises. -/
theorem physicalCircleTrace_contDiffAt_of_inverse_curve 
     {t₀ θ₀ : ℝ}
    (hα : RealSmoothAt α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hdα : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = unitCircleMap θ₀)
    (hβ : RealSmoothAt β t₀) (hdβ : deriv β t₀ ≠ 0)
    (hforward : ∀ᶠ t in 𝓝 t₀, F (α t) = β t) :
    RealSmoothAt (physicalCircleTrace F) θ₀ ∧
      deriv (physicalCircleTrace F) θ₀ ≠ 0 := by
  obtain ⟨g, hg₀, hgs, hgd, hcircleG⟩ :=
    exists_riemannMappingBoundaryAngularInverse hα hcircle hdα hcenter
  have hc := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hdα
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by
    simpa  [hg₀] using hgs.continuousAt.tendsto
  have heq : physicalCircleTrace F =ᶠ[𝓝 θ₀] β ∘ g := by
    filter_upwards [hcircleG, hgt.eventually hforward] with θ hcircleθ hforwardθ
    aesop
  have hβg : RealSmoothAt (β ∘ g) θ₀ := by
    have hβ' : RealSmoothAt β (g θ₀) := by rw [hg₀]; exact hβ
    exact hβ'.comp θ₀ hgs
  have hdβg : HasDerivAt (β ∘ g)
      ((deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ • deriv β t₀) θ₀ := by
    apply ((hβ.differentiableAt (by simp)).hasDerivAt).scomp_of_eq θ₀ hgd hg₀.symm
  refine ⟨hβg.congr_of_eventuallyEq heq, ?_⟩
  rw [(hdβg.congr_of_eventuallyEq heq).deriv]
  exact smul_ne_zero (inv_ne_zero hc) hdβ

/-- The actual physical graph, restricted to its bottom horizontal line. -/
def riemannMappingGraphBoundaryCurve p c hc
    f hf (x : ℝ)  :=
  smoothDirichletGraphChart p c hc f hf (x : ℂ)

section
variable (p c : ℂ) (hc : c ≠ 0) {f : RealMap} (hf : RealSmooth f)
include p c hc f hf

theorem riemannMappingGraphBoundaryCurve_contDiff :
    RealSmooth (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) :=
  (smoothDirichletGraphChart_contDiff p c hc hf).comp Complex.ofRealCLM.contDiff

theorem riemannMappingGraphBoundaryCurve_hasDerivAt x :
    HasDerivAt (riemannMappingGraphBoundaryCurve p c hc f hf.continuous)
      (c⁻¹ * (1 + ((deriv f x : ℝ) : ℂ) * Complex.I)) x := by
  have hd := (smoothDirichletGraphChart_hasFDerivAt p c hc hf x).comp_hasDerivAt
    x (Complex.ofRealCLM.hasDerivAt (x := x))
  convert hd using 1
  · rfl
  · simp [smoothDirichletGraphDifferential, mul_add]

theorem riemannMappingGraphBoundaryCurve_deriv_ne_zero x :
    deriv (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) x ≠ 0 := by
  rw [(riemannMappingGraphBoundaryCurve_hasDerivAt p c hc hf x).deriv]
  apply mul_ne_zero (inv_ne_zero hc)
  intro hz
  have hr := congrArg Complex.re hz
  norm_num at hr

end


@[simp] theorem riemannMappingGraphBoundaryCurve_zero p c hc
     hf (hf₀ : f 0 = 0) :
    riemannMappingGraphBoundaryCurve p c hc f hf 0 = p := by
  simp_all [riemannMappingGraphBoundaryCurve, smoothDirichletGraphShear]

section ActualInverseGraph

variable {Ω } (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F )
    (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω)

include hb hS hsc hF hinj himage

section
variable {θ } {p c : ℂ} (hc : c ≠ 0) {f : RealMap} (hf : RealSmooth f) (hf₀ : f 0 = 0) (hp : p = riemannMappingClosedExtension F (unitCircleMap θ))
local notation "riemannMappingGraphBoundaryCurveFixed" => riemannMappingGraphBoundaryCurve p c hc f

include θ p c hc f hf hf₀ hp

/-- This interface uses the actual closed inverse and genuine bottom frontier.
The inverse graph smoothness and nonstationarity can be supplied by the Green
boundary-field and barrier theorems. -/
theorem riemannMapping_circleTrace_contDiffAt_of_inverse_graph
    (hfront : ∀ᶠ x : ℝ in 𝓝 0,
      riemannMappingGraphBoundaryCurveFixed hf.continuous x ∈ frontier Ω)
    (hα : RealSmoothAt
      (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurveFixed hf.continuous x)) 0)
    (hdα : deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurveFixed hf.continuous x)) 0 ≠ 0) :
    RealSmoothAt (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  let β := riemannMappingGraphBoundaryCurveFixed hf.continuous
  let α  := fun x => riemannMappingClosedInverse F (β x)
  have hcircle  :=
    hfront.mono fun _ hx =>
      riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hx
  have hcenter : α 0 = unitCircleMap θ := by
    change riemannMappingClosedInverse F
      (riemannMappingGraphBoundaryCurveFixed hf.continuous 0) = _
    rw [riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀, hp]
    exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage
      (circleMap_mem_closedBall 0 zero_le_one θ)
  have hforward  :=
    hfront.mono fun _ hx =>
      (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage
        (frontier_subset_closure hx)).2
  exact physicalCircleTrace_contDiffAt_of_inverse_curve hα hcircle hdα hcenter
    (riemannMappingGraphBoundaryCurve_contDiff p c hc hf).contDiffAt
    (riemannMappingGraphBoundaryCurve_deriv_ne_zero p c hc hf 0) hforward

/-- A genuine full-box membership chart supplies the bottom frontier premise;
mere mapping of the open upper half box is not used for that implication. -/
theorem riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
     (ha : 0 < a) (hb₀ : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
    (hα : RealSmoothAt
      (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurveFixed hf.continuous x)) 0)
    (hdα : deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurveFixed hf.continuous x)) 0 ≠ 0) :
    RealSmoothAt (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  apply riemannMapping_circleTrace_contDiffAt_of_inverse_graph hb hS hsc F hF hinj himage
    hc hf hf₀ hp _ hα hdα
  have hI : ∀ᶠ x : ℝ in 𝓝 0, x ∈ Ioo (-a) a :=
    Ioo_mem_nhds (by linarith) ha
  exact hI.mono fun x hx =>
    smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous
      hb₀ hchart (abs_lt.mpr hx)

end


/-- All genuine inverse graph packets yield global smoothness and
nonstationarity of the actual angular trace of the closed extension. -/
theorem riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs
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
    RealSmooth (physicalCircleTrace (riemannMappingClosedExtension F)) ∧
      ∀ θ : ℝ, deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  have hall θ :
      RealSmoothAt (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
    let p := riemannMappingClosedExtension F (unitCircleMap θ)
    have hp : p ∈ frontier Ω :=
      riemannMappingClosedExtension_mem_frontier hb hS.isLipschitzDomain hsc F hF hinj himage
        (by simp  )
    obtain ⟨c, hc, f, hf, a, b, hf₀, ha, hb₀, hchart, hα, hdα⟩ := hgraphs p hp
    exact riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
      hb hS hsc F hF hinj himage hc hf hf₀ rfl ha hb₀ hchart hα hdα
  exact ⟨contDiff_iff_contDiffAt.mpr fun θ => (hall θ).1, fun θ => (hall θ).2⟩

end ActualInverseGraph

/-- A small actual closed rectangle avoids a point avoided at its center. -/
theorem exists_riemannMapping_halfBox_avoiding  {w : ℂ}
    (hΨ : ContinuousAt Ψ 0) (hne : Ψ 0 ≠ w)  (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∀ z ∈ smoothDirichletClosedHalfBox r r, Ψ z ≠ w := by
  have hev  :=
    hΨ.eventually (eventually_ne_nhds hne)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  let r := min ρ (ε / 4)
  have hr : 0 < r := lt_min hρ (by positivity)
  have hrε : r ≤ ε / 4 := min_le_right _ _
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  intro z hz
  apply hball
  rw [mem_ball_zero_iff]
  have hzI : |z.im| ≤ r := by rw [abs_of_nonneg hz.2.1]; exact hz.2.2
  have hzN : ‖z‖ ≤ 2 * r := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * r := by linarith [hz.1]
  exact hzN.trans_lt (by linarith)

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω) {p } (hp : p ∈ frontier Ω)
include Ω hb hS hsc F hF hinj himage p hp

/-- The genuine original-domain gradient fields are transferred to Green
by its actual pole-subtracted datum.  The whole chosen closed rectangle
avoids the original pole; no boundary derivative of Green is assumed. -/
theorem exists_riemannMapping_genuine_green_smooth_boundary_fields :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : RealMap) (hf : RealSmooth f)
      (r : ℝ) (P Q : PlaneMap),
      f 0 = 0 ∧ 0 < r ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let G := riemannMappingFlattenedGreen F Ψ
       let U := smoothDirichletHalfBox r r
       let V := smoothDirichletClosedHalfBox r r
       (∀ z : ℂ, |z.re| < r → |z.im| < r → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ U Ω ∧ (∀ z ∈ V, Ψ z ≠ F 0) ∧
       ContinuousOn (riemannMappingClosedInverse F ∘ Ψ) V ∧
       ContinuousOn G V ∧ RealSmoothOn G U ∧
       ContinuousOn P V ∧ ContinuousOn Q V ∧
       EqOn P (dirD G 1) U ∧ EqOn Q (dirD G Complex.I) U ∧
       RealSmoothAt (fun x : ℝ => P (x : ℂ)) 0 ∧
       RealSmoothAt (fun x : ℝ => Q (x : ℂ)) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hchart, hclosed, hmap, huc, hus, huz,
    hXc, hYc, hXu, hYu, hXsmooth, hYsmooth⟩ :=
    exists_riemannMapping_genuine_gradient_smooth_boundary_fields
      hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let L := riemannMappingGreenLogDatum F d Ψ
  have hΨ  :=
    smoothDirichletGraphChart_contDiff p c hc hf
  have hΨ₀ : Ψ 0 = p := by
    solve_by_elim (maxDepth := 5) [riemannMappingGraphBoundaryCurve, riemannMappingGraphBoundaryCurve_zero]
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    exact hp.2 (riemannMapping_pole_mem F himage)
  obtain ⟨r, hr, hrρ, hne⟩ := exists_riemannMapping_halfBox_avoiding
    Ψ.continuous.continuousAt (by rw [hΨ₀]; exact hpne) hρ
  let U := smoothDirichletHalfBox r r
  let V := smoothDirichletClosedHalfBox r r
  have hrA : r < A := hrρ.trans_lt (hρA.trans (by linarith))
  have hrb  := hrρ.trans_lt hρb
  have hUρ : U ⊆ smoothDirichletHalfBox ρ ρ := by
    grind [PolyaNeumann.smoothDirichletHalfBox]
  have hVρ : V ⊆ smoothDirichletClosedHalfBox ρ ρ := by
    grind [PolyaNeumann.smoothDirichletClosedHalfBox]
  have hUA : U ⊆ smoothDirichletHalfBox A b := by
    grind [PolyaNeumann.smoothDirichletHalfBox]
  have hVA : V ⊆ smoothDirichletClosedHalfBox A b := by
    grind [PolyaNeumann.smoothDirichletClosedHalfBox]
  have hUV : U ⊆ V := by
    intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hclosed' : MapsTo Ψ V (closure Ω) := fun z hz => hclosed (hVA hz)
  have hmap' : MapsTo Ψ U Ω := fun z hz => hmap (hUA hz)
  have hLs (z : ℂ) (hz : z ∈ V)  :=
    riemannMappingGreenLogDatum_contDiffAt F d hΨ.contDiffAt (hne z hz)
  have hLc : ContinuousOn L V := fun z hz => (hLs z hz).continuousAt.continuousWithinAt
  have hDs (w : ℂ) (z : ℂ) (hz : z ∈ V)  :=
    contDiffAt_infty_dirD (hLs z hz) w
  have hDc (w : ℂ) : ContinuousOn (dirD L w) V :=
    fun z hz => (hDs w z hz).continuousAt.continuousWithinAt
  have hV₀ : (0 : ℂ) ∈ V := by
    change |(0 : ℂ).re| ≤ r ∧ 0 ≤ (0 : ℂ).im ∧ (0 : ℂ).im ≤ r
    simpa   using
      (show (0 : ℝ) ≤ r ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ r from ⟨hr.le, le_rfl, hr.le⟩)
  have hLsmooth (w : ℂ) :=
    (hDs w 0 hV₀).comp (f := fun x : ℝ => (x : ℂ)) (g := dirD L w) 0
      Complex.ofRealCLM.contDiff.contDiffAt
  let P := ((X + dirD L 1))
  let Q := ((Y + dirD L Complex.I))
  let G := riemannMappingFlattenedGreen F Ψ
  have hsum : EqOn G (((u + L))) V := by
    intro z hz
    exact riemannMappingFlattenedGreen_eq_remainder_add_datum
      hb hS hsc F hF hinj himage d Ψ (hclosed' hz) (hne z hz)
  have hGc := ((huc.mono hVA).add hLc).congr hsum
  have hus' := hus.mono hUA
  have hLs' : RealSmoothOn L U :=
    fun z hz => (hLs z (hUV hz)).contDiffWithinAt
  have hGs :=
    (hus'.add hLs').congr (hsum.mono hUV)
  have hU := isOpen_smoothDirichletHalfBox r r
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
    (riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).comp
      Ψ.continuous.continuousOn hclosed',
    hGc, hGs, (hXc.mono hVρ).add (hDc 1),
    (hYc.mono hVρ).add (hDc Complex.I), hP, hQ, hXsmooth.add (hLsmooth 1),
    hYsmooth.add (hLsmooth Complex.I)⟩
  grind

/-- Genuine inverse graph regularity follows from the original physical
domain, its actual Green function and the proved finite-order boundary fields. -/
theorem exists_riemannMapping_genuine_regular_inverse_graph :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : RealMap) (hf : RealSmooth f) (a b : ℝ),
      f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
      RealSmoothAt
        (fun x : ℝ => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
      deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0 := by
  obtain ⟨c, hc, f, hf, r, P, Q, hf₀, hr, hchart, hmap, hne,
    hJ, hGc, hGs, hPc, hQc, hP, hQ, hPsmooth, hQsmooth⟩ :=
    exists_riemannMapping_genuine_green_smooth_boundary_fields hb hS hsc F hF hinj himage hp
  have hpole : ∀ z ∈ smoothDirichletHalfBox r r,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0 := by
    intro z hz
    exact hne z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hα := riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    hb hS hsc F hF hinj himage p c hc hf hr hr hmap hpole hJ hPc hQc hP hQ hPsmooth hQsmooth
  have hdα := riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    hb hS hsc F hF hinj himage p c hc hf hf₀ hp hr hr hchart hmap hpole
      hJ hGc hGs hPc hQc hP hQ
  exact ⟨c, hc, f, hf, r, r, hf₀, hr, hr, hchart, hα, hdα⟩

end


end PolyaNeumann

end
