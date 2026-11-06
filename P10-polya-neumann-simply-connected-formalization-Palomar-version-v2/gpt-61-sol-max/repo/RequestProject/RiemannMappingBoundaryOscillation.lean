module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.RiemannMappingEnergy
public import RequestProject.GreenWinding
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Finite-energy circular caps of the interior Riemann map

The derivative is cut off to the **open** disk, where the actual map is
holomorphic. Translated polar integration and the nonintegrability of
`1/r` at zero give arbitrarily small circles whose portions in the disk
have arbitrarily small image length. The chosen radius is also a genuine
integrable angular slice, so no default-valued integral is used as a
substitute for finite length.

Integrating the actual derivative on any open circular arc in the disk
constructs its finite endpoint values. None of these statements assumes
or asserts a continuous extension of the Riemann map to the whole circle.
The Jordan crosscut separation argument needed to turn these cap estimates
into a full Carathéodory extension remains a separate geometric step. In
that step distinct frontier endpoints are joined by a short physical
boundary arc; coincident endpoints instead give a small closed loop.
Endpoint injectivity is not assumed before proving the boundary theorem.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

/-- The actual complex derivative, extended by zero outside its open
domain. Values of the original total function on the boundary are unused. -/
def riemannInteriorDerivative (F : PlaneMap) z  :=
  (unitDisk).indicator (deriv F) z

theorem riemannInteriorDerivative_measurable F :
    Measurable (riemannInteriorDerivative F) :=
  (measurable_deriv F).indicator measurableSet_ball

section
variable (F : PlaneMap) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) (hb : Bornology.IsBounded (F '' unitDisk))

include F hF hinj hb in
theorem riemannInteriorDerivative_sq_integrable :
    Integrable (fun z => ‖riemannInteriorDerivative F z‖ ^ 2) := by
  have h := (interiorConformal_deriv_sq_integrable F hF hinj hb).integrable_indicator
    measurableSet_ball
  refine h.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ ball 0 1
  · simp_all [riemannInteriorDerivative]
  simp_all [riemannInteriorDerivative]

/-- The true angular derivative of `F ∘ circleMap c r` on its portions
inside the disk, and zero on the remaining portions. -/
def riemannCapDerivative F c r θ  :=
  riemannInteriorDerivative F (circleMap c r θ) * (circleMap 0 r θ * Complex.I)

theorem riemannCapDerivative_measurable F c r :
    Measurable (riemannCapDerivative F c r) := ((riemannInteriorDerivative_measurable F).comp
    (continuous_circleMap c r).measurable).mul
      ((continuous_circleMap 0 r).measurable.mul_const Complex.I)

theorem norm_riemannCapDerivative F c 
    (hr : 0 ≤ r) θ :
    ‖riemannCapDerivative F c r θ‖ =
      r * ‖riemannInteriorDerivative F (circleMap c r θ)‖ := by
  simp  [riemannCapDerivative, abs_of_nonneg hr, mul_comm]

theorem riemannCapDerivative_hasDerivAt F
    (hF : DifferentiableOn ℂ F unitDisk)
    c r θ (hθ : circleMap c r θ ∈ unitDisk) :
    HasDerivAt (fun t => F (circleMap c r t)) (riemannCapDerivative F c r θ) θ := by
  have hd := (hF.differentiableAt (isOpen_ball.mem_nhds hθ)).hasDerivAt
  have h := hd.comp θ (hasDerivAt_circleMap c r θ)
  simpa  [riemannCapDerivative, riemannInteriorDerivative,
    indicator_of_mem hθ, Function.comp_def] using h

/-- Polar integration of an actual nonnegative L¹ density after a
translation. This supplies both finite slices and an integrable radial
energy density. -/
private theorem translated_polar_integrable 
    (hgm : Measurable g) (hg : Integrable g) c :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * g (c + Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have ht  := hg.comp_add_left c
  have hm : Measurable (fun p : ℝ × ℝ =>
      p.1 * g (c + Complex.polarCoord.symm p)) :=
    measurable_fst.mul (hgm.comp (measurable_const.add measurable_complexPolarCoord_symm))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have heq :
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ) =
      ∫⁻ z : ℂ, ‖g (c + z)‖ₑ := by
    rw [← Complex.lintegral_comp_polarCoord_symm]
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    change ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ =
      ENNReal.ofReal p.1 • ‖g (c + Complex.polarCoord.symm p)‖ₑ
    rw [enorm_mul, Real.enorm_eq_ofReal hp.1.le]
    rfl
  rw [heq]
  exact ht.hasFiniteIntegral

/-- An integrable radial energy cannot be bounded below by `ε/r` at
almost every sufficiently small radius. A null exceptional set of bad
slices can be excluded simultaneously. -/
private theorem exists_small_radius_of_integrable 
    (hR : IntegrableOn R (Ioi (0 : ℝ))) {P : ℝ → Prop}
    (hP : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), P r)
     (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ, P r ∧ r * R r < ε := by
  by_contra hn
  have hge : ∀ r ∈ Ioo (0 : ℝ) δ, P r → ε ≤ r * R r := by
    simp_all
  have hi : IntegrableOn (fun r : ℝ => ε * r⁻¹) (Ioo 0 δ) := by
    apply (hR.mono_set Ioo_subset_Ioi_self).mono'
      (measurable_const.mul measurable_inv).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hP] with r hr hp
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg hε.le (inv_nonneg.mpr hr.1.le))]
    simpa  [div_eq_mul_inv] using
      (div_le_iff₀ hr.1).2 (by simpa  [mul_comm] using hge r hr hp)
  have hinv : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo 0 δ) := by
    have h := hi.const_mul ε⁻¹
    simpa  [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hε.ne'] using h
  have hp : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo 0 δ) := by
    simpa  [Real.rpow_neg_one] using hinv
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 hp
  linarith

include F hF hinj hb in
/-- Arbitrarily small radii have a genuinely integrable angular
derivative and arbitrarily small angular squared energy. -/
theorem riemannMapping_exists_small_cap_energy
    c  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (fun θ =>
        ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
        (Ioo (-Real.pi) Real.pi) ∧
      r ^ 2 * (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2) < ε := by
  let g  := fun z => ‖riemannInteriorDerivative F z‖ ^ 2
  have hgp := translated_polar_integrable
    ((riemannInteriorDerivative_measurable F).norm.pow_const 2)
    (riemannInteriorDerivative_sq_integrable F hF hinj hb) c
  have heq : ∀ p : ℝ × ℝ,
      c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [heq] at hgp
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hgp
  let R  := fun r => ∫ θ in Ioo (-Real.pi) Real.pi,
    r * g (circleMap c r θ)
  have hR  := hgp.integral_prod_left
  have hslice : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      IntegrableOn (fun θ => g (circleMap c r θ)) (Ioo (-Real.pi) Real.pi) := by
    filter_upwards [hgp.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    have h := hr.const_mul r⁻¹
    have hrpos  := hr0
    simpa  [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hrpos.ne'] using h
  obtain ⟨r, hr, hs, hsmall⟩ := exists_small_radius_of_integrable hR hslice hδ hε
  refine ⟨r, hr, hs, ?_⟩
  simpa  [integral_const_mul, ← mul_assoc, ← pow_two] using hsmall

/-- Finite angular squared energy gives genuine finite angular length. -/
private theorem riemannCapDerivative_integrable F c
     (hr : 0 ≤ r)
    (hs : IntegrableOn (fun θ =>
      ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
      (Ioo (-Real.pi) Real.pi)) :
    IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) := by
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    simpa  [IntegrableOn, norm_riemannCapDerivative F c hr, mul_pow] using hs.const_mul (r ^ 2)
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp )
  apply (hconst.add hsq).mono' (riemannCapDerivative_measurable F c r).aestronglyMeasurable
  exact Eventually.of_forall fun θ => by
    dsimp
    nlinarith

include F hF hinj hb in
/-- The Courant–Lebesgue length consequence for the actual map. The
integral includes exactly the portions of the circle lying in the open
disk; the derivative was proved to vanish on its other portions. -/
theorem riemannMapping_exists_small_cap_length
    c  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) ∧
      (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) < ε := by
  let a  := ε / (4 * Real.pi)
  have ha  := div_pos hε (by positivity)
  obtain ⟨r, hr, hs, hsmall⟩ := riemannMapping_exists_small_cap_energy
    F hF hinj hb c hδ (show 0 < 2 * a * ε by positivity)
  have hi := riemannCapDerivative_integrable F c hr.1.le hs
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    simpa only [IntegrableOn, norm_riemannCapDerivative F c hr.1.le, mul_pow]
      using hs.const_mul (r ^ 2)
  have hsqsmall : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) < 2 * a * ε := by
    simpa only [norm_riemannCapDerivative F c hr.1.le, mul_pow,
      integral_const_mul] using hsmall
  have hconst : IntegrableOn (fun _ : ℝ => a) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp )
  have hpoint : ∀ θ, ‖riemannCapDerivative F c r θ‖ ≤
      a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) := by
    intro θ
    have h : (‖riemannCapDerivative F c r θ‖ - a) * (4 * a) ≤
        ‖riemannCapDerivative F c r θ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 2 * a)]
    have := (le_div_iff₀ (show 0 < 4 * a by positivity)).2 h
    linarith
  have hle := integral_mono hi.norm (hconst.add (hsq.div_const (4 * a))) hpoint
  change (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) ≤
    ∫ θ in Ioo (-Real.pi) Real.pi, a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) at hle
  have hmeasure : (∫ θ in Ioo (-Real.pi) Real.pi, a) = 2 * Real.pi * a := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    ring
  rw [integral_add hconst (hsq.div_const (4 * a)), hmeasure, integral_div] at hle
  have hdiv : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) / (4 * a) < ε / 2 := by
    apply (div_lt_iff₀ (show 0 < 4 * a by positivity)).2
    nlinarith [hsqsmall]
  refine ⟨r, hr, hi, hle.trans_lt ?_⟩
  have hhalf : 2 * Real.pi * a = ε / 2 := by
    dsimp [a]
    field_simp [Real.pi_pos.ne']; ring
  linarith

end


theorem riemannCapDerivative_periodic F c r :
    Function.Periodic (riemannCapDerivative F c r) circlePeriod := by
  intro θ
  simp  [riemannCapDerivative, periodic_circleMap c r θ,
    periodic_circleMap 0 r θ]

/-- A good polar slice is integrable on every finite angular interval,
including intervals crossing the polar cut. -/
theorem riemannCapDerivative_intervalIntegrable F c r
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    a b : IntervalIntegrable (riemannCapDerivative F c r) volume a b := by
  have hbase : IntervalIntegrable (riemannCapDerivative F c r) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    exact hi
  exact (riemannCapDerivative_periodic F c r).intervalIntegrable Real.two_pi_pos.ne'
    hbase a b

section
variable (F : PlaneMap) (hF : DifferentiableOn ℂ F unitDisk) (c : ℂ)
include F hF c

/-- On an actual open circular arc inside the disk, the cut-off
derivative is continuous at each parameter. Nothing is required of `F`
at either endpoint of the arc. -/
theorem riemannCapDerivative_continuousAt_interior r θ (hθ : circleMap c r θ ∈ unitDisk) :
    ContinuousAt (riemannCapDerivative F c r) θ := by
  have hcont : ContinuousAt (fun t =>
      deriv F (circleMap c r t) * (circleMap 0 r t * Complex.I)) θ := by
    exact (((hF.deriv isOpen_ball).continuousOn.continuousAt
      (isOpen_ball.mem_nhds hθ)).comp (continuous_circleMap c r).continuousAt).mul
        ((continuous_circleMap 0 r).continuousAt.mul_const Complex.I)
  apply hcont.congr
  have hmem  :=
    (continuous_circleMap c r).continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds hθ)
  filter_upwards [hmem] with t ht
  simp_all [riemannCapDerivative, riemannInteriorDerivative]

section
variable (r : ℝ) (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) {a b : ℝ}
include r hi a b

/-- The actual image of every open circular arc has finite endpoint
limits at a good radius. The continuous function is explicitly obtained
by integrating the true angular derivative; no boundary value of the
original total function is used. -/
theorem riemannMapping_cap_continuous_extension (hab : a < b)
    (harc : MapsTo (circleMap c r) (Ioo a b) unitDisk) :
    ∃ G : ComplexCurve, Continuous G ∧
      EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] a) (𝓝 (G a)) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] b) (𝓝 (G b)) := by
  let t  := (a + b) / 2
  have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
  let V  := riemannCapDerivative F c r
  have hVi  :=
    riemannCapDerivative_intervalIntegrable F c r hi
  let G  := fun θ => F (circleMap c r t) + ∫ s in t..θ, V s
  have hGc : Continuous G := continuous_const.add
    (intervalIntegral.continuous_primitive hVi t)
  have hGd : ∀ θ ∈ Ioo a b, HasDerivAt G (V θ) θ := by
    intro θ hθ
    have hd := intervalIntegral.integral_hasDerivAt_right (hVi t θ)
      (riemannCapDerivative_measurable F c r).aestronglyMeasurable.stronglyMeasurableAtFilter
      (riemannCapDerivative_continuousAt_interior F hF c r θ (harc hθ))
    aesop
  have hfd  :=
    fun θ hθ => riemannCapDerivative_hasDerivAt F hF c r θ (harc hθ)
  have heq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun θ hθ => (hGd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => (hfd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => by rw [(hGd θ hθ).deriv, (hfd θ hθ).deriv]) ht
    measurability
  refine ⟨G, hGc, heq, ?_, ?_⟩
  · refine ((hGc.tendsto a).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact heq hθ
  · refine ((hGc.tendsto b).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact heq hθ

/-- The exact subarc length bound, including endpoint parameters. This
also supplies the genuine arclength domination needed to reparametrize
the cap image by a Lipschitz curve. -/
theorem riemannMapping_cap_extension_subarc_displacement
    (harc : MapsTo (circleMap c r) (Ioo a b) unitDisk)
     (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b))
     (hθ : θ ∈ Icc a b) (hτ : τ ∈ Icc a b) (hθτ : θ ≤ τ) :
    ‖G τ - G θ‖ ≤ ∫ s in θ..τ, ‖riemannCapDerivative F c r s‖ := by
  have hsub : Ioo θ τ ⊆ Ioo a b := by
    grind
  have hGd : ∀ s ∈ Ioo a b, HasDerivAt G (riemannCapDerivative F c r s) s := by
    intro s hs
    apply (riemannCapDerivative_hasDerivAt F hF c r s (harc hs)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact hGeq hu
  apply norm_sub_le_integral_of_norm_deriv_le_of_le hθτ hGc.continuousOn
    (fun s hs => (hGd s (hsub hs)).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall fun s hs => ?_)
    (riemannCapDerivative_intervalIntegrable F c r hi θ τ).norm
  rw [(hGd s (hsub hs)).deriv]

end


end


/-- A finite image limit at a boundary source point belongs to the
physical frontier. The genuine holomorphic interior inverse rules out
an interior image limit. -/
theorem riemannMapping_limit_mem_frontier {A : Type*} {l } [NeBot l]
    F (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    {z : A → ℂ} {ζ w : ℂ} (hζ : ‖ζ‖ = 1)
    (hzin : ∀ᶠ x in l, z x ∈ unitDisk)
    (hz : Tendsto z l (𝓝 ζ)) (hw : Tendsto (fun x => F (z x)) l (𝓝 w)) :
    w ∈ frontier (F '' unitDisk) := by
  have hopen  :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball
      (convex_ball 0 1).isPreconnected hF hinj subset_rfl isOpen_ball
  have hcl  :=
    mem_closure_of_tendsto hw (hzin.mono fun x hx => mem_image_of_mem F hx)
  rw [hopen.frontier_eq]
  refine ⟨hcl, ?_⟩
  intro hwin
  obtain ⟨J, hJ, hJmap, hJF, _⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball 0 1).isPreconnected hF hinj
  have him  :=
    hzin.mono fun x hx => mem_image_of_mem F hx
  have hJlim  :=
    (hJ.continuousOn w hwin).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hw, him⟩)
  have hJz  := hJlim.congr' (hzin.mono fun x hx => hJF _ hx)
  have heq  := tendsto_nhds_unique hz hJz
  measurability

/-- The inward central angle of the circular cap based at `ζ`. -/
def riemannCapCenterAngle ζ  := Complex.arg (-ζ)

/-- The exact half-angle cut out by the open unit disk. -/
def riemannCapHalfAngle r  := Real.arccos (r / 2)

section
variable {ζ : ℂ} (hζ : ‖ζ‖ = 1)
include ζ hζ

private theorem riemannCap_circle_eq r θ :
    circleMap ζ r (riemannCapCenterAngle ζ + θ) = ζ * (1 - circleMap 0 r θ) := by
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa  [riemannCapCenterAngle, hζ]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  simp  [circleMap, add_mul, Complex.exp_add, he]
  ring

private theorem riemannCap_circle_norm_sq r θ :
    ‖circleMap ζ r (riemannCapCenterAngle ζ + θ)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos θ := by
  rw [riemannCap_circle_eq hζ, norm_mul, hζ, one_mul,
    ← Complex.normSq_eq_norm_sq]
  calc
    Complex.normSq (1 - circleMap 0 r θ) =
        (1 - r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
      simp [circleMap, Complex.normSq_apply, pow_two]
    _ = 1 + r ^ 2 - 2 * r * Real.cos θ := by
      linear_combination r ^ 2 * (Real.sin_sq_add_cos_sq θ)

/-- The entire open cap, including its exact angular endpoints, is
determined directly from the unit disk geometry. -/
theorem riemannCap_geometry 
    (hr : 0 < r) (hr1 : r < 1) :
    let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
    let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
    a < b ∧ b ≤ a + 2 * Real.pi ∧
      MapsTo (circleMap ζ r) (Ioo a b) unitDisk ∧
      ‖circleMap ζ r a‖ = 1 ∧ ‖circleMap ζ r b‖ = 1 := by
  let α := riemannCapHalfAngle r
  have hα : 0 < α := Real.arccos_pos.2 (by linarith)
  have hαπ : α ≤ Real.pi := Real.arccos_le_pi _
  have hc : Real.cos α = r / 2 := Real.cos_arccos (by linarith) (by linarith)
  refine ⟨by linarith,
    by linarith, ?_, ?_, ?_⟩
  · intro θ hθ
    let u := θ - riemannCapCenterAngle ζ
    have hu : |u| < α := abs_lt.2 ⟨by linarith [hθ.1],
      by linarith [hθ.2]⟩
    have hcos : r / 2 < Real.cos u := by
      rw [← hc, ← Real.cos_abs u]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ hu
    rw [mem_ball_zero_iff]
    apply (sq_lt_one_iff₀ (norm_nonneg _)).1
    have heq : θ = riemannCapCenterAngle ζ + u := by ring
    rw [heq, riemannCap_circle_norm_sq hζ]
    nlinarith
  · have heq : riemannCapCenterAngle ζ - riemannCapHalfAngle r =
        riemannCapCenterAngle ζ + -α := by dsimp [α]; ring
    have hsq : ‖circleMap ζ r (riemannCapCenterAngle ζ - riemannCapHalfAngle r)‖ ^ 2 = 1 := by
      rw [heq, riemannCap_circle_norm_sq hζ, Real.cos_neg, hc]
      ring
    nlinarith [norm_nonneg (circleMap ζ r
      (riemannCapCenterAngle ζ - riemannCapHalfAngle r))]
  · have hsq : ‖circleMap ζ r (riemannCapCenterAngle ζ + riemannCapHalfAngle r)‖ ^ 2 = 1 := by
      rw [riemannCap_circle_norm_sq hζ, hc]
      ring
    nlinarith [norm_nonneg (circleMap ζ r
      (riemannCapCenterAngle ζ + riemannCapHalfAngle r))]

end


end PolyaNeumann

end
