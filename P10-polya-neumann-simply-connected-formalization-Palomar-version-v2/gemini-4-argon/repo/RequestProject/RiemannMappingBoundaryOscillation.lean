module

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
local notation "Φ0" => ball 0 1

def riemannInteriorDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Φ0).indicator (deriv F) z

theorem riemannInteriorDerivative_measurable F :
    Measurable (riemannInteriorDerivative F) :=
  (measurable_deriv F).indicator measurableSet_ball

/-- The true angular derivative of `F ∘ circleMap c r` on its portions
inside the disk, and zero on the remaining portions. -/
def riemannCapDerivative (F : ℂ → ℂ) (c : ℂ) (r θ : ℝ) : ℂ :=
  riemannInteriorDerivative F (circleMap c r θ) * (circleMap 0 r θ * Complex.I)

theorem riemannCapDerivative_measurable F c r :
    Measurable (riemannCapDerivative F c r) := by
  exact ((riemannInteriorDerivative_measurable F).comp
    (continuous_circleMap c r).measurable).mul
      ((continuous_circleMap 0 r).measurable.mul_const Complex.I)

theorem norm_riemannCapDerivative F c 
    (hr : 0 ≤ r) θ :
    ‖riemannCapDerivative F c r θ‖ =
      r * ‖riemannInteriorDerivative F (circleMap c r θ)‖ := by
  simp [riemannCapDerivative, abs_of_nonneg hr, mul_comm]

theorem riemannCapDerivative_hasDerivAt F
    (hF : DifferentiableOn ℂ F (Φ0))
    c r θ (hθ : circleMap c r θ ∈ Φ0) :
    HasDerivAt (fun t => F (circleMap c r t)) (riemannCapDerivative F c r θ) θ := by
  simpa [riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem hθ, Function.comp_def] using ((hF.differentiableAt (isOpen_ball.mem_nhds hθ)).hasDerivAt).comp θ (hasDerivAt_circleMap c r θ)

/-- Polar integration of an actual nonnegative L¹ density after a
translation. This supplies both finite slices and an integrable radial
energy density. -/
private theorem translated_polar_integrable 
    (hgm : Measurable g) (hg : Integrable g) c :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * g (c + Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  refine ⟨(measurable_fst.mul (hgm.comp (measurable_const.add measurable_complexPolarCoord_symm))).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, show (∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ) = ∫⁻ z : ℂ, ‖g (c + z)‖ₑ by
    rw [← Complex.lintegral_comp_polarCoord_symm]
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    change ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ = _
    rw [enorm_mul, Real.enorm_eq_ofReal hp.1.le]
    rfl]
  exact (hg.comp_add_left c).hasFiniteIntegral

/-- An integrable radial energy cannot be bounded below by `ε/r` at
almost every sufficiently small radius. A null exceptional set of bad
slices can be excluded simultaneously. -/
private theorem exists_small_radius_of_integrable 
    (hR : IntegrableOn R (Ioi 0)) {P : ℝ → Prop}
    (hP : ∀ᵐ r ∂volume.restrict (Ioi 0), P r)
     (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo 0 δ, P r ∧ r * R r < ε := by
  by_contra hn
  have hi : IntegrableOn (fun r => ε * r⁻¹) (Ioo 0 δ) := by
    apply (hR.mono_set Ioo_subset_Ioi_self).mono'
      (measurable_const.mul measurable_inv).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hP] with r hr hp
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg hε.le (inv_nonneg.mpr hr.1.le))]
    simpa only [div_eq_mul_inv] using
      (div_le_iff₀ hr.1).2 (by simpa [mul_comm] using (show ∀ r ∈ Ioo 0 δ, P r → ε ≤ r * R r by
        intro r hr hp
        by_contra hh
        exact hn ⟨r, hr, hp, lt_of_not_ge hh⟩) r hr hp)
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 (show IntegrableOn (fun r => r ^ (-1 : ℝ)) (Ioo 0 δ) by
    simpa [Real.rpow_neg_one] using show IntegrableOn (fun r => r⁻¹) (Ioo 0 δ) by
      simpa [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hε.ne'] using (hi.const_mul ε⁻¹))
  linarith

/-- Arbitrarily small radii have a genuinely integrable angular
derivative and arbitrarily small angular squared energy. -/
theorem riemannMapping_exists_small_cap_energy F
    (hF : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0))
    (hb : Bornology.IsBounded (F '' Φ0))
    (c : ℂ)  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo 0 δ,
      IntegrableOn (fun θ =>
        ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
        (Ioo (-Real.pi) Real.pi) ∧
      r ^ 2 * (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2) < ε := by
  let g : ℂ → ℝ := fun z => ‖riemannInteriorDerivative F z‖ ^ 2
  have hgp := translated_polar_integrable
    ((riemannInteriorDerivative_measurable F).norm.pow_const 2)
    (by
      refine ((interiorConformal_deriv_sq_integrable F hF hinj hb).integrable_indicator measurableSet_ball).congr (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ Φ0
      · simp [riemannInteriorDerivative, indicator_of_mem hz]
      · simp [riemannInteriorDerivative, indicator_of_notMem hz, zero_pow (by decide : 2 ≠ 0)]) c
  have heq : ∀ p : ℝ × ℝ,
      c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [heq] at hgp
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hgp
  let R : ℝ → ℝ := fun r => ∫ θ in Ioo (-Real.pi) Real.pi,
    r * g (circleMap c r θ)
  obtain ⟨r, hr, hs, hsmall⟩ := exists_small_radius_of_integrable hgp.integral_prod_left (by
    filter_upwards [hgp.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul] using (hr.const_mul r⁻¹)) hδ hε
  refine ⟨r, hr, hs, ?_⟩
  simpa only [R, integral_const_mul, ← mul_assoc, ← pow_two, g] using hsmall

/-- The Courant–Lebesgue length consequence for the actual map. The
integral includes exactly the portions of the circle lying in the open
disk; the derivative was proved to vanish on its other portions. -/
theorem riemannMapping_exists_small_cap_length F
    (hF : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0))
    (hb : Bornology.IsBounded (F '' Φ0))
    c  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo 0 δ,
      IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) ∧
      (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) < ε := by
  let a := ε / (4 * Real.pi)
  obtain ⟨r, hr, hs, hsmall⟩ := riemannMapping_exists_small_cap_energy
    F hF hinj hb c hδ (show 0 < 2 * a * ε by positivity)
  have hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) := by
    have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
        (Ioo (-Real.pi) Real.pi) := by
      simpa [IntegrableOn, norm_riemannCapDerivative F c hr.1.le, mul_pow] using hs.const_mul (r ^ 2)
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) :=
      integrableOn_const (by simp)
    apply (hconst.add hsq).mono' (riemannCapDerivative_measurable F c r).aestronglyMeasurable
    exact Eventually.of_forall fun θ => by
      dsimp
      nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 1)]
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    simpa only [IntegrableOn, norm_riemannCapDerivative F c hr.1.le, mul_pow]
      using hs.const_mul (r ^ 2)
  have hconst : IntegrableOn (fun _ => a) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hle := integral_mono hi.norm (hconst.add (hsq.div_const (4 * a))) (show ∀ θ, ‖riemannCapDerivative F c r θ‖ ≤ a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) by
    intro θ
    have := (le_div_iff₀ (show 0 < 4 * a by positivity)).2 (show (‖riemannCapDerivative F c r θ‖ - a) * (4 * a) ≤ ‖riemannCapDerivative F c r θ‖ ^ 2 by
      nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 2 * a)])
    linarith)
  change (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) ≤
    ∫ θ in Ioo (-Real.pi) Real.pi, a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) at hle
  rw [integral_add hconst (hsq.div_const (4 * a)), show (∫ θ in Ioo (-Real.pi) Real.pi, a) = 2 * Real.pi * a by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    ring, integral_div] at hle
  have hdiv : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) / (4 * a) < ε / 2 := by
    apply (div_lt_iff₀ (show 0 < 4 * a by positivity)).2
    nlinarith [show (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖ ^ 2) < 2 * a * ε by
      simpa only [norm_riemannCapDerivative F c hr.1.le, mul_pow,
        integral_const_mul] using hsmall]
  refine ⟨r, hr, hi, hle.trans_lt ?_⟩
  rw [show 2 * Real.pi * a = ε / 2 by
    dsimp [a]
    field_simp [Real.pi_pos.ne']; ring]
  linarith

theorem riemannCapDerivative_periodic F c r :
    Function.Periodic (riemannCapDerivative F c r) (2 * Real.pi) := by
  intro θ
  simp [riemannCapDerivative, periodic_circleMap c r θ, periodic_circleMap 0 r θ]

/-- A good polar slice is integrable on every finite angular interval,
including intervals crossing the polar cut. -/
theorem riemannCapDerivative_intervalIntegrable F c r
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    a b : IntervalIntegrable (riemannCapDerivative F c r) volume a b := by
  exact (riemannCapDerivative_periodic F c r).intervalIntegrable Real.two_pi_pos.ne'
    (by
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
        intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
      exact hi) a b

/-- The actual image of every open circular arc has finite endpoint
limits at a good radius. The continuous function is explicitly obtained
by integrating the true angular derivative; no boundary value of the
original total function is used. -/
theorem riemannMapping_cap_continuous_extension F
    (hF : DifferentiableOn ℂ F (Φ0))
    c r
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
     (hab : a < b)
    (harc : MapsTo (circleMap c r) (Ioo a b) (Φ0)) :
    ∃ G : ℝ → ℂ, Continuous G ∧
      EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] a) (𝓝 (G a)) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] b) (𝓝 (G b)) := by
  let t := (a + b) / 2
  have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
  let V := riemannCapDerivative F c r
  have hVi :=
    riemannCapDerivative_intervalIntegrable F c r hi
  let G : ℝ → ℂ := fun θ => F (circleMap c r t) + ∫ s in t..θ, V s
  have hGc : Continuous G := continuous_const.add
    (intervalIntegral.continuous_primitive hVi t)
  have hGd : ∀ θ ∈ Ioo a b, HasDerivAt G (V θ) θ := by
    intro θ hθ
    simpa [G] using (intervalIntegral.integral_hasDerivAt_right (hVi t θ) (riemannCapDerivative_measurable F c r).aestronglyMeasurable.stronglyMeasurableAtFilter (by
      apply (show ContinuousAt (fun t => deriv F (circleMap c r t) * (circleMap 0 r t * Complex.I)) θ by
        exact (((hF.deriv isOpen_ball).continuousOn.continuousAt
          (isOpen_ball.mem_nhds (harc hθ))).comp (continuous_circleMap c r).continuousAt).mul
            ((continuous_circleMap 0 r).continuousAt.mul_const Complex.I)).congr
      have hmem : ∀ᶠ t in 𝓝 θ, circleMap c r t ∈ Φ0 :=
        (continuous_circleMap c r).continuousAt.preimage_mem_nhds
          (isOpen_ball.mem_nhds (harc hθ))
      filter_upwards [hmem] with t ht
      simp [riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem ht])).const_add (F (circleMap c r t))
  have hfd : ∀ θ ∈ Ioo a b,
      HasDerivAt (fun s => F (circleMap c r s)) (V θ) θ :=
    fun θ hθ => riemannCapDerivative_hasDerivAt F hF c r θ (harc hθ)
  have heq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun θ hθ => (hGd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => (hfd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => by rw [(hGd θ hθ).deriv, (hfd θ hθ).deriv]) ht
    simp [G]
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
theorem riemannMapping_cap_extension_subarc_displacement F
    (hF : DifferentiableOn ℂ F (Φ0))
    c r
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    
    (harc : MapsTo (circleMap c r) (Ioo a b) (Φ0))
     (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b))
     (hθ : θ ∈ Icc a b) (hτ : τ ∈ Icc a b) (hθτ : θ ≤ τ) :
    ‖G τ - G θ‖ ≤ ∫ s in θ..τ, ‖riemannCapDerivative F c r s‖ := by
  have hsub : Ioo θ τ ⊆ Ioo a b := by
    intro s hs
    exact ⟨hθ.1.trans_lt hs.1, hs.2.trans_le hτ.2⟩
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

/-- A finite image limit at a boundary source point belongs to the
physical frontier. The genuine holomorphic interior inverse rules out
an interior image limit. -/
theorem riemannMapping_limit_mem_frontier {A : Type*} {l} [NeBot l]
    F (hF : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0))
    {z : A → ℂ} {ζ w : ℂ} (hζ : ‖ζ‖ = 1)
    (hzin : ∀ᶠ x in l, z x ∈ Φ0)
    (hz : Tendsto z l (𝓝 ζ)) (hw : Tendsto (fun x => F (z x)) l (𝓝 w)) :
    w ∈ frontier (F '' Φ0) := by
  rw [(RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball 0 1).isPreconnected hF hinj subset_rfl isOpen_ball).frontier_eq]
  refine ⟨mem_closure_of_tendsto hw (hzin.mono fun x hx => mem_image_of_mem F hx), ?_⟩
  intro hwin
  obtain ⟨J, hJ, hJmap, hJF, _⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball 0 1).isPreconnected hF hinj
  have hJlim :=
    (hJ.continuousOn w hwin).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hw, (hzin.mono fun x hx => mem_image_of_mem F hx)⟩)
  have hJz := hJlim.congr' (hzin.mono fun x hx => hJF _ hx)
  have heq := tendsto_nhds_unique hz hJz
  have hmem := hJmap hwin
  rw [mem_ball_zero_iff, ← heq, hζ] at hmem
  linarith

/-- The inward central angle of the circular cap based at `ζ`. -/
def riemannCapCenterAngle (ζ : ℂ) : ℝ := Complex.arg (-ζ)

/-- The exact half-angle cut out by the open unit disk. -/
def riemannCapHalfAngle (r : ℝ) : ℝ := Real.arccos (r / 2)

private theorem riemannCap_circle_norm_sq  (hζ : ‖ζ‖ = 1) r θ :
    ‖circleMap ζ r (riemannCapCenterAngle ζ + θ)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos θ := by
  have h_inl r θ : circleMap ζ r (riemannCapCenterAngle ζ + θ) = ζ * (1 - circleMap 0 r θ) := by
    simp [circleMap, add_mul, Complex.exp_add, show Complex.exp ((riemannCapCenterAngle ζ) * Complex.I) = -ζ by
      simpa [riemannCapCenterAngle, hζ]
        using Complex.norm_mul_exp_arg_mul_I (-ζ)]
    ring
  rw [h_inl, norm_mul, hζ, one_mul,
    ← Complex.normSq_eq_norm_sq]
  calc
    _ =
        (1 - r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
      simp [circleMap, Complex.normSq_apply, pow_two]
    _ = 1 + r ^ 2 - 2 * r * Real.cos θ := by
      linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ

/-- The entire open cap, including its exact angular endpoints, is
determined directly from the unit disk geometry. -/
theorem riemannCap_geometry  (hζ : ‖ζ‖ = 1) 
    (hr : 0 < r) (hr1 : r < 1) :
    let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
    let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
    a < b ∧ b ≤ a + 2 * Real.pi ∧
      MapsTo (circleMap ζ r) (Ioo a b) (Φ0) ∧
      ‖circleMap ζ r a‖ = 1 ∧ ‖circleMap ζ r b‖ = 1 := by
  let α := riemannCapHalfAngle r
  have hα : 0 < α := Real.arccos_pos.2 (by linarith)
  have hαπ : α ≤ Real.pi := Real.arccos_le_pi _
  have hc : Real.cos α = r / 2 := Real.cos_arccos (by linarith) (by linarith)
  dsimp
  refine ⟨by dsimp [α] at hα; linarith,
    by dsimp [α] at hαπ; linarith, ?_, ?_, ?_⟩
  · intro θ hθ
    let u := θ - riemannCapCenterAngle ζ
    have hcos : r / 2 < Real.cos u := by
      rw [← hc, ← Real.cos_abs u]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ (abs_lt.2 ⟨by dsimp [u, α]; linarith [hθ.1], by dsimp [u, α]; linarith [hθ.2]⟩)
    rw [mem_ball_zero_iff]
    apply (sq_lt_one_iff₀ (norm_nonneg _)).1
    have heq : θ = riemannCapCenterAngle ζ + u := by dsimp [u]; ring
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

end PolyaNeumann

end
