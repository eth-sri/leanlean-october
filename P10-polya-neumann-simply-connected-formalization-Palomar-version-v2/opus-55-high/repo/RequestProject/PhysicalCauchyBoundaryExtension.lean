module

public import RequestProject.PhysicalCauchyBase
public import RequestProject.LocalConformalBoundaryLipschitz
public import RequestProject.LocalConformalBoundaryGeometry
public import Mathlib.Topology.Piecewise

/-!
# All-approach physical Cauchy boundary extension

A nearest point on the actual compact physical curve supplies a uniformly
dominated Cauchy commutator.  A physical chord bound for the density then gives
its full boundary limit, with no restriction to a normal or radial approach.
The supplied smooth inverse coordinate proves that chord bound for the actual
C¹ periodic physical moment primitive.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Topology


variable {Ω : Set ℂ} (γ : ℝ → ℂ) (hγ : Continuous γ) (w : ℂ) (θ : ℝ) (K : ℝ → ℂ) {L : ℝ}

theorem exists_nearestPhysicalBoundaryParam (hγ : Continuous γ) (w : ℂ) :
    ∃ τ ∈ Icc 0 (2 * Real.pi),
      ∀ θ ∈ Icc 0 (2 * Real.pi), ‖γ τ - w‖ ≤ ‖γ θ - w‖ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, Real.two_pi_pos.le⟩
    (hγ.sub continuous_const).norm.continuousOn

/-- A choice of an actual nearest physical boundary parameter.  Continuity
of this parameter choice is neither asserted nor needed. -/
def nearestPhysicalBoundaryParam (γ : ℝ → ℂ) (hγ : Continuous γ) (w : ℂ) : ℝ :=
  Classical.choose (exists_nearestPhysicalBoundaryParam γ hγ w)

theorem nearestPhysicalBoundaryParam_min (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ ≤ ‖γ θ - w‖ :=
  (Classical.choose_spec (exists_nearestPhysicalBoundaryParam γ hγ w)).2 θ hθ

def nearestPhysicalBoundaryDensity (γ : ℝ → ℂ) (hγ : Continuous γ)
    (K : ℝ → ℂ) (w : ℂ) : ℂ := K (nearestPhysicalBoundaryParam γ hγ w)

/-- The nearest physical point is at most twice as far along a chord from
any comparison point as the approaching point is from that comparison point. -/
theorem nearestPhysicalBoundaryParam_chord_le (γ : ℝ → ℂ) (hγ : Continuous γ)
    (w : ℂ) (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    ‖γ θ - γ (nearestPhysicalBoundaryParam γ hγ w)‖ ≤ 2 * ‖γ θ - w‖ := by
  calc
    _ = ‖(γ θ - w) + (w - γ (nearestPhysicalBoundaryParam γ hγ w))‖ := by
      ring
    _ ≤ ‖γ θ - w‖ + ‖w - γ (nearestPhysicalBoundaryParam γ hγ w)‖ := norm_add_le _ _
    _ = ‖γ θ - w‖ + ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ := by
      rw [norm_sub_rev w]
    _ ≤ ‖γ θ - w‖ + ‖γ θ - w‖ := add_le_add le_rfl (nearestPhysicalBoundaryParam_min γ hγ w θ hθ)
    _ = _ := by ring

theorem nearestPhysicalBoundaryDensity_norm_sub_le
    (γ : ℝ → ℂ) (hγ : Continuous γ) (K : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (w : ℂ) (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
    ‖nearestPhysicalBoundaryDensity γ hγ K w - K t‖ ≤ (2 * L) * ‖w - γ t‖ := by
  calc
    _ = ‖K t - K (nearestPhysicalBoundaryParam γ hγ w)‖ := by
      rw [nearestPhysicalBoundaryDensity, norm_sub_rev]
    _ ≤ L * ‖γ t - γ (nearestPhysicalBoundaryParam γ hγ w)‖ := hchord _ _
    _ ≤ L * (2 * ‖γ t - w‖) := mul_le_mul_of_nonneg_left
      (nearestPhysicalBoundaryParam_chord_le γ hγ w t ht) hL
    _ = _ := by rw [norm_sub_rev (γ t)]; ring

/-- Although the nearest parameter need not be continuous, its actual
physical density tends to the prescribed density at every boundary point. -/
theorem nearestPhysicalBoundaryDensity_tendsto
    (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
    Tendsto (nearestPhysicalBoundaryDensity γ hγ K) (𝓝 (γ t)) (𝓝 (K t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun w => norm_nonneg _) (fun w =>
    nearestPhysicalBoundaryDensity_norm_sub_le γ hγ K hL hchord w t ht)
  have hn : Tendsto (fun w  => ‖w - γ t‖) (𝓝 (γ t)) (𝓝 0) :=
    (continuous_id.sub continuous_const).norm.tendsto' (γ t) 0 (by simp)
  simpa only [mul_zero] using tendsto_const_nhds.mul hn

theorem nearestPhysicalBoundaryDensity_at_trace
    (γ : ℝ → ℂ) (hγ : Continuous γ) (K : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
    nearestPhysicalBoundaryDensity γ hγ K (γ t) = K t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa only [sub_self, norm_zero, mul_zero] using
      nearestPhysicalBoundaryDensity_norm_sub_le γ hγ K hL hchord (γ t) t ht
  positivity

/-- The physical Cauchy commutator with the actual nearest-point density. -/
def physicalNearestCauchyCommutator (γ : ℝ → ℂ) (hγ : Continuous γ)
    (K : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ K w)) / (γ θ - w)

/-- Every approach to an actual boundary point has the same commutator
limit.  The nearest-point construction proves a global integrable bound
`2 L sup |γ'|`; no selection continuity or boundary jump is assumed. -/
theorem physicalNearestCauchyCommutator_tendsto
    (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : Continuous K)
    {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hinj : InjOn γ (Ico 0 (2 * Real.pi)))
    (t : ℝ) (ht : t ∈ Ico 0 (2 * Real.pi)) :
    Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t))
      (𝓝 (∫ θ in 0..(2 * Real.pi),
        (deriv γ θ * (K θ - K t)) / (γ θ - γ t))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
     hγ.continuous_deriv_one.continuousOn
  have hM0  := (norm_nonneg (deriv γ 0)).trans
    (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hbound (w : ℂ) (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
      ‖(deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w)) /
        (γ θ - w)‖ ≤ M * (2 * L) := by
    by_cases hd : γ θ - w = 0
    · rw [hd, div_zero, norm_zero]
      positivity
    · rw [norm_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr hd)).mpr
      calc
        _ = ‖deriv γ θ‖ *
            ‖K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w‖ := norm_mul _ _
        _ ≤ M * ‖K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w‖ :=
          mul_le_mul_of_nonneg_right (hM θ hθ) (norm_nonneg _)
        _ ≤ M * ((2 * L) * ‖γ θ - w‖) := mul_le_mul_of_nonneg_left (by
      calc
        _ ≤ L * ‖γ θ - γ (nearestPhysicalBoundaryParam γ hγ.continuous w)‖ :=
          hchord _ _
        _ ≤ L * (2 * ‖γ θ - w‖) := mul_le_mul_of_nonneg_left
          (nearestPhysicalBoundaryParam_chord_le γ hγ.continuous w θ hθ) hL
        _ = _ := by ring) hM0
        _ = _ := by ring
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
     (bound := fun _  => M * (2 * L))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun w =>
      ((hγ.continuous_deriv_one.measurable.mul (hK.measurable.sub measurable_const)).div
        (hγ.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun w => Eventually.of_forall fun θ hθ => by
      grind
  · filter_upwards [volume.ae_ne t, volume.ae_ne (2 * Real.pi)] with θ hθt hθL
    intro hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub (nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
    t (Ico_subset_Icc_self ht)))).div ((continuous_const.sub continuous_id).tendsto (γ t)) (sub_ne_zero.mpr
      (fun he => hθt (hinj ⟨hθ.1.le, lt_of_le_of_ne hθ.2 hθL⟩ ht he)))

/-- Actual Cauchy decomposition about an arbitrary constant density. -/
theorem physicalWeightedCauchy_eq_subtract_constant
    (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : Continuous K)
    (c w : ℂ) (havoid : ∀ θ ∈ Icc 0 (2 * Real.pi), γ θ ≠ w) :
    physicalWeightedCauchy γ K w =
      (∫ θ in 0..(2 * Real.pi), (deriv γ θ * (K θ - c)) / (γ θ - w)) +
        (2 * Real.pi * Complex.I) * c * windingNumber γ w := by
  let f  := fun θ => (deriv γ θ * (K θ - c)) / (γ θ - w)
  let q  := fun θ => deriv γ θ / (γ θ - w)
  have hq : IntervalIntegrable q volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact hγ.continuous_deriv_one.continuousOn.div
      (hγ.continuous.sub continuous_const).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))
  have heq : (fun θ => (deriv γ θ * K θ) / (γ θ - w)) =
      (fun θ => f θ + c * q θ) := by
    grind
  have hconst : (2 * Real.pi * Complex.I) * c * windingNumber γ w =
      c * ∫ θ in 0..(2 * Real.pi), q θ := by
    change (2 * Real.pi * Complex.I) * c *
      ((2 * Real.pi * Complex.I)⁻¹ * ∫ θ in 0..(2 * Real.pi), q θ) = _
    field_simp 
  rw [hconst, physicalWeightedCauchy, heq,
    intervalIntegral.integral_add (by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact (hγ.continuous_deriv_one.mul (hK.sub continuous_const)).continuousOn.div
      (hγ.continuous.sub continuous_const).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))) (hq.const_mul c), intervalIntegral.integral_const_mul]

theorem physicalWeightedCauchy_eq_nearestCommutator_add_winding
    (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : Continuous K)
    (w : ℂ) (havoid : ∀ θ ∈ Icc 0 (2 * Real.pi), γ θ ≠ w) :
    physicalWeightedCauchy γ K w = physicalNearestCauchyCommutator γ hγ.continuous K w +
      (2 * Real.pi * Complex.I) * nearestPhysicalBoundaryDensity γ hγ.continuous K w *
        windingNumber γ w :=
  physicalWeightedCauchy_eq_subtract_constant γ hγ K hK
    (nearestPhysicalBoundaryDensity γ hγ.continuous K w) w havoid

/-- Holomorphicity of the genuine weighted physical integral away from the
curve follows from the already-proved differentiated ordinary integral. -/
theorem physicalWeightedCauchy_differentiableAt
    (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : Continuous K)
    (w : ℂ) (havoid : ∀ θ ∈ Icc 0 (2 * Real.pi), γ θ ≠ w) :
    DifferentiableAt ℂ (physicalWeightedCauchy γ K) w := by
  have heq : physicalWeightedCauchy γ K =
      fun z => -physicalOrdinaryCauchy γ (fun θ => conj (K θ)) z := by
    simp [physicalOrdinaryCauchy_eq_neg_weighted] 
  rw [heq]
  exact (physicalOrdinaryCauchy_hasDerivAt γ (fun θ => conj (K θ)) hγ
    (Complex.continuous_conj.comp hK) havoid).differentiableAt.neg

private theorem physicalCurve_avoid_of_notMem_frontier
    (him : γ '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω)
    {w : ℂ} (hw : w ∉ frontier Ω) :
    ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ w := by
  grind

/-- A genuine Lipschitz boundary point is approachable from the exterior.
This is derived from the already-proved actual chart box. -/
theorem frontier_mem_closure_physicalExterior (hL : IsLipschitzDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) : p ∈ closure ((closure Ω)ᶜ) := by
  obtain ⟨V, B, _, hpV, _, hBE, _, hcl⟩ := exists_exterior_box hL hp
  exact closure_mono hBE (hcl p ⟨hp, hpV⟩)

private theorem physicalFrontier_parameter_Ico
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (him : γ '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ t ∈ Ico (0 : ℝ) (2 * Real.pi), γ t = p := by
  rw [← him] at hp
  obtain ⟨t, ht, heq⟩ := hp
  by_cases htL : t = 2 * Real.pi
  · refine ⟨0, ⟨le_rfl, Real.two_pi_pos⟩, ?_⟩
    rw [← heq, htL]
    simpa only [zero_add] using (hpγ 0).symm
  grind

/-- Exterior vanishing forces the full boundary commutator limit to be zero.
Actual exterior approachability supplies the nontrivial limit filter. -/
theorem physicalNearestCauchyCommutator_tendsto_zero_of_exterior
    {Ω : Set ℂ} (hΩ : IsLipschitzDomain Ω)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (him : γ '' Icc 0 (2 * Real.pi) = frontier Ω)
    (hinj : InjOn γ (Ico 0 (2 * Real.pi)))
    (K : ℝ → ℂ) (hK : Continuous K) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hzero : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ K w = 0)
    (hwind : ∀ w : ℂ, w ∉ closure Ω → windingNumber γ w = 0)
    (t : ℝ) (ht : t ∈ Ico 0 (2 * Real.pi)) :
    Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t)) (𝓝 0) := by
  have hRzero : ∀ w : ℂ, w ∉ closure Ω →
      physicalNearestCauchyCommutator γ hγ.continuous K w = 0 := by
    intro w hw
    have heq := physicalWeightedCauchy_eq_nearestCommutator_add_winding γ hγ K hK w (physicalCurve_avoid_of_notMem_frontier γ him
      (fun hfront => hw (frontier_subset_closure hfront)))
    simp_all
  haveI  :=
    mem_closure_iff_nhdsWithin_neBot.mp (frontier_mem_closure_physicalExterior hΩ (by
    rw [← him]
    exact mem_image_of_mem γ (Ico_subset_Icc_self ht)))
  have hlim := physicalNearestCauchyCommutator_tendsto γ hγ K hK hL hchord hinj t ht
  have heq : physicalNearestCauchyCommutator γ hγ.continuous K =ᶠ[𝓝[(closure Ω)ᶜ] (γ t)]
      fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp_all
  have hz := tendsto_nhds_unique (hlim.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)
  simp_all

/-- The actual Jordan winding theorem and the all-approach commutator prove
a continuous holomorphic extension of the prescribed physical density.
Only exterior vanishing of its genuine Cauchy integral is an analytic premise;
it will be supplied by the actual physical moment primitive below. -/
theorem exists_physicalCauchy_boundary_extension
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi)))
    (him : γ '' Icc 0 (2 * Real.pi) = frontier Ω)
    (K : ℝ → ℂ) (hK : Continuous K) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hzero : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ K w = 0) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ Icc 0 (2 * Real.pi), G (γ θ) = K θ := by
  classical
  obtain ⟨_, hLip⟩ := exists_periodic_C1_density_lipschitz γ hγ hpγ
  obtain ⟨σ, hσ, hinside, houtside⟩ := windingNumber_pm_one_of_jordan hb hΩ hLip hpγ
    hinj him (isConnected_compl_closure_of_frontier hb hΩ hfc)
  have hσC : (σ : ℂ) ≠ 0 := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  let a  := (2 * Real.pi * Complex.I) * σ
  let N  := nearestPhysicalBoundaryDensity γ hγ.continuous K
  let R  := physicalNearestCauchyCommutator γ hγ.continuous K
  let G  := fun w => if w ∈ Ω then physicalWeightedCauchy γ K w / a else N w
  have hΩo  := hΩ.1.1
  have hav (w : ℂ) (hw : w ∈ Ω) :
      ∀ θ ∈ Icc 0 (2 * Real.pi), γ θ ≠ w := by
    apply physicalCurve_avoid_of_notMem_frontier γ him
    simp_all [hΩo.frontier_eq]
  have hdiff (w : ℂ) (hw : w ∈ Ω) : DifferentiableAt ℂ G w := by
    apply ((physicalWeightedCauchy_differentiableAt γ hγ K hK w (hav w hw)).div_const a).congr_of_eventuallyEq
    filter_upwards [hΩo.mem_nhds hw] with z hz
    grind
  have htrace (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) : G (γ θ) = K θ := by
    have hpnot : γ θ ∉ Ω := by
      grind
    simp only [G, if_neg hpnot]
    exact nearestPhysicalBoundaryDensity_at_trace γ hγ.continuous K hL hchord θ hθ
  refine ⟨G, ⟨fun w hw => (hdiff w hw).differentiableWithinAt, ?_⟩, htrace⟩
  intro p hpcl
  by_cases hpΩ : p ∈ Ω
  · exact (hdiff p hpΩ).continuousAt.continuousWithinAt
  · obtain ⟨t, ht, rfl⟩ := physicalFrontier_parameter_Ico γ hpγ him (by
      rw [hΩo.frontier_eq]
      trivial)
    have hN := nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
      t (Ico_subset_Icc_self ht)
    have haux : Tendsto (fun w  => R w / a + N w) (𝓝 (γ t)) (𝓝 (K t)) := by
      simpa only [zero_div, zero_add] using ((physicalNearestCauchyCommutator_tendsto_zero_of_exterior hΩ γ hγ him hinj
      K hK hL hchord hzero houtside t ht).div_const a).add hN
    have hf : Tendsto (fun w  => physicalWeightedCauchy γ K w / a)
        (𝓝[closure Ω ∩ Ω] (γ t)) (𝓝 (K t)) := by
      apply Tendsto.congr' ?_ (haux.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [physicalWeightedCauchy_eq_nearestCommutator_add_winding
        γ hγ K hK w (hav w hw.2), hinside w hw.2]
      dsimp only [R, N, a]
      field_simp 
    change Tendsto G (𝓝[closure Ω] (γ t)) (𝓝 (G (γ t)))
    rw [htrace t (Ico_subset_Icc_self ht)]
    exact hf.if_nhdsWithin (p := fun w => w ∈ Ω) (hN.mono_left nhdsWithin_le_nhds)

/-- Actual physical antiholomorphic moments yield an actual continuous
holomorphic extension of the conjugated primitive.  The inverse collar
supplies the proved density chord bound, while the given physical domain
supplies the Jordan winding and exterior connectedness theorems. -/
theorem exists_localConformal_physicalMomentPrimitive_extension
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball 0 1 = Ω)
    (H : ℝ → ℂ) (hH : Continuous H)
    (hpH : Function.Periodic H (2 * Real.pi))
    (hmom : ∀ m : ℕ, (∫ θ in 0..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ Icc 0 (2 * Real.pi),
        G (physicalCircleTrace F θ) =
          conj (physicalMomentPrimitive (physicalCircleTrace F) H θ) := by
  let γ := physicalCircleTrace F
  let K := physicalMomentPrimitive γ H
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpγ  := physicalCircleTrace_periodic F
  have hK  := contDiff_physicalMomentPrimitive γ H hγ hH
  have him : γ '' Icc 0 (2 * Real.pi) = frontier Ω := by
    simpa only [himage] using localConformal_circleTrace_image_frontier hR F hFs hinj (himage.symm ▸ hΩ.1.1)
  have hfc : IsPreconnected (frontier Ω) := by
    rw [← him]
    exact isPreconnected_Icc.image γ hγ.continuous.continuousOn
  obtain ⟨L, hL, hchord⟩ :=
    exists_localConformal_boundaryDensity_chord_bound_of_nonzeroDifferential
      hR F hFs hhol hinj hnz K hK (by
    apply physicalMomentPrimitive_periodic γ H hγ hH hpγ hpH
    simpa only [pow_zero, mul_one] using hmom 0)
  have hconjchord (θ τ : ℝ) : ‖conj (K θ) - conj (K τ)‖ ≤ L * ‖γ θ - γ τ‖ := by
    rw [← map_sub, Complex.norm_conj]
    grind
  exact exists_physicalCauchy_boundary_extension hb hΩ hfc γ hγ hpγ
    (physicalCircleTrace_injOn_of_closedDisk_inj F hinj) him
    (fun θ => conj (K θ)) (Complex.continuous_conj.comp hK.continuous)
    hL hconjchord (by
    intro w hw
    have hzero : physicalOrdinaryCauchy γ K w = 0 := by
      rw [physicalOrdinaryCauchy_eq_conj,
        physicalMomentPrimitive_exterior_eq_zero hb hΩ hfc γ H hγ hH him hmom w hw,
        map_zero]
    simp_all [physicalOrdinaryCauchy_eq_neg_weighted])

end PolyaNeumann

end
