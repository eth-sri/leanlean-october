module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Topology



theorem exists_nearestPhysicalBoundaryParam γ (hγ : Continuous γ) (w : ℂ) :
    ∃ τ ∈ boundaryInterval,
      ∀ θ ∈ boundaryInterval, ‖γ τ - w‖ ≤ ‖γ θ - w‖ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, Real.two_pi_pos.le⟩
    (hγ.sub continuous_const).norm.continuousOn

/-- A choice of an actual nearest physical boundary parameter.  Continuity
of this parameter choice is neither asserted nor needed. -/
def nearestPhysicalBoundaryParam γ hγ w  :=
  Classical.choose (exists_nearestPhysicalBoundaryParam γ hγ w)

section
variable (γ : ComplexCurve) (hγ : Continuous γ) (w : ℂ) (θ ) (hθ : θ ∈ boundaryInterval)

include γ hγ w θ hθ in
theorem nearestPhysicalBoundaryParam_min :
    ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ ≤ ‖γ θ - w‖ :=
  (Classical.choose_spec (exists_nearestPhysicalBoundaryParam γ hγ w)).2 θ hθ

def nearestPhysicalBoundaryDensity γ hγ
    (K : ComplexCurve) w  := K (nearestPhysicalBoundaryParam γ hγ w)

include γ hγ w θ hθ in
/-- The nearest physical point is at most twice as far along a chord from
any comparison point as the approaching point is from that comparison point. -/
theorem nearestPhysicalBoundaryParam_chord_le :
    ‖γ θ - γ (nearestPhysicalBoundaryParam γ hγ w)‖ ≤ 2 * ‖γ θ - w‖ := by
  have hm := nearestPhysicalBoundaryParam_min γ hγ w θ hθ
  calc
    _ = ‖(γ θ - w) + (w - γ (nearestPhysicalBoundaryParam γ hγ w))‖ := by
      ring
    _ ≤ ‖γ θ - w‖ + ‖w - γ (nearestPhysicalBoundaryParam γ hγ w)‖ := norm_add_le _ _
    _ = ‖γ θ - w‖ + ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ := by
      rw [norm_sub_rev w]
    _ ≤ ‖γ θ - w‖ + ‖γ θ - w‖ := add_le_add le_rfl hm
    _ = _ := by ring

end


section
variable (γ : ComplexCurve) (hγ : Continuous γ) (K : ComplexCurve) {L } (hL : 0 ≤ L) (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
include γ hγ K L hL hchord

theorem nearestPhysicalBoundaryDensity_norm_sub_le
    w t (ht : t ∈ boundaryInterval) :
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
    t (ht : t ∈ boundaryInterval) :
    Tendsto (nearestPhysicalBoundaryDensity γ hγ K) (𝓝 (γ t)) (𝓝 (K t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun w => norm_nonneg _) (fun w =>
    nearestPhysicalBoundaryDensity_norm_sub_le γ hγ K hL hchord w t ht)
  have hn : Tendsto (fun w : ℂ => ‖w - γ t‖) (𝓝 (γ t)) (𝓝 0) :=
    (continuous_id.sub continuous_const).norm.tendsto' (γ t) 0 (by simp)
  simpa   using (tendsto_const_nhds.mul hn)

theorem nearestPhysicalBoundaryDensity_at_trace
    t (ht : t ∈ boundaryInterval) :
    nearestPhysicalBoundaryDensity γ hγ K (γ t) = K t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa   using
      nearestPhysicalBoundaryDensity_norm_sub_le γ hγ K hL hchord (γ t) t ht
  · exact norm_nonneg _

end


/-- The physical Cauchy commutator with the actual nearest-point density. -/
def physicalNearestCauchyCommutator γ hγ
    K w  :=
  ∫ θ in (0 : ℝ)..circlePeriod,
    (deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ K w)) / (γ θ - w)

section
variable (γ : ComplexCurve) (hγ : ContDiff ℝ 1 γ) (K : ComplexCurve) (hK : Continuous K)
include γ hγ K hK

/-- Every approach to an actual boundary point has the same commutator
limit.  The nearest-point construction proves a global integrable bound
`2 L sup |γ'|`; no selection continuity or boundary jump is assumed. -/
theorem physicalNearestCauchyCommutator_tendsto
     (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hinj : InjOn γ (Ico (0 : ℝ) circlePeriod))
    t (ht : t ∈ Ico (0 : ℝ) circlePeriod) :
    Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t))
      (𝓝 (∫ θ in (0 : ℝ)..circlePeriod,
        (deriv γ θ * (K θ - K t)) / (γ θ - γ t))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 circlePeriod) hγ.continuous_deriv_one.continuousOn
  have hM0  := (norm_nonneg (deriv γ 0)).trans
    (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hbound (w : ℂ) (θ : ℝ) (hθ : θ ∈ boundaryInterval) :
      ‖(deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w)) /
        (γ θ - w)‖ ≤ M * (2 * L) := by
    have hKθ : ‖K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w‖ ≤
        (2 * L) * ‖γ θ - w‖ := by
      calc
        _ ≤ L * ‖γ θ - γ (nearestPhysicalBoundaryParam γ hγ.continuous w)‖ :=
          hchord _ _
        _ ≤ L * (2 * ‖γ θ - w‖) := mul_le_mul_of_nonneg_left
          (nearestPhysicalBoundaryParam_chord_le γ hγ.continuous w θ hθ) hL
        _ = _ := by ring
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
        _ ≤ M * ((2 * L) * ‖γ θ - w‖) := mul_le_mul_of_nonneg_left hKθ hM0
        _ = _ := by ring
  have hN := nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
    t (Ico_subset_Icc_self ht)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ : ℝ => M * (2 * L))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun w =>
      ((hγ.continuous_deriv_one.measurable.mul (hK.measurable.sub measurable_const)).div
        (hγ.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun w => Eventually.of_forall fun θ hθ => by
      grind
  · filter_upwards [volume.ae_ne t, volume.ae_ne circlePeriod] with θ hθt hθL
    intro hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    have hθ' : θ ∈ Ico (0 : ℝ) circlePeriod :=
      ⟨hθ.1.le, lt_of_le_of_ne hθ.2 hθL⟩
    have hd  := sub_ne_zero.mpr
      (fun he => hθt (hinj hθ' ht he))
    have hden : Tendsto (fun w : ℂ => γ θ - w) (𝓝 (γ t)) (𝓝 (γ θ - γ t)) :=
      (continuous_const.sub continuous_id).tendsto (γ t)
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub hN)).div hden hd

/-- Actual Cauchy decomposition about an arbitrary constant density. -/
theorem physicalWeightedCauchy_eq_subtract_constant
    c w (havoid : ∀ θ ∈ boundaryInterval, γ θ ≠ w) :
    physicalWeightedCauchy γ K w =
      (∫ θ in (0 : ℝ)..circlePeriod, (deriv γ θ * (K θ - c)) / (γ θ - w)) +
        (2 * Real.pi * Complex.I) * c * windingNumber γ w := by
  let f  := fun θ => (deriv γ θ * (K θ - c)) / (γ θ - w)
  let q  := fun θ => deriv γ θ / (γ θ - w)
  have hf : IntervalIntegrable f volume 0 circlePeriod := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact (hγ.continuous_deriv_one.mul (hK.sub continuous_const)).continuousOn.div
      (hγ.continuous.sub continuous_const).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))
  have hq : IntervalIntegrable q volume 0 circlePeriod := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact hγ.continuous_deriv_one.continuousOn.div
      (hγ.continuous.sub continuous_const).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))
  have heq : (fun θ => (deriv γ θ * K θ) / (γ θ - w)) =
      (fun θ => f θ + c * q θ) := by
    funext θ
    ring
  have ha : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp 
  have hconst : (2 * Real.pi * Complex.I) * c * windingNumber γ w =
      c * ∫ θ in (0 : ℝ)..circlePeriod, q θ := by
    grind only [windingNumber]
  rw [hconst, physicalWeightedCauchy, heq,
    intervalIntegral.integral_add hf (hq.const_mul c), intervalIntegral.integral_const_mul]

section
variable (w ) (havoid : ∀ θ ∈ boundaryInterval, γ θ ≠ w)
include w havoid

theorem physicalWeightedCauchy_eq_nearestCommutator_add_winding :
    physicalWeightedCauchy γ K w = physicalNearestCauchyCommutator γ hγ.continuous K w +
      (2 * Real.pi * Complex.I) * nearestPhysicalBoundaryDensity γ hγ.continuous K w *
        windingNumber γ w :=
  physicalWeightedCauchy_eq_subtract_constant γ hγ K hK
    (nearestPhysicalBoundaryDensity γ hγ.continuous K w) w havoid

/-- Holomorphicity of the genuine weighted physical integral away from the
curve follows from the already-proved differentiated ordinary integral. -/
theorem physicalWeightedCauchy_differentiableAt :
    DifferentiableAt ℂ (physicalWeightedCauchy γ K) w := by
  have heq : physicalWeightedCauchy γ K =
      fun z => -physicalOrdinaryCauchy γ (fun θ => conj (K θ)) z := by
    funext z
    rw [physicalOrdinaryCauchy_eq_neg_weighted]
    simp  
  rw [heq]
  exact (physicalOrdinaryCauchy_hasDerivAt γ (fun θ => conj (K θ)) hγ
    (Complex.continuous_conj.comp hK) havoid).differentiableAt.neg

end


end


section
variable {Ω : PlanarSet}
include Ω

private theorem physicalCurve_avoid_of_notMem_frontier γ
    (him : γ '' boundaryInterval = frontier Ω)
     (hw : w ∉ frontier Ω) :
    ∀ θ ∈ boundaryInterval, γ θ ≠ w := by
  grind

private theorem physicalFrontier_parameter_Ico γ (hpγ : Function.Periodic γ circlePeriod)
    (him : γ '' boundaryInterval = frontier Ω)
     (hp : p ∈ frontier Ω) :
    ∃ t ∈ Ico (0 : ℝ) circlePeriod, γ t = p := by
  rw [← him] at hp
  obtain ⟨t, ht, heq⟩ := hp
  by_cases htL : t = 2 * Real.pi
  · refine ⟨0, ⟨le_rfl, Real.two_pi_pos⟩, ?_⟩
    rw [← heq, htL]
    simpa   using (hpγ 0).symm
  grind

/-- Exterior vanishing forces the full boundary commutator limit to be zero.
Actual exterior approachability supplies the nontrivial limit filter. -/
theorem physicalNearestCauchyCommutator_tendsto_zero_of_exterior (hΩ : IsLipschitzDomain Ω)
    γ (hγ : ContDiff ℝ 1 γ)
    (him : γ '' boundaryInterval = frontier Ω)
    (hinj : InjOn γ (Ico (0 : ℝ) circlePeriod))
    K (hK : Continuous K)  (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hzero : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ K w = 0)
    (hwind : ∀ w : ℂ, w ∉ closure Ω → windingNumber γ w = 0)
    t (ht : t ∈ Ico (0 : ℝ) circlePeriod) :
    Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t)) (𝓝 0) := by
  have hp : γ t ∈ frontier Ω := by
    grind
  have hRzero : ∀ w : ℂ, w ∉ closure Ω →
      physicalNearestCauchyCommutator γ hγ.continuous K w = 0 := by
    intro w hw
    have hav := physicalCurve_avoid_of_notMem_frontier γ him
      (fun hfront => hw (frontier_subset_closure hfront))
    grind only [physicalWeightedCauchy_eq_nearestCommutator_add_winding]
  haveI  :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_compl_closure hΩ hp)
  have hlim := physicalNearestCauchyCommutator_tendsto γ hγ K hK hL hchord hinj t ht
  have heq : physicalNearestCauchyCommutator γ hγ.continuous K =ᶠ[𝓝[(closure Ω)ᶜ] (γ t)]
      0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hRzero w hw
  have hout  := tendsto_const_nhds.congr' heq.symm
  have hz := tendsto_nhds_unique (hlim.mono_left nhdsWithin_le_nhds) hout
  rw [hz] at hlim
  exact hlim

/-- The actual Jordan winding theorem and the all-approach commutator prove
a continuous holomorphic extension of the prescribed physical density.
Only exterior vanishing of its genuine Cauchy integral is an analytic premise;
it will be supplied by the actual physical moment primitive below. -/
theorem exists_physicalCauchy_boundary_extension (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    γ (hγ : ContDiff ℝ 1 γ)
    (hpγ : Function.Periodic γ circlePeriod)
    (hinj : InjOn γ (Ico (0 : ℝ) circlePeriod))
    (him : γ '' boundaryInterval = frontier Ω)
    K (hK : Continuous K)  (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hzero : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ K w = 0) :
    ∃ G : PlaneMap, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ boundaryInterval, G (γ θ) = K θ := by
  classical
  obtain ⟨_, hLip⟩ := exists_periodic_C1_density_lipschitz γ hγ hpγ
  obtain ⟨σ, hσ, hinside, houtside⟩ := windingNumber_pm_one_of_jordan hb hΩ hLip hpγ
    hinj him (isConnected_compl_closure_of_frontier hb hΩ hfc)
  have hσC : (σ : ℂ) ≠ 0 := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  have hA : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp 
  let a  := (2 * Real.pi * Complex.I) * σ
  let N  := nearestPhysicalBoundaryDensity γ hγ.continuous K
  let R  := physicalNearestCauchyCommutator γ hγ.continuous K
  let G  := fun w => if w ∈ Ω then physicalWeightedCauchy γ K w / a else N w
  have hΩo  := hΩ.1.1
  have hav (w : ℂ) (hw : w ∈ Ω) :
      ∀ θ ∈ boundaryInterval, γ θ ≠ w := by
    apply physicalCurve_avoid_of_notMem_frontier γ him
    intro hfront
    rw [hΩo.frontier_eq] at hfront
    exact hfront.2 hw
  have hdiff (w : ℂ) (hw : w ∈ Ω) : DifferentiableAt ℂ G w := by
    have hd := (physicalWeightedCauchy_differentiableAt γ hγ K hK w (hav w hw)).div_const a
    apply hd.congr_of_eventuallyEq
    filter_upwards [hΩo.mem_nhds hw] with z hz
    simp only [G, if_pos hz]
  have htrace (θ : ℝ) (hθ : θ ∈ boundaryInterval) : G (γ θ) = K θ := by
    grind only [nearestPhysicalBoundaryDensity_at_trace]
  refine ⟨G, ⟨fun w hw => (hdiff w hw).differentiableWithinAt, ?_⟩, htrace⟩
  intro p hpcl
  by_cases hpΩ : p ∈ Ω
  · exact (hdiff p hpΩ).continuousAt.continuousWithinAt
  · have hpfront : p ∈ frontier Ω := by
      rw [hΩo.frontier_eq]
      exact ⟨hpcl, hpΩ⟩
    obtain ⟨t, ht, rfl⟩ := physicalFrontier_parameter_Ico γ hpγ him hpfront
    have hN := nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
      t (Ico_subset_Icc_self ht)
    have hR := physicalNearestCauchyCommutator_tendsto_zero_of_exterior hΩ γ hγ him hinj
      K hK hL hchord hzero houtside t ht
    have haux : Tendsto (fun w : ℂ => R w / a + N w) (𝓝 (γ t)) (𝓝 (K t)) := by
      simpa   using (hR.div_const a).add hN
    have hf : Tendsto (fun w : ℂ => physicalWeightedCauchy γ K w / a)
        (𝓝[closure Ω ∩ Ω] (γ t)) (𝓝 (K t)) := by
      apply Tendsto.congr' ?_ (haux.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with w hw
      grind [physicalWeightedCauchy_eq_nearestCommutator_add_winding]
    have hg : Tendsto N (𝓝[closure Ω ∩ Ωᶜ] (γ t)) (𝓝 (K t)) :=
      hN.mono_left nhdsWithin_le_nhds
    change Tendsto G (𝓝[closure Ω] (γ t)) (𝓝 (G (γ t)))
    rw [htrace t (Ico_subset_Icc_self ht)]
    exact hf.if_nhdsWithin (p := fun w => w ∈ Ω) hg

/-- Actual physical antiholomorphic moments yield an actual continuous
holomorphic extension of the conjugated primitive.  The inverse collar
supplies the proved density chord bound, while the given physical domain
supplies the Jordan winding and exterior connectedness theorems. -/
theorem exists_localConformal_physicalMomentPrimitive_extension (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
     (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F closedUnitDisk)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' unitDisk = Ω)
    H (hH : Continuous H)
    (hpH : Function.Periodic H circlePeriod)
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    ∃ G : PlaneMap, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ boundaryInterval,
        G (physicalCircleTrace F θ) =
          conj (physicalMomentPrimitive (physicalCircleTrace F) H θ) := by
  let γ := physicalCircleTrace F
  let K := physicalMomentPrimitive γ H
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpγ  := physicalCircleTrace_periodic F
  have hK  := contDiff_physicalMomentPrimitive γ H hγ hH
  have hpK : Function.Periodic K circlePeriod := by
    apply physicalMomentPrimitive_periodic γ H hγ hH hpγ hpH
    simpa   using hmom 0
  have hΩimage  := himage.symm ▸ hΩ.1.1
  have him : γ '' boundaryInterval = frontier Ω := by
    simpa  [himage] using localConformal_circleTrace_image_frontier hR F hFs hinj hΩimage
  have hfc : IsPreconnected (frontier Ω) := by
    rw [← him]
    exact isPreconnected_Icc.image γ hγ.continuous.continuousOn
  obtain ⟨L, hL, hchord⟩ :=
    exists_localConformal_boundaryDensity_chord_bound_of_nonzeroDifferential
      hR F hFs hhol hinj hnz K hK hpK
  have hconjchord (θ τ : ℝ) : ‖conj (K θ) - conj (K τ)‖ ≤ L * ‖γ θ - γ τ‖ := by
    rw [← map_sub, Complex.norm_conj]
    exact hchord θ τ
  have hext : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ (fun θ => conj (K θ)) w = 0 := by
    intro w hw
    have hzero : physicalOrdinaryCauchy γ K w = 0 := by
      rw [physicalOrdinaryCauchy_eq_conj,
        physicalMomentPrimitive_exterior_eq_zero hb hΩ hfc γ H hγ hH him hmom w hw,
        map_zero]
    rw [physicalOrdinaryCauchy_eq_neg_weighted] at hzero
    exact neg_eq_zero.mp hzero
  exact exists_physicalCauchy_boundary_extension hb hΩ hfc γ hγ hpγ
    (physicalCircleTrace_injOn_of_closedDisk_inj F hinj) him
    (fun θ => conj (K θ)) (Complex.continuous_conj.comp hK.continuous)
    hL hconjchord hext

end


end PolyaNeumann

end
