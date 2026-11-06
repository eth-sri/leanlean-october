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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Topology ContDiff


variable {L : ℝ}

local notation "Φ0" => Icc 0

theorem exists_nearestPhysicalBoundaryParam (γ : ℝ → ℂ) (hγ : Continuous γ) w :
    ∃ τ ∈ Φ0 (2 * Real.pi),
      ∀ θ ∈ Φ0 (2 * Real.pi), ‖γ τ - w‖ ≤ ‖γ θ - w‖ := by
  exact isCompact_Icc.exists_isMinOn ⟨0, le_rfl, Real.two_pi_pos.le⟩
    (hγ.sub continuous_const).norm.continuousOn

/-- A choice of an actual nearest physical boundary parameter.  Continuity
of this parameter choice is neither asserted nor needed. -/
def nearestPhysicalBoundaryParam (γ : ℝ → ℂ) (hγ : Continuous γ) (w : ℂ) : ℝ :=
  Classical.choose (exists_nearestPhysicalBoundaryParam γ hγ w)

def nearestPhysicalBoundaryDensity (γ : ℝ → ℂ) (hγ : Continuous γ)
    (K : ℝ → ℂ) (w : ℂ) : ℂ := K (nearestPhysicalBoundaryParam γ hγ w)

/-- The nearest physical point is at most twice as far along a chord from
any comparison point as the approaching point is from that comparison point. -/
theorem nearestPhysicalBoundaryParam_chord_le (γ : ℝ → ℂ) hγ
    (w : ℂ) θ (hθ : θ ∈ Φ0 (2 * Real.pi)) :
    ‖γ θ - γ (nearestPhysicalBoundaryParam γ hγ w)‖ ≤ 2 * ‖γ θ - w‖ := by
  calc
    _ = ‖(γ θ - w) + (w - γ (nearestPhysicalBoundaryParam γ hγ w))‖ := by
      congr 1
      ring
    _ ≤ _ := norm_add_le _ _
    _ = ‖γ θ - w‖ + ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ := by
      rw [norm_sub_rev w]
    _ ≤ _ := add_le_add le_rfl ((Classical.choose_spec (exists_nearestPhysicalBoundaryParam γ hγ w)).2 θ hθ)
    _ = _ := by ring

theorem nearestPhysicalBoundaryDensity_norm_sub_le
    γ hγ K  (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (w : ℂ) t (ht : t ∈ Φ0 (2 * Real.pi)) :
    ‖nearestPhysicalBoundaryDensity γ hγ K w - K t‖ ≤ 2 * L * ‖w - γ t‖ := by
  calc
    _ = _ := by
      rw [nearestPhysicalBoundaryDensity, norm_sub_rev]
    _ ≤ _ := hchord _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (nearestPhysicalBoundaryParam_chord_le γ hγ w t ht) hL
    _ = _ := by rw [norm_sub_rev (γ t)]; ring

/-- Although the nearest parameter need not be continuous, its actual
physical density tends to the prescribed density at every boundary point. -/
theorem nearestPhysicalBoundaryDensity_tendsto
    γ hγ K  (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    t (ht : t ∈ Φ0 (2 * Real.pi)) :
    Tendsto (nearestPhysicalBoundaryDensity γ hγ K) (𝓝 (γ t)) (𝓝 (K t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun w => norm_nonneg _) (fun w =>
    nearestPhysicalBoundaryDensity_norm_sub_le γ hγ K hL hchord w t ht)
  simpa using (tendsto_const_nhds.mul ((continuous_id.sub continuous_const).norm.tendsto' (γ t) 0 (by simp)) :
    Tendsto (fun w => 2 * L * ‖w - γ t‖) (𝓝 (γ t)) (𝓝 ((2 * L) * 0)))

/-- The physical Cauchy commutator with the actual nearest-point density. -/
def physicalNearestCauchyCommutator (γ : ℝ → ℂ) (hγ : Continuous γ)
    (K : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ θ in 0..(2 * Real.pi),
    (deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ K w)) / (γ θ - w)

theorem physicalWeightedCauchy_eq_nearestCommutator_add_winding
    γ (hγ : ContDiff ℝ 1 γ) K (hK : Continuous K)
    w (havoid : ∀ θ ∈ Φ0 (2 * Real.pi), γ θ ≠ w) :
    physicalWeightedCauchy γ K w = physicalNearestCauchyCommutator γ hγ.continuous K w +
      (2 * Real.pi * Complex.I) * nearestPhysicalBoundaryDensity γ hγ.continuous K w *
        windingNumber γ w :=
  (show physicalWeightedCauchy γ K w = (∫ θ in 0..(2 * Real.pi), (deriv γ θ * (K θ - (nearestPhysicalBoundaryDensity γ hγ.continuous K w))) / (γ θ - w)) + (2 * Real.pi * Complex.I) * (nearestPhysicalBoundaryDensity γ hγ.continuous K w) * windingNumber γ w by
    let f : ℝ → ℂ := fun θ => (deriv γ θ * (K θ - (nearestPhysicalBoundaryDensity γ hγ.continuous K w))) / (γ θ - w)
    let q : ℝ → ℂ := fun θ => deriv γ θ / (γ θ - w)
    rw [(show (2 * Real.pi * Complex.I) * (nearestPhysicalBoundaryDensity γ hγ.continuous K w) * windingNumber γ w = (nearestPhysicalBoundaryDensity γ hγ.continuous K w) * ∫ θ in 0..(2 * Real.pi), q θ by
      rw [windingNumber]
      change (2 * Real.pi * Complex.I) * (nearestPhysicalBoundaryDensity γ hγ.continuous K w) *
        ((2 * Real.pi * Complex.I)⁻¹ * ∫ θ in 0..(2 * Real.pi), q θ) = _
      field_simp [show (2 * Real.pi * Complex.I : ℂ) ≠ 0 by
        simp]), physicalWeightedCauchy, (show (fun θ => (deriv γ θ * K θ) / (γ θ - w)) = (fun θ => f θ + (nearestPhysicalBoundaryDensity γ hγ.continuous K w) * q θ) by
      funext θ
      dsimp only [f, q]
      ring),
      intervalIntegral.integral_add (by
        apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
        exact (hγ.continuous_deriv_one.mul (hK.sub continuous_const)).continuousOn.div
          (hγ.continuous.sub continuous_const).continuousOn
          (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))) ((show IntervalIntegrable q volume 0 (2 * Real.pi) by
            apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
            exact hγ.continuous_deriv_one.continuousOn.div
              (hγ.continuous.sub continuous_const).continuousOn
              (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))).const_mul (nearestPhysicalBoundaryDensity γ hγ.continuous K w)), intervalIntegral.integral_const_mul])

private theorem physicalCurve_avoid_of_notMem_frontier
     γ
    (him : γ '' Φ0 (2 * Real.pi) = frontier Ω)
    {w : ℂ} (hw : w ∉ frontier Ω) :
    ∀ θ ∈ Φ0 (2 * Real.pi), γ θ ≠ w := by
  intro θ hθ heq
  apply hw
  rw [← him]
  exact heq ▸ mem_image_of_mem γ hθ

/-- A genuine Lipschitz boundary point is approachable from the exterior.
This is derived from the already-proved actual chart box. -/
theorem frontier_mem_closure_physicalExterior  (hL : IsLipschitzDomain Ω)
     (hp : p ∈ frontier Ω) : p ∈ closure ((closure Ω)ᶜ) := by
  obtain ⟨V, B, _, hpV, _, hBE, _, hcl⟩ := exists_exterior_box hL hp
  exact closure_mono hBE (hcl p ⟨hp, hpV⟩)

/-- The actual Jordan winding theorem and the all-approach commutator prove
a continuous holomorphic extension of the prescribed physical density.
Only exterior vanishing of its genuine Cauchy integral is an analytic premise;
it will be supplied by the actual physical moment primitive below. -/
theorem exists_physicalCauchy_boundary_extension
     (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    γ (hγ : ContDiff ℝ 1 γ)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi)))
    (him : γ '' Φ0 (2 * Real.pi) = frontier Ω)
    (K : ℝ → ℂ) (hK : Continuous K)  (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hzero : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ K w = 0) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ Φ0 (2 * Real.pi), G (γ θ) = K θ := by
  classical
  obtain ⟨_, hLip⟩ := exists_periodic_C1_density_lipschitz γ hγ hpγ
  obtain ⟨σ, hσ, hinside, houtside⟩ := windingNumber_pm_one_of_jordan hb hΩ hLip hpγ
    hinj him (isConnected_compl_closure_of_frontier hb hΩ hfc)
  let a := 2 * Real.pi * Complex.I * σ
  let N := nearestPhysicalBoundaryDensity γ hγ.continuous K
  let R := physicalNearestCauchyCommutator γ hγ.continuous K
  let G : ℂ → ℂ := fun w => if w ∈ Ω then physicalWeightedCauchy γ K w / a else N w
  have hΩo := hΩ.1.1
  have hav w (hw : w ∈ Ω) :
      ∀ θ ∈ Φ0 (2 * Real.pi), γ θ ≠ w := by
    apply physicalCurve_avoid_of_notMem_frontier γ him
    intro hfront
    rw [hΩo.frontier_eq] at hfront
    exact hfront.2 hw
  have hdiff w (hw : w ∈ Ω) : DifferentiableAt ℂ G w := by
    apply ((show DifferentiableAt ℂ (physicalWeightedCauchy γ K) w by
      have heq : physicalWeightedCauchy γ K =
          fun z => -physicalOrdinaryCauchy γ (fun θ => conj (K θ)) z := by
        funext z
        rw [physicalOrdinaryCauchy_eq_neg_weighted]
        simp
      rw [heq]
      exact (physicalOrdinaryCauchy_hasDerivAt γ (fun θ => conj (K θ)) hγ
        (Complex.continuous_conj.comp hK) (hav w hw)).differentiableAt.neg).div_const a).congr_of_eventuallyEq
    filter_upwards [hΩo.mem_nhds hw] with z hz
    simp [G, if_pos hz]
  have htrace θ (hθ : θ ∈ Φ0 (2 * Real.pi)) : G (γ θ) = K θ := by
    have hp : γ θ ∈ frontier Ω := by
      rw [← him]
      exact mem_image_of_mem γ hθ
    simp [G, if_neg (by
      rw [hΩo.frontier_eq] at hp
      exact hp.2)]
    exact (by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      apply le_antisymm
      · simpa using
          nearestPhysicalBoundaryDensity_norm_sub_le γ hγ.continuous K hL hchord (γ θ) θ hθ
      · exact norm_nonneg _)
  refine ⟨G, ⟨fun w hw => (hdiff w hw).differentiableWithinAt, ?_⟩, htrace⟩
  intro p hpcl
  by_cases hpΩ : p ∈ Ω
  · exact (hdiff p hpΩ).continuousAt.continuousWithinAt
  · have hpfront : p ∈ frontier Ω := by
      rw [hΩo.frontier_eq]
      exact ⟨hpcl, hpΩ⟩
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ Ico 0 (2 * Real.pi), γ t = p := by
      rw [← him] at hpfront
      obtain ⟨t, ht, heq⟩ := hpfront
      by_cases htL : t = 2 * Real.pi
      · refine ⟨0, ⟨le_rfl, Real.two_pi_pos⟩, ?_⟩
        rw [← heq, htL]
        simpa using (hpγ 0).symm
      · exact ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 htL⟩, heq⟩
    have hN := nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
      t (Ico_subset_Icc_self ht)
    have hf : Tendsto (fun w => physicalWeightedCauchy γ K w / a)
        (𝓝[closure Ω ∩ Ω] (γ t)) (𝓝 (K t)) := by
      apply Tendsto.congr' ?_ ((show Tendsto (fun w => R w / a + N w) (𝓝 (γ t)) (𝓝 (K t)) by
        simpa using ((show Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t)) (𝓝 0) by
          have hRzero : ∀ w : ℂ, w ∉ closure Ω →
              physicalNearestCauchyCommutator γ hγ.continuous K w = 0 := by
            intro w hw
            have heq := physicalWeightedCauchy_eq_nearestCommutator_add_winding γ hγ K hK w (physicalCurve_avoid_of_notMem_frontier γ him (fun hfront => hw (frontier_subset_closure hfront)))
            rw [hzero w hw, houtside w hw, mul_zero, add_zero] at heq
            exact heq.symm
          haveI : (𝓝[(closure Ω)ᶜ] (γ t)).NeBot :=
            mem_closure_iff_nhdsWithin_neBot.mp (frontier_mem_closure_physicalExterior hΩ (by
              rw [← him]
              exact mem_image_of_mem γ (Ico_subset_Icc_self ht)))
          have hlim : Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t)) (𝓝 (∫ θ in 0..(2 * Real.pi), deriv γ θ * (K θ - K t) / (γ θ - γ t))) := by
            obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
              (s := Φ0 (2 * Real.pi)) hγ.continuous_deriv_one.continuousOn
            have hM0 := (norm_nonneg (deriv γ 0)).trans
              (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
            have hbound w θ (hθ : θ ∈ Φ0 (2 * Real.pi)) :
                ‖(deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w)) /
                  (γ θ - w)‖ ≤ M * (2 * L) := by
              have hKθ : ‖K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w‖ ≤
                  2 * L * ‖γ θ - w‖ := by
                calc
                  _ ≤ _ :=
                    hchord _ _
                  _ ≤ _ := mul_le_mul_of_nonneg_left
                    (nearestPhysicalBoundaryParam_chord_le γ hγ.continuous w θ hθ) hL
                  _ = _ := by ring
              by_cases hd : γ θ - w = 0
              · rw [hd, div_zero, norm_zero]
                positivity
              · rw [norm_div]
                apply (div_le_iff₀ (norm_pos_iff.mpr hd)).mpr
                calc
                  _ = _ := norm_mul _ _
                  _ ≤ _ :=
                    mul_le_mul_of_nonneg_right (hM θ hθ) (norm_nonneg _)
                  _ ≤ _ := mul_le_mul_of_nonneg_left hKθ hM0
                  _ = _ := by ring
            unfold physicalNearestCauchyCommutator
            refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
              (μ := volume) (bound := fun _ => M * (2 * L))
              ?_ ?_ intervalIntegrable_const ?_
            · exact Eventually.of_forall fun w =>
                ((hγ.continuous_deriv_one.measurable.mul (hK.measurable.sub measurable_const)).div
                  (hγ.continuous.measurable.sub measurable_const)).aestronglyMeasurable
            · exact Eventually.of_forall fun w => Eventually.of_forall fun θ hθ => by
                rw [uIoc_of_le Real.two_pi_pos.le] at hθ
                exact hbound w θ ⟨hθ.1.le, hθ.2⟩
            · filter_upwards [volume.ae_ne t, volume.ae_ne (2 * Real.pi)] with θ hθt hθL
              intro hθ
              rw [uIoc_of_le Real.two_pi_pos.le] at hθ
              exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub (nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord t (Ico_subset_Icc_self ht)))).div ((continuous_const.sub continuous_id).tendsto (γ t)) (sub_ne_zero.mpr (fun he => hθt (hinj ⟨hθ.1.le, lt_of_le_of_ne hθ.2 hθL⟩ ht he)))
          have heq : physicalNearestCauchyCommutator γ hγ.continuous K =ᶠ[𝓝[(closure Ω)ᶜ] (γ t)]
              fun _ => 0 := by
            filter_upwards [self_mem_nhdsWithin] with w hw
            exact hRzero w hw
          rw [tendsto_nhds_unique (hlim.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)] at hlim
          exact hlim).div_const a).add hN).mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [physicalWeightedCauchy_eq_nearestCommutator_add_winding γ hγ K hK w (hav w hw.2), hinside w hw.2]
      dsimp only [R, N, a]
      field_simp [show 2 * Real.pi * Complex.I ≠ 0 by
        simp, show σ ≠ 0 by
        rcases hσ with hσ | hσ <;> simp [hσ]]
    change Tendsto G (𝓝[closure Ω] (γ t)) (𝓝 (G (γ t)))
    rw [htrace t (Ico_subset_Icc_self ht)]
    exact hf.if_nhdsWithin (p := fun w => w ∈ Ω) (hN.mono_left nhdsWithin_le_nhds)

/-- Actual physical antiholomorphic moments yield an actual continuous
holomorphic extension of the conjugated primitive.  The inverse collar
supplies the proved density chord bound, while the given physical domain
supplies the Jordan winding and exterior connectedness theorems. -/
theorem exists_localConformal_physicalMomentPrimitive_extension
     (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
     (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball 0 1 = Ω)
    H (hH : Continuous H)
    (hpH : Function.Periodic H (2 * Real.pi))
    (hmom : ∀ m : ℕ, (∫ θ in 0..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ Φ0 (2 * Real.pi),
        G (physicalCircleTrace F θ) =
          conj (physicalMomentPrimitive (physicalCircleTrace F) H θ) := by
  let γ := physicalCircleTrace F
  let K := physicalMomentPrimitive γ H
  have hγ :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpγ := physicalCircleTrace_periodic F
  have hK := contDiff_physicalMomentPrimitive γ H hγ hH
  have him : γ '' Φ0 (2 * Real.pi) = frontier Ω := by
    simpa [himage] using localConformal_circleTrace_image_frontier hR F hFs hinj (himage.symm ▸ hΩ.1.1)
  have hfc : IsPreconnected (frontier Ω) := by
    rw [← him]
    exact isPreconnected_Icc.image γ hγ.continuous.continuousOn
  obtain ⟨L, hL, hchord⟩ :=
    exists_localConformal_boundaryDensity_chord_bound_of_nonzeroDifferential
      hR F hFs hhol hinj hnz K hK (by
        apply physicalMomentPrimitive_periodic γ H hγ hH hpγ hpH
        simpa using hmom 0)
  have hconjchord (θ τ : ℝ) : ‖conj (K θ) - conj (K τ)‖ ≤ L * ‖γ θ - γ τ‖ := by
    rw [← map_sub, Complex.norm_conj]
    exact hchord θ τ
  exact exists_physicalCauchy_boundary_extension hb hΩ hfc γ hγ hpγ
    (physicalCircleTrace_injOn_of_closedDisk_inj F hinj) him
    (fun θ => conj (K θ)) (Complex.continuous_conj.comp hK.continuous)
    hL hconjchord (by
      intro w hw
      have hzero : physicalOrdinaryCauchy γ K w = 0 := by
        rw [physicalOrdinaryCauchy_eq_conj,
          physicalMomentPrimitive_exterior_eq_zero hb hΩ hfc γ H hγ hH him hmom w hw,
          map_zero]
      rw [physicalOrdinaryCauchy_eq_neg_weighted] at hzero
      exact neg_eq_zero.mp hzero)

end PolyaNeumann

end
