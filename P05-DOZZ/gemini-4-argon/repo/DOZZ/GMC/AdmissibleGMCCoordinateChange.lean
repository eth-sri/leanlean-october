/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCUniqueConcrete
public import DOZZ.GMC.AdmissibleGMCRestriction
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! Coordinate transport inputs for admissible GMC versions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped CompactlySupported

namespace DOZZ.Proofs


/-- Matching the reference measure and fields makes the two regularized test masses agree under
an open partial homeomorphism. -/
theorem regularizedLogChaosTestMass_coordinate_change
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    U V (densU densV : ℂ → ℝ) εU εV
    YU YV
    (hYU : IsAdmissibleLogRegularization P U densU εU YU)
    (hYV : IsAdmissibleLogRegularization P V densV εV YV)
    (φ : OpenPartialHomeomorph ℂ ℂ) (hφU : φ.source = U) (hφV : φ.target = V)
    (hReference : logRegularizationReference V densV =
      (logRegularizationReference U densU).map φ)
    (hField : ∀ ω ε, ∀ y ∈ V, YV ω ε y = YU ω ε (φ.symm y))
    γ (f : BoundedContinuousFunction ℂ ℝ)
    (hfCompact : HasCompactSupport (f : ℂ → ℝ)) (hfV : tsupport (f : ℂ → ℝ) ⊆ V) :
    ∃ g : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (g : ℂ → ℝ) ∧ tsupport (g : ℂ → ℝ) ⊆ U ∧
      (∀ x ∈ U, g x = f (φ x)) ∧ (∀ x ∉ U, g x = 0) ∧
      ∀ r ω, regularizedLogChaosTestMass P V densV YV γ r ω f =
        regularizedLogChaosTestMass P U densU YU γ r ω g := by
  classical
  have exists_partialHomeomorph_pullback_test : ∃ g : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (g : ℂ → ℝ) ∧ tsupport (g : ℂ → ℝ) ⊆ U ∧ (∀ x ∈ U, g x = f (φ x)) ∧ (∀ x ∉ U, g x = 0) := by
    classical
    let K := φ.symm '' tsupport (f : ℂ → ℝ)
    have hKcompact : IsCompact K := hfCompact.image_of_continuousOn (φ.symm.continuousOn.mono (by
        intro y hy
        simpa [hφV] using hfV hy))
    have hKU : K ⊆ U := by
      rintro x ⟨y, hy, rfl⟩
      simpa [hφU] using (φ.map_target (by simpa [hφV] using hfV hy))
    have hKclosed := hKcompact.isClosed
    let g : ℂ → ℝ := fun x => if x ∈ U then f (φ x) else 0
    have hsupport : Function.support g ⊆ K := by
      intro x hx
      by_cases hxU : x ∈ U
      · have hfx : f (φ x) ≠ 0 := by
          simpa [g, hxU, Function.mem_support] using hx
        exact ⟨φ x, (subset_tsupport (f : ℂ → ℝ) (Function.mem_support.mpr hfx)), by
          exact φ.left_inv (by simpa [hφU] using hxU)⟩
      · simp [g, hxU] at hx
    have htsupport := closure_minimal hsupport hKclosed
    have hgcont : Continuous g := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      by_cases hxU : x ∈ U
      · have hcomp : ContinuousOn (fun y => f (φ y)) U :=
          f.continuous.continuousOn.comp (by
            simpa [hφU] using φ.continuousOn) (by
            intro y hy
            simpa [hφV] using (φ.map_source (by simpa [hφU] using hy)))
        have hnear := (show IsOpen U by simpa [hφU] using φ.open_source).mem_nhds hxU
        exact (hcomp.continuousAt hnear).congr (show (fun y => g y) =ᶠ[𝓝 x] fun y => f (φ y) by filter_upwards [hnear] with y hy; simp [g, hy]).symm
      · have hxK : x ∉ K := fun hxK => hxU (hKU hxK)
        have hzero : (fun y => g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(hKclosed.isOpen_compl.mem_nhds hxK)] with y hy
          by_contra hne
          exact hy (hsupport (Function.mem_support.mpr hne))
        exact continuousAt_const.congr hzero.symm
    let gc : C_c(ℂ, ℝ) := ⟨⟨g, hgcont⟩, by
      change IsCompact (tsupport g)
      exact hKcompact.of_isClosed_subset (isClosed_tsupport g) htsupport⟩
    refine ⟨gc.toBoundedContinuousFunction, ?_, ?_, ?_⟩
    · exact gc.hasCompactSupport
    · exact htsupport.trans hKU
    · constructor
      · intro x hx
        change g x = f (φ x)
        simp [g, hx]
      · intro x hx
        change g x = 0
        simp [g, hx]
  obtain ⟨g, hgCompact, hgU, hgOn, hgOff⟩ :=
    exists_partialHomeomorph_pullback_test
  refine ⟨g, hgCompact, hgU, hgOn, hgOff, ?_⟩
  intro r ω
  let ε : ℝ := Real.exp (-r)
  let μU : Measure ℂ := logRegularizationReference U densU
  let μV : Measure ℂ := logRegularizationReference V densV
  let varU : ℂ → ℝ := fun x => ∫ ω', YU ω' ε x ^ 2 ∂P
  let varV : ℂ → ℝ := fun y => ∫ ω', YV ω' ε y ^ 2 ∂P
  let targetIntegrand : ℂ → ℝ := fun y =>
    f y * Real.exp (γ * YV ω ε y - γ ^ 2 / 2 * varV y)
  let sourceIntegrand : ℂ → ℝ := fun x =>
    g x * Real.exp (γ * YU ω ε x - γ ^ 2 / 2 * varU x)
  have hUmeas := hYU.openChart.measurableSet
  have := hYV.openChart.measurableSet
  have hμUrestrict : μU = μU.restrict U := by
    dsimp [μU]
    exact logRegularizationReference_restrict_of_subset U U densU hUmeas subset_rfl
  have : Measurable (fun y => YV ω ε y) := (hYV.measurableAtScale ε).comp (measurable_const.prodMk measurable_id)
  have : Measurable (fun x => YU ω ε x) := (hYU.measurableAtScale ε).comp (measurable_const.prodMk measurable_id)
  have : Measurable varV := ((show Measurable (fun q : ℂ × Ω => YV q.2 ε q.1 ^ 2) by exact (hYV.measurableAtScale ε).comp measurable_swap |>.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have : Measurable varU := ((show Measurable (fun q : ℂ × Ω => YU q.2 ε q.1 ^ 2) by exact (hYU.measurableAtScale ε).comp measurable_swap |>.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hpoint x (hx : x ∈ U) : targetIntegrand (φ x) = sourceIntegrand x := by
    have hxSource : x ∈ φ.source := by simpa [hφU] using hx
    have hfield ω' : YV ω' ε (φ x) = YU ω' ε x := by
      rw [hField ω' ε (φ x) (show φ x ∈ V by simpa [hφV] using (φ.map_source hxSource)), (φ.left_inv hxSource)]
    have hvariance : varV (φ x) = varU x := by
      dsimp [varV, varU]
      exact integral_congr_ae (ae_of_all P fun ω' => by
        change YV ω' ε (φ x) ^ 2 = YU ω' ε x ^ 2
        rw [hfield ω'])
    simp [targetIntegrand, sourceIntegrand, hgOn x hx, hfield ω, hvariance]
  change ∫ y, targetIntegrand y ∂μV = ∫ x, sourceIntegrand x ∂μU
  calc
    ∫ y, targetIntegrand y ∂μV = ∫ y, targetIntegrand y ∂μU.map φ := by
      dsimp [μU, μV]
      rw [hReference]
    _ = ∫ x, targetIntegrand (φ x) ∂μU :=
      integral_map (by rw [hμUrestrict]; exact (show ContinuousOn φ U by simpa [hφU] using φ.continuousOn).aemeasurable hUmeas) (show Measurable targetIntegrand by dsimp [targetIntegrand]; fun_prop).aestronglyMeasurable
    _ = ∫ x, sourceIntegrand x ∂μU := integral_congr_ae (by rw [hμUrestrict]; filter_upwards [ae_restrict_mem hUmeas] with x hx; exact hpoint x hx)

end DOZZ.Proofs
