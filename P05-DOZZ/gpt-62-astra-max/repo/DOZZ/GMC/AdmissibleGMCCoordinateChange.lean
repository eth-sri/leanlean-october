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

/-- Pull a compactly supported continuous test on the target chart back through an open partial
homeomorphism, extending it by zero off the source chart. -/
theorem exists_partialHomeomorph_pullback_test
    (U V : Set ℂ) (φ : OpenPartialHomeomorph ℂ ℂ)
    (hφU : φ.source = U) (hφV : φ.target = V)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hfCompact : HasCompactSupport (f : ℂ → ℝ))
    (hfV : tsupport (f : ℂ → ℝ) ⊆ V) :
    ∃ g : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (g : ℂ → ℝ) ∧ tsupport (g : ℂ → ℝ) ⊆ U ∧
        (∀ x ∈ U, g x = f (φ x)) ∧ (∀ x ∉ U, g x = 0) := by
  classical
  let K : Set ℂ := φ.symm '' tsupport (f : ℂ → ℝ)
  have hKcompact : IsCompact K := by
    exact hfCompact.image_of_continuousOn (φ.symm.continuousOn.mono (by
      intro y hy
      simpa [hφV] using hfV hy))
  have hKU : K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    have hyV : y ∈ φ.target := by simpa [hφV] using hfV hy
    have hySource := φ.map_target hyV
    simpa [hφU] using hySource
  have hKclosed : IsClosed K := hKcompact.isClosed
  let g : ℂ → ℝ := fun x => if x ∈ U then f (φ x) else 0
  have hsupport : Function.support g ⊆ K := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hfx : f (φ x) ≠ 0 := by
        simpa [g, hxU, Function.mem_support] using hx
      have hφx : φ x ∈ tsupport (f : ℂ → ℝ) :=
        subset_tsupport (f : ℂ → ℝ) (Function.mem_support.mpr hfx)
      exact ⟨φ x, hφx, by
        have hxSource : x ∈ φ.source := by simpa [hφU] using hxU
        exact φ.left_inv hxSource⟩
    · simp [g, hxU] at hx
  have htsupport : tsupport g ⊆ K := closure_minimal hsupport hKclosed
  have hgcont : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hxU : x ∈ U
    · have hcomp : ContinuousOn (fun y => f (φ y)) U :=
        f.continuous.continuousOn.comp (by
          simpa [hφU] using φ.continuousOn) (by
          intro y hy
          have hySource : y ∈ φ.source := by simpa [hφU] using hy
          have hφy := φ.map_source hySource
          simpa [hφV] using hφy)
      have hUopen : IsOpen U := by simpa [hφU] using φ.open_source
      have hnear : U ∈ 𝓝 x := hUopen.mem_nhds hxU
      have hct := hcomp.continuousAt hnear
      have heq : (fun y => g y) =ᶠ[𝓝 x] fun y => f (φ y) := by
        filter_upwards [hnear] with y hy
        simp [g, hy]
      exact hct.congr heq.symm
    · have hxK : x ∉ K := fun hxK => hxU (hKU hxK)
      have hnear : Kᶜ ∈ 𝓝 x := hKclosed.isOpen_compl.mem_nhds hxK
      have hzero : (fun y => g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hnear] with y hy
        have hgy : g y = 0 := by
          by_contra hne
          have hyK : y ∈ K := hsupport (Function.mem_support.mpr hne)
          exact hy hyK
        exact hgy
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

/-- Matching the reference measure and fields makes the two regularized test masses agree under
an open partial homeomorphism. -/
theorem regularizedLogChaosTestMass_coordinate_change
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U V : Set ℂ) (densU densV : ℂ → ℝ) (εU εV : ℝ)
    (YU YV : Ω → ℝ → ℂ → ℝ)
    (hYU : IsAdmissibleLogRegularization P U densU εU YU)
    (hYV : IsAdmissibleLogRegularization P V densV εV YV)
    (φ : OpenPartialHomeomorph ℂ ℂ) (hφU : φ.source = U) (hφV : φ.target = V)
    (hReference : logRegularizationReference V densV =
      (logRegularizationReference U densU).map φ)
    (hField : ∀ ω ε, ∀ y ∈ V, YV ω ε y = YU ω ε (φ.symm y))
    (γ : ℝ) (f : BoundedContinuousFunction ℂ ℝ)
    (hfCompact : HasCompactSupport (f : ℂ → ℝ)) (hfV : tsupport (f : ℂ → ℝ) ⊆ V) :
    ∃ g : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (g : ℂ → ℝ) ∧ tsupport (g : ℂ → ℝ) ⊆ U ∧
      (∀ x ∈ U, g x = f (φ x)) ∧ (∀ x ∉ U, g x = 0) ∧
      ∀ r ω, regularizedLogChaosTestMass P V densV YV γ r ω f =
        regularizedLogChaosTestMass P U densU YU γ r ω g := by
  classical
  obtain ⟨g, hgCompact, hgU, hgOn, hgOff⟩ :=
    exists_partialHomeomorph_pullback_test U V φ hφU hφV f hfCompact hfV
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
  have hUmeas : MeasurableSet U := hYU.openChart.measurableSet
  have hVmeas : MeasurableSet V := hYV.openChart.measurableSet
  have hμUrestrict : μU = μU.restrict U := by
    dsimp [μU]
    exact logRegularizationReference_restrict_of_subset U U densU hUmeas subset_rfl
  have hφcontU : ContinuousOn φ U := by simpa [hφU] using φ.continuousOn
  have hφae : AEMeasurable φ μU := by
    rw [hμUrestrict]
    exact hφcontU.aemeasurable hUmeas
  have hsectionV : Measurable (fun y => YV ω ε y) := by
    exact (hYV.measurableAtScale ε).comp (measurable_const.prodMk measurable_id)
  have hsectionU : Measurable (fun x => YU ω ε x) := by
    exact (hYU.measurableAtScale ε).comp (measurable_const.prodMk measurable_id)
  have hvarV : Measurable varV := by
    have hsquare : Measurable (fun q : ℂ × Ω => YV q.2 ε q.1 ^ 2) := by
      exact (hYV.measurableAtScale ε).comp measurable_swap |>.pow_const 2
    exact (hsquare.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hvarU : Measurable varU := by
    have hsquare : Measurable (fun q : ℂ × Ω => YU q.2 ε q.1 ^ 2) := by
      exact (hYU.measurableAtScale ε).comp measurable_swap |>.pow_const 2
    exact (hsquare.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have htargetMeas : Measurable targetIntegrand := by
    dsimp [targetIntegrand]
    fun_prop
  have hsourceMeas : Measurable sourceIntegrand := by
    dsimp [sourceIntegrand]
    fun_prop
  have hpoint (x : ℂ) (hx : x ∈ U) : targetIntegrand (φ x) = sourceIntegrand x := by
    have hxSource : x ∈ φ.source := by simpa [hφU] using hx
    have hφxV : φ x ∈ V := by
      have h := φ.map_source hxSource
      simpa [hφV] using h
    have hleft : φ.symm (φ x) = x := φ.left_inv hxSource
    have hfield (ω' : Ω) : YV ω' ε (φ x) = YU ω' ε x := by
      rw [hField ω' ε (φ x) hφxV, hleft]
    have hvariance : varV (φ x) = varU x := by
      dsimp [varV, varU]
      exact integral_congr_ae (ae_of_all P fun ω' => by
        change YV ω' ε (φ x) ^ 2 = YU ω' ε x ^ 2
        rw [hfield ω'])
    simp [targetIntegrand, sourceIntegrand, hgOn x hx, hfield ω, hvariance]
  have hcompAE : (fun x => targetIntegrand (φ x)) =ᵐ[μU] sourceIntegrand := by
    rw [hμUrestrict]
    filter_upwards [ae_restrict_mem hUmeas] with x hx
    exact hpoint x hx
  change ∫ y, targetIntegrand y ∂μV = ∫ x, sourceIntegrand x ∂μU
  calc
    ∫ y, targetIntegrand y ∂μV = ∫ y, targetIntegrand y ∂μU.map φ := by
      dsimp [μU, μV]
      rw [hReference]
    _ = ∫ x, targetIntegrand (φ x) ∂μU :=
      integral_map hφae htargetMeas.aestronglyMeasurable
    _ = ∫ x, sourceIntegrand x ∂μU := integral_congr_ae hcompAE

end DOZZ.Proofs
