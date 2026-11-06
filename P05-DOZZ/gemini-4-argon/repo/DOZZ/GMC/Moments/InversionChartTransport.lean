/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.Moments.InversionAdmissibleVersion
public import DOZZ.GMC.Moments.InversionAtomless
public import DOZZ.GMC.Moments.InversionCoordinate

/-! Transport of arbitrary limiting GMC versions through the punctured inversion chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- An arbitrary `IsGMCOf` version, restricted to the inversion chart and then pushed through
inversion, is an admissible version of the pulled-back regularization. The pushed chart measure
agrees almost surely with the full inversion image because the original chaos has no atom at zero.
-/
theorem isGMCOf_inversion_chart_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hXc : IsCircleAverage P X Xc) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P inversionChart (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω (complexInvOpenPartialHomeomorph x)
          (Real.log (1 / ε))) γ N ∧
      ∀ᵐ ω ∂P, (M ω).map complexInvOpenPartialHomeomorph = N ω := by
  classical
  have hP : IsProbabilityMeasure P := hX.1
  let U := inversionChart
  let dens : ℂ → ℝ := fun x => normPlus x ^ (-4 : ℝ)
  let Y : Ω → ℝ → ℂ → ℝ := fun ω ε x => Xc ω x (Real.log (1 / ε))
  let φ : ℂ → ℂ := complexInvOpenPartialHomeomorph
  have hφ : Measurable φ := by
    change Measurable (fun x : ℂ => x⁻¹)
    fun_prop
  obtain ⟨Mchart, hMchart, hMchartFinite, hMrestrict⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hXc U
      isOpen_compl_singleton
  let N : Ω → Measure ℂ := fun ω => (Mchart ω).map φ
  have hNfinite : ∀ ω, IsFiniteMeasure (N ω) := by
    intro ω
    exact (Measure.isFiniteMeasure_map_iff hφ.aemeasurable).2 (hMchartFinite ω)
  have hNsupport : ∀ ω, N ω Uᶜ = 0 := by
    intro ω
    apply le_antisymm
    · calc
        N ω Uᶜ = (Mchart ω) (φ ⁻¹' Uᶜ) := by
          rw [show N ω = (Mchart ω).map φ by rfl,
            Measure.map_apply hφ (by exact (show MeasurableSet U by change MeasurableSet (({0} : Set ℂ)ᶜ); exact (isOpen_compl_singleton : IsOpen (({0} : Set ℂ)ᶜ)).measurableSet).compl)]
        _ ≤ (Mchart ω) Uᶜ := measure_mono (by intro x hx; by_contra hxU; exact hx (by simpa [U, inversionChart] using (by change x⁻¹ ≠ 0; exact inv_ne_zero (by simpa [U, inversionChart] using hxU))))
        _ = 0 := hMchart.2.1 ω
    · exact zero_le
  have hNlimit (f : BoundedContinuousFunction ℂ ℝ)
      (hfcompact : HasCompactSupport (f : ℂ → ℝ))
      (hfU : tsupport (f : ℂ → ℝ) ⊆ U) :
      TendstoInMeasure P
        (fun r ω => regularizedLogChaosTestMass P U dens
          (fun ω ε x => Y ω ε (φ x)) γ r ω f) atTop
        (fun ω => ∫ x, f x ∂N ω) := by
    obtain ⟨g, hgcompact, hgU, hgOn, _hgOff, hmass⟩ :=
      @regularizedLogChaosTestMass_inversion_coordinate_change Ω _ P hP Y (isCircleAverage_admissible P X hX Xc hXc U isOpen_compl_singleton) γ f
        hfcompact hfU
    have hMapTest ω :
        ∫ x, f x ∂N ω = ∫ x, g x ∂Mchart ω := by
      calc
        ∫ x, f x ∂N ω = ∫ x, f (φ x) ∂Mchart ω := by
          dsimp [N]
          exact integral_map hφ.aemeasurable f.continuous.aestronglyMeasurable
        _ = ∫ x, g x ∂Mchart ω := by
          apply integral_congr_ae
          filter_upwards [(show ∀ᵐ x ∂Mchart ω, x ∈ U by rw [ae_iff]; exact hMchart.2.1 ω)] with x hx
          exact (hgOn x hx).symm
    exact TendstoInMeasure.congr (fun r => ae_of_all P (fun ω => hmass r ω)) (ae_of_all P (fun ω => (hMapTest _).symm)) (hMchart.2.2.2 g hgcompact hgU)
  have hN : IsAdmissibleGMCVersion P U dens
      (fun ω ε x => Y ω ε (φ x)) γ N :=
    ⟨(by apply Measure.measurable_of_measurable_coe; intro A hA; rw [(show (fun ω => N ω A) = fun ω => Mchart ω (φ ⁻¹' A) by funext ω; exact Measure.map_apply hφ hA)]; exact (Measure.measurable_coe (hA.preimage hφ)).comp hMchart.1), hNsupport, (by intro ω K hK hKU; exact lt_of_le_of_lt (measure_mono (Set.subset_univ K)) (hNfinite ω).measure_univ_lt_top), hNlimit⟩
  have hfull : ∀ᵐ ω ∂P, (M ω).map (fun x : ℂ => x⁻¹) = N ω := by
    filter_upwards [(gmc_atomless_at_zero_of_isGMCOf P X hX γ hγ hγ2 M hM), hMrestrict] with ω hωAtom hωrestrict
    calc
      (M ω).map (fun x : ℂ => x⁻¹) = ((M ω).restrict U).map (fun x : ℂ => x⁻¹) :=
        congrArg (fun μ : Measure ℂ => μ.map (fun x : ℂ => x⁻¹)) (Measure.restrict_eq_self_of_ae_mem (show ∀ᵐ x ∂M ω, x ∈ U by rw [ae_iff]; simpa [U, inversionChart] using hωAtom)).symm
      _ = ((M ω).restrict U).map φ := by
        rfl
      _ = N ω := congrArg (fun μ : Measure ℂ => μ.map φ) hωrestrict
  refine ⟨N, ?_, ?_⟩
  · simpa [Y, φ, U, dens] using hN
  · filter_upwards [hfull] with ω hω
    simpa [φ, complexInvOpenPartialHomeomorph] using hω

end DOZZ.Proofs
