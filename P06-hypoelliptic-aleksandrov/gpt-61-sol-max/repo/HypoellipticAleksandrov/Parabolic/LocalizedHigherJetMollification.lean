module

public import HypoellipticAleksandrov.Parabolic.HigherJetLocalization
public import HypoellipticAleksandrov.Parabolic.CompactWeakDerivativeFamilyGlobalization
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollificationSupport
public import HypoellipticAleksandrov.Parabolic.HigherWeakDerivativeMollification
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



/-!
# Localized higher-jet mollification

This file assembles compact localization, ambient globalization, and the
common spacetime mollification of a finite ordinary weak-derivative jet.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

/-- A finite local weak-derivative jet admits one compactly supported ambient
localization whose positive-radius mollifications have a common compact
support, retain the full higher-derivative identity, and agree with the
original mollified jet on the prescribed compact set. -/
theorem exists_localizedHigherJetMollification
    {d m : ℕ} {U C : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u) :
    ∃ (ρ : ℝ) (_ : 0 < ρ)
      (K : HypoellipticAleksandrov.Parabolic.Region d)
      (_ : IsCompact K)
      (_ : MeasurableSet K)
      (_ : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) K < ∞)
      (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
      (_ : ContDiff ℝ PDE.smoothOrder b)
      (_ : HasCompactSupport b)
      (_ : tsupport b ⊆ U)
      (G : ParabolicWeakDerivativeFamily d (2 * m) Set.univ
        (fun z ↦ b z * u z)),
      Set.EqOn b 1 (Metric.cthickening ρ C) ∧
      (∀ beta : TimeVelocityDerivativeIndex d m,
        Set.EqOn (G.ordinaryRepresentative beta)
          (D.ordinaryRepresentative beta) (Metric.cthickening ρ C)) ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ →
        ∀ beta : TimeVelocityDerivativeIndex d m,
          TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
              (SpacetimeMollifier.spacetimeMollification ε
                (G.ordinaryRepresentative
                  (TimeVelocityDerivativeIndex.zero d m))) =
            SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative beta) ∧
          tsupport (SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative beta)) ⊆ K ∧
          Set.EqOn
            (SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative beta))
            (SpacetimeMollifier.spacetimeMollification ε
              (D.ordinaryRepresentative beta)) C := by
  let sharedTerm_8d68e40829 := ((ParabolicDerivativeIndex.zero d (2 * m)))
  let sharedTerm_183d11f3ad := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  obtain ⟨δ, hδ, b, hbSmooth, hbCompact, hbSupport, hbOne,
      B, hB, hbBound, Dloc, hDlocRep, hDlocSupport,
      ρloc, hρloc, hρlocδ, hDlocEq⟩ :=
    exists_localizedHigherJetFamily hU hC hCU D
  have hDlocSupportU  :=
    fun beta ↦ (hDlocSupport beta).trans hbSupport
  let G₀ := Dloc.compactSupportGlobalize hU hDlocSupportU

  have hzero  :=
    Dloc.zero_representative_ae_eq_of_support_subset hU.measurableSet
      (hDlocSupportU sharedTerm_8d68e40829) (by
          intro z hz
          apply hbSupport
          exact subset_tsupport b (fun hbz ↦ hz (by simp [hbz])))
  let G : ParabolicWeakDerivativeFamily d (2 * m) Set.univ
      (fun z ↦ b z * u z) :=
    { representative := G₀.representative
      memLp := G₀.memLp
      zero_ae := by
        change Dloc.representative sharedTerm_8d68e40829
          =ᵐ[sharedTerm_183d11f3ad.restrict Set.univ]
            (fun z ↦ b z * u z)
        simpa using hzero
      hasWeakTimeSucc := G₀.hasWeakTimeSucc
      hasWeakVelocitySucc := G₀.hasWeakVelocitySucc }
  let ρ : ℝ := min ρloc 1
  let K  := Metric.cthickening 1 (tsupport b)

  have hρρloc : ρ ≤ ρloc := min_le_left _ _

  have hKCompact : IsCompact K := hbCompact.cthickening


  refine ⟨ρ, (lt_min hρloc zero_lt_one), K, hKCompact, hKCompact.isClosed.measurableSet, hKCompact.measure_lt_top,
    b, hbSmooth, hbCompact, hbSupport, G, ?_, ?_, ?_⟩
  · exact hbOne.mono
      (Metric.cthickening_mono (hρρloc.trans hρlocδ.le) C)
  · intro beta
    exact (hDlocEq beta).mono (Metric.cthickening_mono hρρloc C)
  · intro ε hε hερ beta
    refine ⟨G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
      ε hε beta, ?_, ?_⟩
    · exact (SpacetimeMollifier.tsupport_spacetimeMollification_subset_cthickening
        (f := G.ordinaryRepresentative beta) hε).trans
          ((Metric.cthickening_subset_of_subset ε
            ((hDlocSupport beta.toParabolic).trans (by rfl))).trans
            (Metric.cthickening_mono (hερ.le.trans (min_le_right _ _)) (tsupport b)))
    · apply SpacetimeMollifier.spacetimeMollification_congr_on_of_eqOn_thickening hε
      change Set.EqOn (Dloc.ordinaryRepresentative beta)
        (D.ordinaryRepresentative beta) (Metric.thickening ε C)
      exact (hDlocEq beta).mono
        (Metric.thickening_subset_cthickening_of_le
          (hερ.le.trans hρρloc) C)

end HypoellipticAleksandrov.Parabolic
