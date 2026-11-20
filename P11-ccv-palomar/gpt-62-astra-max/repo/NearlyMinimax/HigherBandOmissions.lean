module

public import NearlyMinimax.HigherBandFamily


@[expose] public section

/-! Exact omission of zero-variation rows and positive subunit scale rows
from the actual finite signed family. A subunit interpolation target remains
zero; no zero-defect assertion is made for that source branch. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable {d D M q : ℕ} (a b C lam ell N mu : ℝ) (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (F : (i : Fin (D-2) × Bool) → HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    {n : ℕ}

theorem centered_cardinal_measure_below_one_eq_zero (i : Fin n) (d : ℕ)
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1) : centeredCardinalMeasure i d T = 0 := by
  simp only [centeredCardinalMeasure, spatialScaleMeasure,
    spatial_scale_domain_empty_below_one i hT hT1, Measure.restrict_empty, Measure.zero_prod]

theorem higherBand_coarse_below_one_signed_zero (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 0 < T) (hT1 : T < 1) : higherBandSignedRow d r m D q a b C lam L T false = 0 := by
  rw [higherBandSignedRow, higherBandCarrierMeasure,
    (by unfold cardinalSeparatedMeasure; simp_rw [centered_cardinal_measure_below_one_eq_zero _ d hT hT1, Measure.map_zero]; exact Finset.sum_const_zero : cardinalSeparatedMeasure d r T = 0), highPacketSignedMeasure]
  ext1 s hs
  rw [withDensityᵥ_apply (by simp) hs]
  simp

def higherBandFamilyRowIntegral
    (i : Fin (D-2) × Bool) : ℝ :=
  ∫ᵛ e, F i e ∂<•higherBandSignedRow d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ell (higherBandFamilyUpper d ell N mu i) i.2

def higherBandPhysicalIntegral
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      higherBandFamilyRowIntegral a b C lam ell N mu F i else 0
  else higherBandFamilyRowIntegral a b C lam ell N mu F i

theorem higherBandPhysicalIntegral_selected {a b C lam ell N mu : ℝ}
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    {i : Fin (D-2) × Bool} (hi : HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral a b C lam ell N mu F i =
      higherBandFamilyRowIntegral a b C lam ell N mu F i := by
  unfold higherBandPhysicalIntegral
  by_cases hf : i.2 = true
  · rw [ite_eq_left hf, ite_eq_left (hi.2.1 hf)]
  · rw [ite_eq_right hf]

theorem higherBandPhysicalIntegral_unselected_zero {a b C lam ell N mu : ℝ}
    (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    {i : Fin (D-2) × Bool} (hi : ¬HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral a b C lam ell N mu F i = 0 := by
  rcases i with ⟨j, fine⟩
  cases fine
  · simp [higherBandPhysicalIntegral]
    have hT  :=
      lt_min (by linarith) (hnu j)
    let targetScale := higherBandTargetScale d (j.val+3) N mu
    by_cases hT1 : 1 ≤ min ell (targetScale)
    · have hz : higherBandRowMass d (j.val+3) D D q a b C lam ell
          (min ell (targetScale)) false = 0 := by
        have hn := higherBandRowMass_nonneg d (j.val+3) D D q a b C lam ell
          (min ell (targetScale)) false
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        change (1 ≤ min ell (targetScale)) ∧
          (false = true → ell < targetScale) ∧
          j.val+3 ≤ D ∧ 0 < higherBandRowMass d (j.val+3) D D q a b C lam ell
            (min ell (targetScale)) false
        grind
      have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,false))
          (higherBandFamilyGuardDegree M (j,false)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,false)) false = 0 := by
        solve_by_elim [higherBand_zero_mass_signed_zero]
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,false))
          (higherBandFamilyGuardDegree M (j,false)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,false)) false = 0 := higherBand_coarse_below_one_signed_zero (hT := hT) (hT1 := (not_le.mp hT1)) ..
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
  · simp only [higherBandPhysicalIntegral, ite_true, higherBandFamilyTarget]
    by_cases hactive : ell < higherBandTargetScale d (j.val+3) N mu
    · have hT1  := hell.trans hactive.le
      have hz : higherBandRowMass d (j.val+3) M D q a b C lam ell
          (higherBandTargetScale d (j.val+3) N mu) true = 0 := by
        have hn := higherBandRowMass_nonneg d (j.val+3) M D q a b C lam ell
          (higherBandTargetScale d (j.val+3) N mu) true
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        exact ⟨hT1, fun _ => hactive, hFine j hactive, hp⟩
      have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,true))
          (higherBandFamilyGuardDegree M (j,true)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,true)) true = 0 := by
        solve_by_elim [higherBand_zero_mass_signed_zero]
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · rw [ite_eq_right hactive]

include hell hnu hFine in
theorem higherBandFamily_signedIntegral_sum_eq_physical :
    (∑ i : HigherBandFamilyIndex d D M q a b C lam ell N mu,
      higherBandFamilyRowIntegral a b C lam ell N mu F i.val) =
      ∑ i, higherBandPhysicalIntegral a b C lam ell N mu F i := by
  classical
  exact (Finset.sum_congr_set {i | HigherBandFamilySelected d D M q a b C lam ell N mu i}
    (higherBandPhysicalIntegral a b C lam ell N mu F)
    (fun i => higherBandFamilyRowIntegral a b C lam ell N mu F i.val)
    (fun i hi => higherBandPhysicalIntegral_selected F hi)
    (fun i hi => higherBandPhysicalIntegral_unselected_zero hell hnu hFine F hi)).symm

end NearlyMinimax
