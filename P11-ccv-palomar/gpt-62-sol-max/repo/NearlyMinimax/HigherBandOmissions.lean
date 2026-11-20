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

theorem centered_cardinal_measure_below_one_eq_zero {n : ℕ} (i : Fin n) (d : ℕ)
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1) : centeredCardinalMeasure i d T = 0 := by
  simp only [centeredCardinalMeasure, spatialScaleMeasure,
    spatial_scale_domain_empty_below_one i hT hT1, Measure.restrict_empty, Measure.zero_prod]

theorem cardinal_separated_measure_below_one_eq_zero (d n : ℕ) {T : ℝ}
    (hT : 0 < T) (hT1 : T < 1) : cardinalSeparatedMeasure d n T = 0 := by
  unfold cardinalSeparatedMeasure
  simp [centered_cardinal_measure_below_one_eq_zero _ d hT hT1, Measure.map_zero]

theorem higherBand_coarse_below_one_signed_zero (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 0 < T) (hT1 : T < 1) : higherBandSignedRow d r m D q a b C lam L T false = 0 := by
  rw [higherBandSignedRow, higherBandCarrierMeasure,
    cardinal_separated_measure_below_one_eq_zero d r hT hT1, highPacketSignedMeasure, Measure.zero_prod]
  ext1 s hs
  simp [withDensityᵥ_apply (by simp : Integrable _ (0 : Measure _)) hs]

def higherBandFamilyRowIntegral (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  ∫ᵛ e, F i e ∂<•higherBandSignedRow d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ell (higherBandFamilyUpper d ell N mu i) i.2

def higherBandPhysicalIntegral (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true → ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
    higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i else 0

section
variable (d D M q : ℕ) (a b C lam ell N mu : ℝ)

theorem higherBandPhysicalIntegral_selected
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) (hi : HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral d D M q a b C lam ell N mu F i =
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i := if_pos hi.2.1

section
variable (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
include hell hnu hFine

theorem higherBandPhysicalIntegral_unselected_zero
    (i : Fin (D-2) × Bool) (hi : ¬HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral d D M q a b C lam ell N mu F i = 0 := by
  classical
  unfold higherBandPhysicalIntegral
  split_ifs with hactive
  swap
  · rfl
  let T := higherBandFamilyUpper d ell N mu i
  let r := higherBandFamilyTarget i
  let m := higherBandFamilyGuardDegree M i
  have hr : r ≤ m := by
    rcases i with ⟨j, _ | _⟩
    · change j.val + 3 ≤ D
      omega
    · exact hFine j (hactive rfl)
  by_cases hT : 1 ≤ T
  · have hz : higherBandRowMass d r m D q a b C lam ell T i.2 = 0 :=
      le_antisymm (le_of_not_gt fun hp => hi ⟨hT, hactive, hr, hp⟩)
        (higherBandRowMass_nonneg d r m D q a b C lam ell T i.2)
    unfold higherBandFamilyRowIntegral
    rw [higherBand_zero_mass_signed_zero d r m D q a b C lam ell T hT i.2 hz]
    simp
  · rcases i with ⟨j, _ | _⟩
    · have hpos : 0 < T := lt_min (by linarith) (hnu j)
      unfold higherBandFamilyRowIntegral
      rw [higherBand_coarse_below_one_signed_zero d r m D q a b C lam ell T hpos (not_le.mp hT)]
      simp
    · exact (hT (hell.trans (hactive rfl).le)).elim

theorem higherBandFamily_signedIntegral_sum_eq_physical :
    (∑ i : HigherBandFamilyIndex d D M q a b C lam ell N mu,
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i.val) =
      ∑ i : Fin (D-2) × Bool, higherBandPhysicalIntegral d D M q a b C lam ell N mu F i := by
  classical
  exact (Finset.sum_congr_set {i | HigherBandFamilySelected d D M q a b C lam ell N mu i}
    (higherBandPhysicalIntegral d D M q a b C lam ell N mu F)
    (fun i => higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i.val)
    (fun i hi => higherBandPhysicalIntegral_selected d D M q a b C lam ell N mu F i hi)
    (fun i hi => higherBandPhysicalIntegral_unselected_zero d D M q a b C lam ell N mu hell hnu hFine F i hi)).symm

end

end

end NearlyMinimax
