module

public import NearlyMinimax.HigherBandTargetAction
public import NearlyMinimax.HighSourceCountCancellation
public import NearlyMinimax.HighSourceFineAliasIdentification
public import NearlyMinimax.OrdinaryFineAliasAggregation


@[expose] public section

/-! Exact matched-target and ordinary-fine-alias decomposition of the
actual selected higher family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem responseMatrixAction_matrix_zero (q : ℕ) (C : ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : responseMatrixAction q C (fun _ _ => 0) c Φ = 0 := by
  simp [responseMatrixAction, covarianceAction, covarianceWeight]
end Matrix

section
variable {d n : ℕ} (ad bd lam ell N mu : ℝ) (r D M q : ℕ) (C : ℝ) (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (U : DesignSample d n) (p : Fin n → ℝ) (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ)

def higherBandCoarseFirstAction : ℝ :=
  higherBandFirstAction ad bd lam ell (min ell (higherBandTargetScale d r N mu)) r D q C false U p c Φ

def higherBandFineFirstAction {D : ℕ} (q : ℕ) (C : ℝ) (U : DesignSample d n) (p : Fin n → ℝ)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) : ℝ :=
  if ell < higherBandTargetScale d r N mu then
    higherBandFirstAction ad bd lam ell (higherBandTargetScale d r N mu) r M q C true U p c Φ else 0

include hell hnu hFine in
theorem higherBandFamilyFirstAction_coarse_fine :
    higherBandFamilyFirstAction ad bd lam ell N mu M q C U p c Φ =
      (∑ j : Fin (D-2), higherBandCoarseFirstAction ad bd lam ell N mu (j.val+3) D q C U p c Φ) +
      (∑ j : Fin (D-2), higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c Φ) := by
  rw [higherBandFamilyFirstAction, higherBandFamilyFirstAction_eq_physical ad bd lam ell N mu D M q C hell hnu hFine U p c Φ,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, higherBandPhysicalFirstAction, higherBandFamilyTarget,
    higherBandFamilyUpper, higherBandFamilyGuardDegree, Bool.false_eq_true, ite_false, ite_true,
    higherBandCoarseFirstAction, higherBandFineFirstAction, Finset.sum_add_distrib]
  exact add_comm _ _

end

section
variable {d n : ℕ} (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd)
include ha hab

theorem higherBandCoarseFirstAction_zero_other_count (hell : 0 < ell)
    {r D : ℕ} (q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hne : n ≠ r)
    (hnu : 0 < higherBandTargetScale d r N mu) (C : ℝ)
    {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    higherBandCoarseFirstAction ad bd lam ell N mu r D q C U p c Φ = 0 := by
  unfold higherBandCoarseFirstAction
  by_cases hT : 1 ≤ min ell (higherBandTargetScale d r N mu)
  · apply higherBandFirstAction_zero_other_count <;> assumption
  · unfold higherBandFirstAction
    rw [higherBand_coarse_below_one_signed_zero d r D D q ad bd C lam ell _ (lt_min hell hnu) (not_le.mp hT)]
    simp

theorem higherBandFineFirstAction_zero_small_count (hell : 1 ≤ ell)
    (r M D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hnr : n < r) (C : ℝ)
    {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    higherBandFineFirstAction ad bd lam ell N mu r M q C U p c Φ = 0 := by
  unfold higherBandFineFirstAction
  grind [higherBandFirstAction_zero_small_count]

end

variable {d n : ℕ} {ad bd lam ell N mu : ℝ} (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hell : 1 ≤ ell)
include ha hab hell hlam

theorem higherBand_matched_coarse_fine
    (M D q : ℕ) (hn : 2 ≤ n) (hD : 1 ≤ D) (hnD : n ≤ D)
    (hnu : 0 < higherBandTargetScale d n N mu)
    (hFine : ell < higherBandTargetScale d n N mu → n ≤ M) (C : ℝ)
    {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    higherBandCoarseFirstAction ad bd lam ell N mu n D q C U p c Φ +
      higherBandFineFirstAction ad bd lam ell N mu n M q C U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c Φ := by
  have hell0 : 0 < ell := by linarith
  by_cases hT : 1 ≤ higherBandTargetScale d n N mu
  · have hc := higherBandFirstAction_target_count
      ha hab hlam hell0 (le_min hell hT) D D q hn hD hnD hnD C false hU hp c Φ
    unfold higherBandCoarseFirstAction higherBandFineFirstAction
    rw [hc]
    by_cases hactive : ell < higherBandTargetScale d n N mu
    · rw [ite_eq_left hactive, higherBandFirstAction_target_count ha hab hlam hell0 hT
        M D q hn hD hnD (hFine hactive) C true hU hp c Φ]
      simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
        min_eq_left hactive.le, globalCardinalBandMatrix]
      rw [← mul_add, ← responseMatrixAction_matrix_add]
      simp [globalCardinalBandMatrix]
    · rw [ite_eq_right hactive]
      simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, min_eq_right (le_of_not_gt hactive), add_zero]
  · have hTlt := not_le.mp hT
    unfold higherBandCoarseFirstAction higherBandFineFirstAction higherBandFirstAction
    rw [higherBand_coarse_below_one_signed_zero d n D D q ad bd C lam ell _ (lt_min hell0 hnu)
      (by bound), ite_eq_right (by linarith)]
    simp only [VectorMeasure.integral_zero_vectorMeasure, add_zero]
    have hmat : (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U : HighFrameIndex d D → _ → ℝ) =
        fun _ _ => 0 := by
      funext i j
      exact integrated_cardinal_matrix_below_one_eq_zero ⟨0, by omega⟩ lam hnu hTlt ..
    rw [hmat, responseMatrixAction_matrix_zero, mul_zero]

/-- The selected genuine higher family is exactly its matched full target
plus ordinary fine rows with strictly smaller target counts. -/
theorem higherBandFamilyFirstAction_matched_and_fine_below
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C : ℝ) {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ell N mu M q C U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c Φ +
      ∑ j : Fin (D-2), if j.val+3 < n then
        higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c Φ else 0 := by
  have hD : 1 ≤ D := by omega
  let b : Fin (D-2) := ⟨n-3, by omega⟩
  have hb : b.val+3 = n := by dsimp [b]; omega
  have hcSum : (∑ j : Fin (D-2), higherBandCoarseFirstAction ad bd lam ell N mu (j.val+3) D q C U p c Φ) =
      higherBandCoarseFirstAction ad bd lam ell N mu n D q C U p c Φ := by
    calc
      _ = _ := by
        apply Finset.sum_eq_single b
        · intro j _ hj
          grind [higherBandCoarseFirstAction_zero_other_count]
        · grind
      _ = _ := by rw [hb]
  have hfPoint j :
      higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c Φ =
        (if j = b then higherBandFineFirstAction ad bd lam ell N mu n M q C U p c Φ else 0) +
        (if j.val+3 < n then higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c Φ else 0) := by
    grind [higherBandFineFirstAction_zero_small_count]
  have hfSum : (∑ j : Fin (D-2), higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c Φ) =
      higherBandFineFirstAction ad bd lam ell N mu n M q C U p c Φ +
      ∑ j : Fin (D-2), if j.val+3 < n then
        higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c Φ else 0 := Eq.trans (Finset.sum_congr rfl (fun j _ => hfPoint j)) (by rw [Finset.sum_add_distrib]; simp)
  have hnupos : 0 < higherBandTargetScale d n N mu := by simpa only [hb] using hnu b
  rw [higherBandFamilyFirstAction_coarse_fine ad bd lam ell N mu D M q C hell hnu hFine U p c Φ, hcSum, hfSum,
    ← add_assoc, higherBand_matched_coarse_fine ha hab hlam hell M D q (by omega) hD hnD hnupos (by simpa only [hb] using hFine b) C hU hp c Φ]

end NearlyMinimax
