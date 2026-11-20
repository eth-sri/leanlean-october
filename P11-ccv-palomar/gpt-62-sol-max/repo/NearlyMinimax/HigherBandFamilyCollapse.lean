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

def higherBandCoarseFirstAction {d n : ℕ} (ad bd lam ell N mu : ℝ)
    (r D q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  higherBandFirstAction ad bd lam ell (min ell (higherBandTargetScale d r N mu)) r D D q C false U p c Φ

def higherBandFineFirstAction {d n : ℕ} (ad bd lam ell N mu : ℝ)
    (r M D q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  if ell < higherBandTargetScale d r N mu then
    higherBandFirstAction ad bd lam ell (higherBandTargetScale d r N mu) r M D q C true U p c Φ else 0

section
variable {d n : ℕ} (ad bd lam ell N mu : ℝ)

theorem higherBandFamilyFirstAction_coarse_fine
    (D M q : ℕ) (C : ℝ) (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c Φ =
      (∑ j : Fin (D-2), higherBandCoarseFirstAction ad bd lam ell N mu (j.val+3) D q C U p c Φ) +
      (∑ j : Fin (D-2), higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ) := by
  rw [higherBandFamilyFirstAction, higherBandFamilyFirstAction_eq_physical ad bd lam ell N mu D M q C hell hnu hFine U p c Φ,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, higherBandPhysicalFirstAction, higherBandFamilyTarget,
    higherBandFamilyUpper, higherBandFamilyGuardDegree, Bool.false_eq_true, ite_false, ite_true,
    false_implies, true_implies, higherBandCoarseFirstAction, higherBandFineFirstAction,
    Finset.sum_add_distrib]
  ring

section
variable (ha : 0 < ad) (hab : ad < bd)
include ha hab

theorem higherBandCoarseFirstAction_zero_other_count (hell : 0 < ell)
    (r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hne : n ≠ r)
    (hnu : 0 < higherBandTargetScale d r N mu) (C : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandCoarseFirstAction ad bd lam ell N mu r D q C U p c Φ = 0 := by
  unfold higherBandCoarseFirstAction
  by_cases hT : 1 ≤ min ell (higherBandTargetScale d r N mu)
  · apply higherBandFirstAction_zero_other_count <;> assumption
  · have hz := higherBand_coarse_below_one_signed_zero d r D D q ad bd C lam ell _ (lt_min hell hnu) (not_le.mp hT)
    unfold higherBandSignedRow at hz
    simp [higherBandFirstAction, highPacketFirstAction, hz]

theorem higherBandFineFirstAction_zero_small_count (hell : 1 ≤ ell)
    (r M D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hnr : n < r) (C : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFineFirstAction ad bd lam ell N mu r M D q C U p c Φ = 0 := by
  unfold higherBandFineFirstAction
  split_ifs with hactive
  · exact higherBandFirstAction_zero_small_count ad bd lam ell _ ha hab (hell.trans hactive.le)
      r M D q hr hD hnD hnr C true U hU p hp c Φ
  rfl

section
variable (hlam : 0 ≤ lam) (hell : 1 ≤ ell)
include hlam hell

theorem higherBand_matched_coarse_fine
    (M D q : ℕ) (hn : 2 ≤ n) (hD : 1 ≤ D) (hnD : n ≤ D)
    (hnu : 0 < higherBandTargetScale d n N mu)
    (hFine : ell < higherBandTargetScale d n N mu → n ≤ M) (C : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandCoarseFirstAction ad bd lam ell N mu n D q C U p c Φ +
      higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c Φ := by
  have hell0 : 0 < ell := by linarith
  by_cases hT : 1 ≤ higherBandTargetScale d n N mu
  · have hc := higherBandFirstAction_target_count ad bd lam ell (min ell (higherBandTargetScale d n N mu))
      ha hab hlam hell0 (le_min hell hT) D D q hn hD hnD hnD C false U hU p hp c Φ
    unfold higherBandCoarseFirstAction higherBandFineFirstAction
    rw [hc]
    by_cases hactive : ell < higherBandTargetScale d n N mu
    · rw [ite_eq_left hactive, higherBandFirstAction_target_count ad bd lam ell _ ha hab hlam hell0 hT
        M D q hn hD hnD (hFine hactive) C true U hU p hp c Φ]
      simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
        min_eq_left hactive.le]
      rw [← mul_add, ← responseMatrixAction_matrix_add]
      congr 2
      funext i j
      unfold globalCardinalBandMatrix
      ring
    · rw [ite_eq_right hactive]
      simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, min_eq_right (le_of_not_gt hactive), add_zero]
  · have hTlt := not_le.mp hT
    have hmin :=
      min_eq_right (hTlt.le.trans hell)
    unfold higherBandCoarseFirstAction higherBandFineFirstAction higherBandFirstAction
    unfold highPacketFirstAction
    have hz := higherBand_coarse_below_one_signed_zero d n D D q ad bd C lam ell _ (lt_min hell0 hnu)
      (by linarith)
    unfold higherBandSignedRow at hz
    rw [hz]
    have hactive : ¬ell < higherBandTargetScale d n N mu := by linarith
    rw [ite_eq_right hactive]
    simp only [VectorMeasure.integral_zero_vectorMeasure, add_zero]
    have hmat : (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U : HighFrameIndex d D → _ → ℝ) =
        fun _ _ => 0 := by
      funext i j
      exact integrated_cardinal_matrix_below_one_eq_zero lam hnu hTlt U i j
    rw [hmat, responseMatrixAction_matrix_zero, mul_zero]

/-- The selected genuine higher family is exactly its matched full target
plus ordinary fine rows with strictly smaller target counts. -/
theorem higherBandFamilyFirstAction_matched_and_fine_below
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C : ℝ) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c Φ +
      ∑ j : Fin (D-2), if j.val+3 < n then
        higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ else 0 := by
  have hD : 1 ≤ D := by omega
  have hell0 : 0 < ell := by linarith
  let b : Fin (D-2) := ⟨n-3, by omega⟩
  have hb : b.val+3 = n := by dsimp [b]; omega
  have hcSum : (∑ j : Fin (D-2), higherBandCoarseFirstAction ad bd lam ell N mu (j.val+3) D q C U p c Φ) =
      higherBandCoarseFirstAction ad bd lam ell N mu n D q C U p c Φ := by
    calc
      _ = higherBandCoarseFirstAction ad bd lam ell N mu (b.val+3) D q C U p c Φ := by
        apply Finset.sum_eq_single b
        · grind [higherBandCoarseFirstAction_zero_other_count]
        grind
      _ = _ := by rw [hb]
  have hfPoint (j : Fin (D-2)) :
      higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ =
        (if j = b then higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ else 0) +
        (if j.val+3 < n then higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ else 0) := by
    grind [higherBandFineFirstAction_zero_small_count]
  have hfSum : (∑ j : Fin (D-2), higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ) =
      higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ +
      ∑ j : Fin (D-2), if j.val+3 < n then
        higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ else 0 := by
    calc
      _ = ∑ j : Fin (D-2), ((if j = b then higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ else 0) +
        (if j.val+3 < n then higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c Φ else 0)) :=
          Finset.sum_congr rfl (fun j _ => hfPoint j)
      _ = _ := by norm_num [Finset.sum_add_distrib]
  have hnupos : 0 < higherBandTargetScale d n N mu := by simpa only [hb] using hnu b
  have hFineN : ell < higherBandTargetScale d n N mu → n ≤ M := by simpa only [hb] using hFine b
  rw [higherBandFamilyFirstAction_coarse_fine ad bd lam ell N mu D M q C hell hnu hFine U p c Φ, hcSum, hfSum,
    ← add_assoc, higherBand_matched_coarse_fine ad bd lam ell N mu ha hab hlam hell M D q (by omega) hD hnD hnupos hFineN C U hU p hp c Φ]

end

end

end

end NearlyMinimax
