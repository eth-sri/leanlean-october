module

public import NearlyMinimax.HigherBandFamilyCollapse


@[expose] public section

/-! Exact finite-target reindexing and full-response ordinary-fine-alias
identification for the genuine selected higher family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

theorem higherBand_alias_index_sum_eq (d D n : ℕ) (ell N mu : ℝ) (A : ℕ → ℝ) :
    (∑ j : Fin (D-2), if j.val+3 < n then
      (if ell < higherBandTargetScale d (j.val+3) N mu then A (j.val+3) else 0) else 0) =
      ∑ r ∈ (ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n), A r := by
  classical
  have hi (j : Fin (D-2)) :
      (if j.val+3 < n then (if ell < higherBandTargetScale d (j.val+3) N mu then A (j.val+3) else 0) else 0) =
      if j.val+3 < n ∧ ell < higherBandTargetScale d (j.val+3) N mu then A (j.val+3) else 0 := by
    grind
  simp_rw [hi]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val+3)
  · intro j hj
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      grind
    · exact ((Finset.mem_filter.mp hj).2).1
  · omega
  · intro r hr
    have hI := Finset.mem_filter.mp (Finset.mem_filter.mp hr).1
    have hrd := Finset.mem_range.mp hI.1
    let j : Fin (D-2) := ⟨r-3, by omega⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by aesop⟩, (by dsimp [j]; omega)⟩
  · simp

variable {d D n : ℕ} {ad bd lam : ℝ} {F M : ℕ} {ell N mu : ℝ} (ha : 0 < ad) (hab : ad < bd)
    (hlam : 0 ≤ lam) (hell : 1 ≤ ell)

theorem higherBandFine_below_eq_alias_family
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hell : 1 ≤ ell)
    (D M q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (C a V eta : ℝ)
    {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (y : TernaryVector n) :
    (∑ j : Fin (D-2), if j.val+3 < n then
      higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M q C U p c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) else 0) =
      ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n))
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y := by
  unfold higherBandFineFirstAction
  have he : (∑ j : Fin (D-2), if j.val+3 < n then
      (if ell < higherBandTargetScale d (j.val+3) N mu then
        higherBandFirstAction ad bd lam ell (higherBandTargetScale d (j.val+3) N mu) (j.val+3) M q C true U p c
          (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) else 0) else 0) =
      ∑ j : Fin (D-2), if j.val+3 < n then
        (if ell < higherBandTargetScale d (j.val+3) N mu then
          ordinaryFineAliasRawAction ad bd lam ell (higherBandTargetScale d (j.val+3) N mu)
            M (j.val+3) q C a V eta U p g w c y else 0) else 0 := by
    grind [higherBandFirstAction_fine_eq_aliasRawAction]
  rw [he]
  exact higherBand_alias_index_sum_eq d D n ell N mu
    (fun r => ordinaryFineAliasRawAction ad bd lam ell (higherBandTargetScale d r N mu) M r q C a V eta U p g w c y)

include ha hab hlam hell in
theorem higherBandFamilyFirstAction_matched_and_alias_raw
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C a V eta : ℝ) {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (y : TernaryVector n) :
    higherBandFamilyFirstAction ad bd lam ell N mu M q C U p c
      (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) +
      ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n))
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y := by
  rw [higherBandFamilyFirstAction_matched_and_fine_below ha hab hlam hell D M q hn hnD hnu hFine C hU hp c,
    higherBandFine_below_eq_alias_family ad bd lam ell N mu ha hab hlam hell D M q (by omega) hnD C a V eta hU p g w hp c y]

theorem ordinaryFineAliasFamilyRawAction_below_eq_zero
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hnM : n ≤ M) (C a V eta : ℝ)
    (U : DesignSample d n) (p g w : Fin n → ℝ) (c : HighFrameVector d F)
    (y : TernaryVector n) :
    ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n))
      ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  have hfilter := Finset.mem_filter.mp hr
  have htarget := Finset.mem_filter.mp hfilter.1
  unfold ordinaryFineAliasRawAction
  rw [densityCountCoefficient_exact ad bd ha hab M r n (by omega) (hfilter.2).le hnM, if_neg (by omega), zero_mul]

theorem ordinaryFineAliasTargetSet_below_eq (hMn : M < n)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) :
    (ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n) = ordinaryFineAliasTargetSet d D ell N mu := by
  apply Finset.filter_eq_self.mpr
  intro r hr
  have htarget := Finset.mem_filter.mp hr
  have hrd := Finset.mem_range.mp htarget.1
  let j : Fin (D-2) := ⟨r-3, by omega⟩
  have hj : j.val+3 = r := by dsimp [j]; omega
  have hm := hFine j (by grind)
  omega

include ha hab hlam hell in
/-- Before M the ordinary fine aliases cancel exactly. Beyond M every
active fine target is strictly below the observed count, and its actual
signed action is precisely the full alias family used by the energy theorem. -/
theorem higherBandFamilyFirstAction_matched_and_full_fine_alias
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C a V eta : ℝ) {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (y : TernaryVector n) :
    higherBandFamilyFirstAction ad bd lam ell N mu M q C U p c
      (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ell N mu)
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y else 0) := by
  rw [higherBandFamilyFirstAction_matched_and_alias_raw ha hab hlam hell D M q hn hnD
    hnu hFine C a V eta hU p g w hp c y]
  by_cases hnM : M<n
  · rw [ite_eq_left hnM, ordinaryFineAliasTargetSet_below_eq hnM hFine]
  · rw [ite_eq_right hnM, ordinaryFineAliasFamilyRawAction_below_eq_zero ad bd lam ell N mu ha hab D M q
      (le_of_not_gt hnM) C a V eta U p g w c y]

end NearlyMinimax
