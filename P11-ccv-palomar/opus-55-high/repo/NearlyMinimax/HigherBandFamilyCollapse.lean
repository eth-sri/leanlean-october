module

public import NearlyMinimax.HigherBandTargetAction
public import NearlyMinimax.HighSourceCountCancellation
public import NearlyMinimax.HighSourceFineAliasIdentification
public import NearlyMinimax.OrdinaryFineAliasAggregation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact matched-target and ordinary-fine-alias decomposition of the
actual selected higher family. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 1400000
𝚬

𝗇 𝔞 fun _ _ => 0
section Matrix
𝛑
theorem responseMatrixAction_matrix_zero q C
    (c : 𝙛) Φ : 𝗔 𝔞 c Φ = 0 := by
  simp [responseMatrixAction, covarianceAction, covarianceWeight]
end Matrix

𝗇 𝔊 𝙮 → ℝ
𝗃 𝔨 higherBandTargetScale d ἀ N mu
𝗇 𝔎 𝔨 r
𝗇 𝔏 𝙔
𝗃 𝔜 ἀ ad bd lam ell
def higherBandCoarseFirstAction (ad bd lam ell N mu : ℝ)
    (r D q : ℕ) (C : ℝ) (U : 𝙇) (p : 𝔏)
    (c : 𝔊) (Φ : 𝔊 → ℝ) : ℝ :=
  𝔜 higherBandFirstAction (min ell 𝔎) r D D q C false U p c Φ

def higherBandFineFirstAction (ad bd lam ell N mu : ℝ)
    (r M D q : ℕ) (C : ℝ) (U : 𝙇) (p : 𝔏)
    (c : 𝔊) (Φ : 𝔊 → ℝ) : ℝ :=
  if ell < 𝔎 then
    𝔜 higherBandFirstAction 𝔎 r M D q C true U p c Φ else 0

𝗃 𝔥 𝔜 ἀ N mu
𝗇 𝔛 𝔥 higherBandFineFirstAction
𝗇 𝔄 𝔛 𝙳 M D q C U p c Φ
𝗇 𝔅 Fin 𝘐
𝗇 𝔇 𝙳
𝗇 𝔐 𝔥 higherBandFamilyFirstAction D M q C U p c Φ
𝗇 𝔚 𝔥 higherBandCoarseFirstAction
𝗃 𝔦 𝔚 ἀ D q C U p c Φ
𝗇 𝔓 ∑ j : 𝔅, 𝔦 𝔇
𝗇 𝔖 ∀ j : 𝔅, ell < 𝔨 𝔇 → 𝔇 ≤ M
𝗇 𝔗 ∀ j : 𝔅, 0 < 𝔨 𝔇
𝗃 𝔩 ∑ j : 𝔅, ἀ
𝗇 𝔙 𝔩 𝔄
𝗇 𝔟 𝗲₁
𝗃 𝔫 𝔥 ἀ D M q C hell hnu hFine U p c Φ
theorem higherBandFamilyFirstAction_coarse_fine ad bd lam ell N mu
    D M q C (hell : 𝔟)
    (hnu : 𝔗)
    (hFine : 𝔖)
    U (p : 𝔏)
    (c : 𝔊) Φ :
    𝔐 =
      𝔓 +
      𝔙 := by
  rw [higherBandFamilyFirstAction, 𝔫 higherBandFamilyFirstAction_eq_physical,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, higherBandPhysicalFirstAction, higherBandFamilyTarget,
    higherBandFamilyUpper, higherBandFamilyGuardDegree, Bool.false_eq_true, ite_false, ite_true,
    higherBandCoarseFirstAction, higherBandFineFirstAction, Finset.sum_add_distrib]
  ring

𝗇 𝔍 𝖳
𝗇 𝔠 𝖼
𝗇 𝔡 𝖽
𝗇 𝔢 𝗮
𝗇 𝔣 𝖠₁
𝗇 𝔤 𝗒₂
𝗃 𝔧 higherBand_coarse_below_one_signed_zero d ἀ D D q ad bd C lam ell _
theorem higherBandCoarseFirstAction_zero_other_count
    ad bd lam ell N mu (ha : 𝔠) (hab : 𝔡) (hell : 𝚁₁)
    r D q (hr : 𝘗) (hD : 𝔢) (hnD : 𝔣) (hne : n ≠ r)
    (hnu : 0 < 𝔎) C
    U (hU : ∀ i j, |𝔤| ≤ 2)
    (p : 𝔏) (hp : 𝔍)
    (c : 𝔊) Φ :
    𝔦 r = 0 := by
  unfold higherBandCoarseFirstAction
  by_cases hT : 1 ≤ min ell 𝔎
  · exact 𝔜 higherBandFirstAction_zero_other_count _ ha hab hT r D D q hr hD hnD hnD hne C false U hU p hp c Φ
  · unfold higherBandFirstAction
    rw [𝔧 r (lt_min hell hnu) $ not_le.mp hT ]
    simp

𝗃 𝔪 𝔛 ἀ M D q C U p c Φ
theorem higherBandFineFirstAction_zero_small_count
    ad bd lam ell N mu (ha : 𝔠) (hab : 𝔡) (hell : 𝔟)
    r M D q (hr : 𝘗) (hD : 𝔢) (hnD : 𝔣) (hnr : n < r) C
    U (hU : ∀ i j, |𝔤| ≤ 2)
    (p : 𝔏) (hp : 𝔍)
    (c : 𝔊) Φ :
    𝔪 r = 0 := by
  unfold higherBandFineFirstAction
  split_ifs with hactive
  · exact 𝔜 higherBandFirstAction_zero_small_count _ ha hab (hell.trans hactive.le)
      r M D q hr hD hnD hnr C true U hU p hp c Φ
  · rfl

𝗇 𝔈 𝔪 n
𝗇 𝔉 𝔨 n
𝗇 𝔑 𝔦 n
𝗇 𝔔 𝗊 * 𝗔 (integratedCardinalMatrix lam 𝔉 U) c Φ
theorem higherBand_matched_coarse_fine
    (ad bd lam ell N mu : ℝ) (ha : 𝔠) (hab : 𝔡) (hlam : 𝖺) (hell : 𝔟)
    (M D q : ℕ) (hn : 𝗏) (hD : 𝔢) (hnD : 𝔣)
    (hnu : 0 < 𝔉)
    (hFine : ell < 𝔉 → n ≤ M) (C : ℝ)
    U (hU : ∀ i j, |𝔤| ≤ 2)
    (p : 𝔏) (hp : 𝔍)
    (c : 𝔊) Φ :
    𝔑 +
      𝔈 =
      𝔔 := by
  have hell0 : 𝚁₁ := 𝖡₄
  by_cases hT : 1 ≤ 𝔉
  · have hc := 𝔜 higherBandFirstAction_target_count (min ell 𝔉)
      ha hab hlam hell0 (le_min hell hT) D D q hn hD hnD hnD C false U hU p hp c Φ
    unfold higherBandCoarseFirstAction higherBandFineFirstAction
    rw [hc]
    by_cases hactive : ell < 𝔉
    · rw [ite_eq_left hactive, 𝔜 higherBandFirstAction_target_count _ ha hab hlam hell0 hT
        M D q hn hD hnD (hFine hactive) C true U hU p hp c Φ]
      simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
        min_eq_left hactive.le]
      rw [← mul_add, ← responseMatrixAction_matrix_add]
      congr 2
      funext i j
      unfold globalCardinalBandMatrix
      ring
    · rw [ite_eq_right hactive]
      aesop
  · have hTlt := not_le.mp hT
    have hmin :=
      min_eq_right $ hTlt.le.trans hell
    unfold higherBandCoarseFirstAction higherBandFineFirstAction higherBandFirstAction
    rw [𝔧 n (lt_min hell0 hnu)
      𝖡₄ ]
    rw [ite_eq_right 𝖡₄ ]
    simp only [VectorMeasure.integral_zero_vectorMeasure, add_zero]
    have hmat : (integratedCardinalMatrix lam 𝔉 U : 𝙮 → _ → ℝ) =
        𝔞 := by
      funext i j
      exact integrated_cardinal_matrix_below_one_eq_zero ⟨0, 𝖡₃⟩ lam hnu hTlt U i j
    rw [hmat, responseMatrixAction_matrix_zero, mul_zero]

𝗇 𝔒 if 𝔇 < n then 𝔄 else 0
𝗇 𝔘 if j = b then 𝔈 else 0
/-- The selected genuine higher family is exactly its matched full target
plus ordinary fine rows with strictly smaller target counts. -/
theorem higherBandFamilyFirstAction_matched_and_fine_below
    (ad bd lam ell N mu : ℝ) (ha : 𝔠) (hab : 𝔡) (hlam : 𝖺) (hell : 𝔟)
    (D M q : ℕ) (hn : 𝖬₂) (hnD : 𝔣)
    (hnu : 𝔗)
    (hFine : 𝔖)
    (C : ℝ) U (hU : ∀ i j, |𝔤| ≤ 2)
    (p : 𝔏) (hp : 𝔍)
    (c : 𝔊) Φ :
    𝔐 =
      𝔔 +
      𝔩 𝔒 := by
  have hD : 𝔢 := 𝖡₃
  let b : 𝔅 := ⟨n-3, 𝖡₃⟩
  have hb : b.val+3 = n := 𝖤₃
  have hcSum : 𝔓 =
      𝔑 := by
    calc
      _ = 𝔚 (b.val+3) D q C U p c Φ := by
        apply Finset.sum_eq_single b
        · intro j _ hj
          have hne : n ≠ 𝔇 := by
            omega
          exact 𝔥 higherBandCoarseFirstAction_zero_other_count ha hab  𝖡₄ 
            𝔇 D q  𝖡₃  hD hnD hne (hnu j) C U hU p hp c Φ
        simp
      𝘿 := 𝖤₄
  have hfPoint j :
      𝔄 =
        𝔘 +
        𝔒 := by
    by_cases hj : j = b
    · simp_all
    · by_cases hlt : 𝔇 < n
      · simp_all
      · have hgt : n < 𝔇 := by
          omega
        have hz := 𝔥 higherBandFineFirstAction_zero_small_count ha hab hell
          𝔇 M D q  𝖡₃  hD hnD hgt C U hU p hp c Φ
        simp_all
  have hfSum : 𝔙 =
      𝔈 +
      𝔩 𝔒 := by
    calc
      _ = ∑ j : 𝔅, (𝔘 +
        𝔒) :=
          Finset.sum_congr rfl fun j _ => hfPoint j
      𝘿 := by rw [Finset.sum_add_distrib]; simp
  have hnupos : 0 < 𝔉 := by simpa only [hb] using hnu b
  rw [𝔫 higherBandFamilyFirstAction_coarse_fine, hcSum, hfSum,
    ← add_assoc, 𝔥 higherBand_matched_coarse_fine ha hab hlam hell M D q  𝖡₃  hD hnD hnupos (by simpa only [hb] using hFine b) C U hU p hp c Φ]
