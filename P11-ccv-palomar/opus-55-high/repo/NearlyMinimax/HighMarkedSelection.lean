module

public import NearlyMinimax.HighUnionScore
public import NearlyMinimax.HighSelectedScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact reduction of the complete marked score to observations inside
its true patch. Density resets and regression windows are unchanged
outside the selected coordinates, so their likelihood factors cancel. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

𝗇 𝔏 Finset.univ \ Finset.univ.map e
𝗃 𝔔 ἀ $ e l
section

variable (e : 𝚖₁)
    (F : 𝙔)

theorem finite_product_split_embedding :
     ∏ i : Fin n, F i =
      (∏ i ∈ 𝔏, F i) * ∏ l : Fin r, 𝔔 F := by
  rw [← Finset.prod_sdiff $ Finset.subset_univ $ Finset.univ.map e ]
  simp

theorem finite_sum_split_embedding :
     ∑ i : Fin n, F i =
       ∑ i ∈ 𝔏, F i + ∑ l : Fin r, 𝔔 F := by
  simp

end

section
𝛤

𝗇 𝔙 𝗡 φ
𝗇 𝔐 ternaryMass a (𝔙 c i) V $ y i
𝗃 𝔟 ἀ $ cReset z
𝗇 𝔄 ternaryMass a (𝔟 𝔙 i) V (y i) / 𝔐
𝗇 𝔅 𝖩 * (𝙿 / 𝔐)
𝗇 𝔇 𝔙
𝗇 𝔚 pReset z i / p i
𝗇 𝔈 ∏ i, 𝔚
𝗃 𝔜 ἀ π activation a V η p pReset cReset g w φ c y
𝗇 𝔊 𝔜 highMarkedLocalScore
𝗃 𝔞 ἀ a V η g w φ
𝗇 𝔍 𝔞 highResponseProduct
𝗇 𝔑 ∀ i b, 0 < ternaryMass a (𝔇 c i) V b
𝗇 𝔖 activation z * 𝔈 * ∏ i, 𝔄
𝗇 𝔗 𝗊
𝗇 𝔘 𝗎₂
theorem high_marked_local_score_ratio (π : Measure E) activation
    a V η p pReset
    cReset (g w : 𝙔) φ
    (c : 𝙛) y (hpd : 𝔘)
    (hp : 𝔑) :
    𝔊 =
       ∫ z, 𝔖 ∂π -
      𝙎 * ∑ i, 𝔅 := by
  have hpP : 𝔗 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hpd i
  unfold highMarkedLocalScore highMarkedResponseAction
  rw [sub_div, ← integral_div]
  have hfirst : (fun z => activation z * (∏ i, pReset z i) *
      𝔟 𝔍 y /
        (𝔗 * 𝔍 c y)) =
       fun z => 𝔖 := by
    funext z
    simp
    unfold highResponseProduct
    ring
  rw [hfirst]
  congr 1
  calc
    _ = 𝙎 * ((∑ i, 𝖩 * 𝔞 highResponseVarianceTerm c y i) /
        𝔍 c y) := 𝖧₃
    𝘿 := by
      simp_rw [Finset.sum_div, mul_div_assoc,
        𝔞 high_response_variance_ratio c y _ fun i => 𝚗₁ ]

𝗇 𝔉 𝔔 y
𝗇 𝔎 fun z => pReset z ∘ e
𝗇 𝔒 ternaryMass a (𝔇 c $ e l ) V 𝔉
𝗃 𝔛 ἀ ∘ e
𝗃 𝔓 ἀ π activation a V η 𝔛 p 𝔎 cReset 𝔛 g 𝔛 w 𝔛 φ c 𝔛 y
theorem high_marked_local_score_selected (e : 𝚖₁)
    (π : Measure E) activation a V η
    p pReset cReset
    g w φ (c : 𝙛) y
    (hpd : 𝔘)
    (hp : 𝔑)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    𝔊 =
      𝔓 highMarkedLocalScore := by
  rw [𝔜 high_marked_local_score_ratio hpd hp,
    𝔓 high_marked_local_score_ratio (fun l => 𝔔 hpd)
       fun l b => 𝔔 hp b ]
  have hprod z :
      𝔈 *
          ∏ i, 𝔄 =
      (∏ l : Fin r, pReset z (e l) / 𝔔 p) *
          ∏ l : Fin r, ternaryMass a (𝔟 𝔇 $ e l ) V 𝔉 /
            𝔒 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      finite_product_split_embedding e]
    have ho : ∏ i ∈ 𝔏,
        𝔚 *
          𝔄 = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hv : 𝔟 𝔇 i = 𝔇 c i := by
        simp [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2 ]
      grind
    simp_all
  have hsum : ∑ i, 𝔅 =
      ∑ l : Fin r, 𝔔 w ^ 2 * (ternaryVarianceDerivative a 𝔉 /
        𝔒) := by
    rw [finite_sum_split_embedding e]
    have ho : ∑ i ∈ 𝔏,
        𝔅 = 0 := by
      apply Finset.sum_eq_zero
      simp_all
    linarith
  simp_rw [mul_assoc, hprod, hsum]
  rfl
