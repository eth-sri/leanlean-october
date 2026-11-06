module

public import NearlyMinimax.SourceRows
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact finite source activity bookkeeping, with costs derived from
the actual positive separated measures and signed atoms. -/
𝚫
𝚪
𝚨
𝚩
𝚾
𝚬

𝗃 𝔐 ἀ d r m D q
𝗇 𝔈 𝔐 higherBandRowMass_le_activityCap hr hD a b ha hab C lam
theorem higherBandRowMass_le_activityCap_of_fine d r m D q (hr : 𝘠₁) (hD : 𝗮)
    a b (ha : 𝙆) (hab : 𝙭) C lam L T
    (hT : 𝖹) fine (hLT : fine = true → L ≤ T) :
    𝔐 higherBandRowMass a b C lam L T fine ≤ 𝔐 higherBandRowActivityCap a b C lam T := by
  cases fine
  · exact 𝔈 1 T hT hT false
  · exact 𝔈 L T hT (hLT rfl) true

𝗃 𝔑 higherBandFamilyUpper d ℓ N μ ἀ
𝗇 𝔄 𝗤₂ 𝔑 i i.2
𝗇 𝔅 Fin 𝘐
𝗃 𝔍 ἀ d D M q a b C lam ℓ N μ
𝗇 𝔉 𝔍 HigherBandFamilySelected
def higherBandFilteredMass (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : 𝔅 × Bool) : ℝ :=
  if 𝔉 i then
    𝔄 else 0

𝗇 𝔊 𝔍 higherBandFilteredMass
def higherBandCoarseActivity (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (j : 𝔅) : ℝ :=
  𝔊 (j,false)

def higherBandFineActivity (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (j : 𝔅) : ℝ :=
  𝔊 (j,true)

𝗃 𝔎 highRowTotalMass (ἀ d k D M q a b C lam ℓ N μ).rowMass
𝗇 𝔇 𝔎 higherBandFamilyData
𝗃 𝔏 ∑ j : 𝔅, 𝔍 ἀ j
theorem higherBandFamily_totalMass_eq d k D M q a b C lam ℓ N μ :
    𝔇 =
      𝔏 higherBandCoarseActivity +
      𝔏 higherBandFineActivity := by
  classical
  change ∑ i : 𝔍 HigherBandFamilyIndex,
    higherBandRowMass d (higherBandFamilyTarget i.val) 𝚁 D q
      a b C lam ℓ 𝔑 i.val i.val.2 = _
  rw [← Finset.sum_subtype (Finset.univ.filter 𝔉)
     𝖢₄  fun i => 𝔄 ]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]
  exact add_comm ..

theorem sourceRowTotalMass_eq d k D M q a b C lam ℓ N μ :
    𝔎 sourceRowData =
      highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass + singletonRowMass d D q a b C +
      𝔇 := by
  classical
  simp only [highRowTotalMass, Fintype.sum_sum_type, sourceRowData, sourceRowComponent,
    highUnionRowRestrict, Fintype.sum_unique, singletonRowData, higherBandFamilyData, add_assoc]
