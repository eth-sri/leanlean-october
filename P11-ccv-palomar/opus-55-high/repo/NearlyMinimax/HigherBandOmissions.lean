module

public import NearlyMinimax.HigherBandFamily
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact omission of zero-variation rows and positive subunit scale rows
from the actual finite signed family. A subunit interpolation target remains
zero; no zero-defect assertion is made for that source branch. -/
𝚫
𝚪
𝚨
𝚩
𝚱
𝚬

theorem centered_cardinal_measure_below_one_eq_zero (i : Fin n) d
    (hT : 𝗹₁) (hT1 : T < 1) : centeredCardinalMeasure i d T = 0 := by
  simp only [centeredCardinalMeasure, spatialScaleMeasure,
    spatial_scale_domain_empty_below_one i hT hT1, Measure.restrict_empty, Measure.zero_prod]

theorem cardinal_separated_measure_below_one_eq_zero d n
    (hT : 𝗹₁) (hT1 : T < 1) : 𝚠₂ = 0 := by
  unfold cardinalSeparatedMeasure
  simp_rw [centered_cardinal_measure_below_one_eq_zero _ d hT hT1, Measure.map_zero]
  exact Finset.sum_const_zero

theorem higherBand_coarse_below_one_signed_zero d r m D q a b C lam L T
    (hT : 𝗹₁) (hT1 : T < 1) : higherBandSignedRow d r m D q a b C lam L T false = 0 := by
  rw [higherBandSignedRow, higherBandCarrierMeasure,
    cardinal_separated_measure_below_one_eq_zero d r hT hT1, highPacketSignedMeasure, Measure.zero_prod]
  ext1 s hs
  rw [withDensityᵥ_apply  𝖢₄  hs]
  simp

𝗇 𝔅 Fin 𝘐
𝗇 𝔟 higherBandFamilyGuardDegree M i
𝗃 𝔢 ἀ d $ higherBandFamilyTarget i
𝗇 𝔎 𝔢 HigherBandRowMark 𝔟 D q i.2 → ℝ
𝗇 𝔠 𝔅 × Bool
𝗇 𝔙 (i : 𝔠) → 𝔎
𝗇 𝔜 higherBandFamilyUpper d ell N mu
def higherBandFamilyRowIntegral (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : 𝔙)
    (i : 𝔠) : ℝ :=
  ∫ᵛ e, F i e ∂<•𝔢 higherBandSignedRow 𝔟 D q
    a b C lam ell (𝔜 i) i.2

𝗃 𝔖 ἀ d D M q a b C lam ell N mu
𝗇 𝔓 𝔖 higherBandFamilyRowIntegral F
𝗇 𝔉 𝔓 i
def higherBandPhysicalIntegral (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : 𝔙)
    (i : 𝔠) : ℝ :=
  if i.2 = true then
    if ell < 𝔢 higherBandTargetScale N mu then
      𝔉 else 0
  else 𝔉

𝗇 𝔒 𝔖 higherBandPhysicalIntegral F
𝗇 𝔊 𝔒 i
𝗇 𝔍 𝔖 HigherBandFamilySelected i
theorem higherBandPhysicalIntegral_selected d D M q a b C lam ell N mu
    F
    i (hi : 𝔍) :
    𝔊 =
      𝔉 := by
  unfold higherBandPhysicalIntegral
  by_cases hf : i.2 = true
  · rw [ite_eq_left hf, ite_eq_left $ hi.2.1 hf ]
  simp_all

𝗇 𝔄 higherBandTargetScale d 𝙳 N mu
𝗇 𝔞 (j,false)
𝗇 𝔇 higherBandSignedRow d (higherBandFamilyTarget 𝔞) (higherBandFamilyGuardDegree M 𝔞) D q a b C lam ell (𝔜 𝔞) false = 0
𝗇 𝔈 𝙳
𝗇 𝔔 min ell 𝔄
𝗃 𝔗 ἀ d 𝔈 D D q a b C lam ell
𝗇 𝔐 𝔗 higherBandRowMass 𝔔 false
𝗇 𝔑 ∀ j : 𝔅, ell < 𝔄 → 𝔈 ≤ M
𝗃 𝔘 ἀ d 𝔈 M D q a b C lam ell
𝗇 𝔚 (j,true)
𝗇 𝔛 ∀ j : 𝔅, 0 < 𝔄
theorem higherBandPhysicalIntegral_unselected_zero d D M q a b C lam ell N mu
    (hell : 𝗲₁)
    (hnu : 𝔛)
    (hFine : 𝔑)
    F
    i (hi : ¬𝔍) :
    𝔊 = 0 := by
  rcases i with ⟨j, fine⟩
  cases fine
  · simp only [higherBandPhysicalIntegral]
    by_cases hT1 : 1 ≤ 𝔔
    · have hz : 𝔐 = 0 := by
        have hn := 𝔗 higherBandRowMass_nonneg
          𝔔 false
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        change 1 ≤ 𝔔 ∧
          (false = true → ell < 𝔄) ∧
          𝔈 ≤ D ∧ 0 < 𝔐
        exact ⟨hT1, (by intro h; cases h), 𝖡₃ , hp⟩
      have hzero : 𝔇 := 𝔗 higherBand_zero_mass_signed_zero _ hT1 false hz
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · have hzero : 𝔇 := 𝔗 higherBand_coarse_below_one_signed_zero _ (lt_min  𝖡₄  $ hnu j ) $ not_le.mp hT1
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
  · simp only [higherBandPhysicalIntegral, ite_true, higherBandFamilyTarget]
    by_cases hactive : ell < 𝔄
    · have hT1 := hell.trans hactive.le
      have hz : 𝔘 higherBandRowMass
          𝔄 true = 0 := by
        have hn := 𝔘 higherBandRowMass_nonneg
          𝔄 true
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        exact ⟨hT1, fun _ => hactive, hFine j hactive, hp⟩
      have hzero : higherBandSignedRow d (higherBandFamilyTarget 𝔚)
          (higherBandFamilyGuardDegree M 𝔚) D q a b C lam ell
          (𝔜 𝔚) true = 0 := 𝔘 higherBand_zero_mass_signed_zero _ hT1 true hz
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · rw [ite_eq_right hactive]

𝗇 𝔏 𝔓 i.val
theorem higherBandFamily_signedIntegral_sum_eq_physical d D M q a b C lam ell N mu
    (hell : 𝗲₁)
    (hnu : 𝔛)
    (hFine : 𝔑)
    F :
     ∑ i : 𝔖 HigherBandFamilyIndex,
      𝔏 =
      ∑ i : 𝔠, 𝔊 := by
  classical
  exact (Finset.sum_congr_set {i | 𝔍}
    𝔒
    (fun i => 𝔏)
    (fun i hi => 𝔖 higherBandPhysicalIntegral_selected F i hi)
     fun i hi => 𝔖 higherBandPhysicalIntegral_unselected_zero hell hnu hFine F i hi ).symm
