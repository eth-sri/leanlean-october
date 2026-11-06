module

public import NearlyMinimax.HighUnionScore
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact sum of window scores under a genuine squared partition of unity.
This algebra counts the common variance derivative once. -/
𝚯
𝚪
𝚨
𝚰
𝚬

 set_option hygiene false
𝗇 𝔄 𝙿* ∏ l ∈ Finset.univ.erase i, ternaryMass a (f l) V (y l)
𝗇 𝔉 𝗊
𝗇 𝔅 𝙎*𝔉
𝗇 𝔇 w j i ^2
𝗇 𝔈 𝙔
𝗃 𝔊 ἀ (π j) (activation j) a V η
𝗃 𝔍 ∑ ἀ, 𝔇 * 𝔄
theorem highMarkedLocalScore_sum_of_partition
    [Fintype J] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    (π : J → Measure E) (activation : J → 𝙏) (a V η : ℝ)
    (p : 𝔈) (pReset : J → E → 𝔈)
    (cReset : J → E → 𝙛) (g w : J → 𝔈)
    (φ : J → Fin n → 𝙛) (c : J → 𝙛) f
    (hreg : ∀ j, 𝗢₂ = f)
    (hpartition : ∀ i, ∑ j, 𝔇 = 1) y :
     ∑ j, 𝔊 highMarkedLocalScore p (pReset j)
      (cReset j) (g j) (w j) (φ j) (c j) y =
    ( ∑ j, 𝔊 highMarkedResponseAction
      (pReset j) (cReset j) (g j) (w j) (φ j) y -
      𝔅*∑ i, 𝔄) /
      (𝔉*∏ i, ternaryMass a (f i) V (y i)) := by
  unfold highMarkedLocalScore highResponseProduct highResponseVarianceTerm
  simp_rw [hreg]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  congr 2
  calc
     ∑ j, 𝔅*𝔍 i =
      𝔅*∑ j, 𝔍 i := by rw [Finset.mul_sum]
    _ = 𝔅*∑ i, 𝔍 j := by rw [Finset.sum_comm]
    𝘿 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, hpartition, one_mul]
