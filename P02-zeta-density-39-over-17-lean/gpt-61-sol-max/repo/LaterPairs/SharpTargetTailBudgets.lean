module
import Mathlib
public import LaterPairs.PhysicalTargetWindows
public import RightSolidTailBudgets

@[expose] public section

namespace Montgomery.RationalMoment

section
variable {σ : ℝ}
include σ

/-- Exact genuine-pair tail budgets over the full closed target row6. -/
theorem sharp_row6_tail_budgets 
    (hl : 1959705/2298302 ≤ σ) (_hr : σ ≤ 6482825/7570038) :
    let a : ℝ := 597962/(2187648*σ-772245)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(47947/86410:ℝ)/(107193/345640)-(4+(2+4*(47947/86410))/(107193/345640))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 2187648*σ-772245 := by linarith
  rw [show (1:ℝ)+(47947/86410)/(107193/345640)=298981/107193 by norm_num,
    show (4:ℝ)+(2+4*(47947/86410))/(107193/345640)=629068/35731 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Exact genuine-pair tail budgets over the full closed target row7. -/
theorem sharp_row7_tail_budgets 
    (hl : 6482825/7570038 ≤ σ) (_hr : σ ≤ 2905/3354) :
    let a : ℝ := 16504356/(62198298*σ-22870785)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(2754695/4856993:ℝ)/(1371394/4856993)-(4+(2+4*(2754695/4856993))/(1371394/4856993))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 62198298*σ-22870785 := by linarith
  rw [show (1:ℝ)+(2754695/4856993)/(1371394/4856993)=4126089/1371394 by norm_num,
    show (4:ℝ)+(2+4*(2754695/4856993))/(1371394/4856993)=13109171/685697 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Exact genuine-pair tail budgets over the full closed target row8. -/
theorem sharp_row8_tail_budgets 
    (hl : 2905/3354 ≤ σ) (_hr : σ ≤ 7/8) :
    let a : ℝ := 2172/(8226*σ-3045)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(365/641:ℝ)/(178/641)-(4+(2+4*(365/641))/(178/641))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 8226*σ-3045 := by linarith
  rw [show (1:ℝ)+(365/641)/(178/641)=543/178 by norm_num,
    show (4:ℝ)+(2+4*(365/641))/(178/641)=1727/89 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Identification with the requested row6 density exponent. -/
theorem sharp_row6_density_exponent  :
    3*(597962/(2187648*σ-772245))*(1-σ) =
      597962*(1-σ)/(729216*σ-257415) := by grind

/-- Identification with the requested row7 density exponent. -/
theorem sharp_row7_density_exponent  :
    3*(16504356/(62198298*σ-22870785))*(1-σ) =
      16504356*(1-σ)/(20732766*σ-7623595) := by grind

/-- Identification with the requested row8 density exponent. -/
theorem sharp_row8_density_exponent  :
    3*(2172/(8226*σ-3045))*(1-σ) =
      2172*(1-σ)/(2742*σ-1015) := by grind
end



