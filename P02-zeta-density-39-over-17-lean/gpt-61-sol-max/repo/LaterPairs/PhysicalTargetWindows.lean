module
import Mathlib
public import LaterPairs.PhysicalDetectorParameters

@[expose] public section

namespace Montgomery.RationalMoment.RightDetector

section
variable {σ : ℝ}
include σ

/-- The full closed row3 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row3  (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) :
    PhysicalDetectorWindow σ (31544/(107010*σ-33609)) := by
  have hd : 0 < 107010*σ-33609 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  all_goals (field_simp <;> nlinarith)

/-- The full closed row4 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row4  (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375) :
    PhysicalDetectorWindow σ (1261710/(4342380*σ-1396527)) := by
  have hd : 0 < 4342380*σ-1396527 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  all_goals (field_simp <;> nlinarith)

/-- The full closed row5 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row5  (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302) :
    PhysicalDetectorWindow σ (3066/(10848*σ-3645)) := by
  have hd : 0 < 10848*σ-3645 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  all_goals (field_simp <;> nlinarith)

/-- The full closed row6 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row6  (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) :
    PhysicalDetectorWindow σ (597962/(2187648*σ-772245)) := by
  have hd : 0 < 2187648*σ-772245 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  all_goals (field_simp <;> nlinarith)

/-- The full closed row7 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row7  (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) :
    PhysicalDetectorWindow σ (16504356/(62198298*σ-22870785)) := by
  have hd : 0 < 62198298*σ-22870785 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  all_goals (field_simp <;> nlinarith)

/-- The full closed row8 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row8  (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) :
    PhysicalDetectorWindow σ (2172/(8226*σ-3045)) := by
  have hd : 0 < 8226*σ-3045 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  all_goals (field_simp <;> nlinarith)
end



