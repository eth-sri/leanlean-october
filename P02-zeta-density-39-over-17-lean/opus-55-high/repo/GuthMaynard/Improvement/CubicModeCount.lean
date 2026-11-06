module
public import GuthMaynard.Improvement.RadialRemainder
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace GuthMaynard.Improvement

def cubicModes (U : ℝ) : Finset (ℤ × (ℤ × ℤ)) :=
  (Finset.Icc (-⌊U⌋) ⌊U⌋) ×ˢ ((Finset.Icc (-⌊U⌋) ⌊U⌋) ×ˢ (Finset.Icc (-⌊U⌋) ⌊U⌋))

theorem cubicModes_card {U : ℝ} (hU : 1 ≤ U) : ((cubicModes U).card:ℝ) ≤ 27*U^3 := by
  have hf : 0 ≤ ⌊U⌋ := Int.floor_nonneg.mpr (by linarith)
  have hcZ : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card:ℤ) = 2*⌊U⌋+1 := by
    rw [Int.card_Icc,Int.toNat_of_nonneg (by omega)]
    ring
  have hcR : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card:ℝ) = 2*(⌊U⌋:ℝ)+1 := by exact_mod_cast hcZ
  have hb : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card:ℝ) ≤ 3*U := by
    rw [hcR]
    linarith [Int.floor_le U]
  unfold cubicModes
  rw [Finset.card_product,Finset.card_product]
  push_cast
  calc
    _ ≤ (3*U)*((3*U)*(3*U)) := by gcongr
    _ = _ := by ring

/-- Exact membership in the full symmetric real-frequency truncation. -/
theorem mem_cubicModes (U : ℝ) (m : ℤ × (ℤ × ℤ)) :
    m ∈ cubicModes U ↔ |(m.1:ℝ)| ≤ U ∧ |(m.2.1:ℝ)| ≤ U ∧ |(m.2.2:ℝ)| ≤ U := by
  have hm : ∀ k : ℤ, k ∈ Finset.Icc (-⌊U⌋) ⌊U⌋ ↔ |(k:ℝ)| ≤ U := by
    intro k
    rw [Finset.mem_Icc,abs_le]
    constructor
    · intro hk
      have h₁ : -(k:ℝ) ≤ U := by
        pm_8785 k
        simpa only [Int.cast_neg] using Int.le_floor.mp hz
      exact ⟨by linarith,Int.le_floor.mp hk.2⟩
    · intro hk
      have h₁ : -k ≤ ⌊U⌋ := Int.le_floor.mpr (by push_cast; linarith)
      exact ⟨by omega,Int.le_floor.mpr hk.2⟩
  simp only [cubicModes,Finset.mem_product,hm]

end GuthMaynard.Improvement
