module
public import GuthMaynard.Improvement.AffineFiniteCover

@[expose] public section
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement


def twoShell (B : ℝ) (i : Bool) : ℕ := if i then 2*⌊B⌋₊ else ⌊B⌋₊

section
variable {B : ℝ} (hB : 1 ≤ B) (i : Bool)
include B hB i

theorem twoShell_pos  : 0 < twoShell B i := by
  have h := Nat.floor_pos.mpr hB
  cases i <;> simp [twoShell] <;> omega

theorem twoShell_le  : (twoShell B i:ℝ) ≤ 2*B := by
  have h := Nat.floor_le (show 0 ≤ B by linarith)
  cases i <;> simp [twoShell] <;> linarith
end



