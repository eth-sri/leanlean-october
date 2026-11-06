module
public import GuthMaynard.Improvement.AffineFiniteCover

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

def twoShell (B : ℝ) (i : Bool) : ℕ := if i then 2*⌊B⌋₊ else ⌊B⌋₊

theorem twoShell_pos {B : ℝ} (hB : 1 ≤ B) (i : Bool) : 0 < twoShell B i := by
  have h := Nat.floor_pos.mpr hB
  cases i <;> simp [twoShell] <;> omega

theorem twoShell_le {B : ℝ} (hB : 1 ≤ B) (i : Bool) : (twoShell B i:ℝ) ≤ 2*B := by
  have h := Nat.floor_le (show 0 ≤ B by linarith)
  cases i <;> simp [twoShell] <;> linarith

