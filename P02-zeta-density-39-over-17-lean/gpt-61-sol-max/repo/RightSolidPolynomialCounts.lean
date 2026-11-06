module
public import RightQuadraticParameters

@[expose] public section

open Filter Finset
open scoped Topology
noncomputable section
namespace Montgomery.RationalMoment


/-- The exact five right-hand solid detecting-length exponents. -/
def rightSolidLengthExponent (σ : ℝ) : ℝ :=
  if σ ≤ 29359/37574 then 1/(11*σ-7)
  else if σ ≤ 1015/1294 then 4744/(14610*σ-3849)
  else if σ ≤ 353/447 then 6154/(19062*σ-5079)
  else if σ ≤ 467/586 then 3782/(11808*σ-3195)
  else 2168/(6846*σ-1893)

theorem right_solid_quadratic_window {σ : ℝ} (hl : 7/9 ≤ σ) (hr : σ ≤ 4/5) :
    QuadraticWindow σ (rightSolidLengthExponent σ) := by
  unfold rightSolidLengthExponent
  split_ifs with h₁ h₂ h₃ h₄
  · exact right_quadratic_window_first σ hl h₁
  · exact right_quadratic_window_second σ (by linarith) h₂
  · exact right_quadratic_window_third σ (by linarith) h₃
  · exact right_quadratic_window_fourth σ (by linarith) h₄
  · exact right_quadratic_window_fifth σ (by linarith) hr


