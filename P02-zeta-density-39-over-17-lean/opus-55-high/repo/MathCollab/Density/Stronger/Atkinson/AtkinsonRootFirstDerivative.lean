module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootPhase
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

set_option hygiene false in
macro "pf_144" x1:ident x2:ident x3:term:max x4:term:max : tactic => `(tactic| (
  have hd (y : ℝ) (hy : y ∈ Icc a c) :
      deriv (atkinsonRootPhase T b) y = atkinsonRootSlope T b y :=
    (hasDerivAt_atkinsonRootPhase T b (ha.trans_le hy.1)).deriv
  apply $x1:ident hac (by norm_num : (0 : ℝ) < 2)
    (fun y hy => contDiffAt_atkinsonRootPhase T b (ha.trans_le hy.1))
  · intro y hy
    rw [hd y hy]
    exact $x2:ident hT (ha.trans_le hy.1) ($x3:term $x4:term)
  · intro x hx y hy hxy
    rw [hd x hx, hd y hy]
    exact (atkinsonRootSlope_strictAnti hT.le b).antitoneOn
      (ha.trans_le hx.1) (ha.trans_le hy.1) hxy))
section
variable {T b a c : ℝ} (hT : 0 < T) (ha : 0 < a) (hac : a ≤ c)
include T b a c hT ha hac
theorem norm_atkinsonRootPhase_integral_right
    (hr : atkinsonSaddleRoot (T / (2 * Real.pi)) b + 1 ≤ a) :
    ‖∫ y in a..c, Complex.exp (2 * Real.pi * I * (atkinsonRootPhase T b y : ℂ))‖ ≤
      1 / (2 * Real.pi) := by pf_144 norm_phaseIntegral_le_of_negative_slope atkinsonRootSlope_le_neg_two hr.trans hy.1

theorem norm_atkinsonRootPhase_integral_left
    (hr : c ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - 1) :
    ‖∫ y in a..c, Complex.exp (2 * Real.pi * I * (atkinsonRootPhase T b y : ℂ))‖ ≤
      1 / (2 * Real.pi) := by pf_144 norm_phaseIntegral_le_of_positive_slope two_le_atkinsonRootSlope hy.2.trans hr
end

end MathCollab.Density.Stronger.Atkinson
