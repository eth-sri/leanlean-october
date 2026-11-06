module

public import NearlyMinimax.PaperGoals
public import NearlyMinimax.Chebyshev

@[expose] public section

/-! The paper's numerical constants and conditional analytic corollaries.
The results involving minimax rates explicitly assume `MainBracketClaim`.
-/

noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

section
variable {d : ℕ} (C : ModelConstants d)

theorem paperTau_pos  : 0 < paperTau C := by
  have hab  :=
    C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hs  :=
    Real.sqrt_lt_sqrt C.densityLower_pos.le hab
  have hl  := Real.sqrt_pos.mpr C.densityLower_pos
  apply Real.log_pos
  apply (one_lt_div (sub_pos.mpr hs)).mpr
  linarith

theorem paper_stretchConstant_pos 
    (hreg : highSmoothnessRegime C) :
    0 < stretchConstant C.smoothness d (paperTau C) :=
  stretchConstant_pos hreg.1 hreg.2 (paperTau_pos C)
end


end NearlyMinimax
