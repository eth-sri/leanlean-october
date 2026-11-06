module

public import NearlyMinimax.PaperGoals
public import RoughRegime.Macro
public import NearlyMinimax.Chebyshev
public import RoughRegime.Notation

𝗍

/-! The paper's numerical constants and conditional analytic corollaries.
The results involving minimax rates explicitly assume `MainBracketClaim`.
-/

𝚷
𝚶
𝚨

theorem paperTau_pos (C : ModelConstants d) : 0 < paperTau C := by
  have hs :=
    Real.sqrt_lt_sqrt C.densityLower_pos.le $ C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hl := Real.sqrt_pos.mpr C.densityLower_pos
  apply Real.log_pos
  bound

theorem paper_stretchConstant_pos (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    0 < 𝗙₂ :=
  stretchConstant_pos hreg.1 hreg.2 $ paperTau_pos C
