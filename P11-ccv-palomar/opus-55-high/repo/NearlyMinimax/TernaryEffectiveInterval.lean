module

public import NearlyMinimax.LowSmoothnessPrior
public import RoughRegime.Macro
public import NearlyMinimax.Clipping
public import RoughRegime.Notation


𝗍

/-! The actual ternary neighborhood lies in the effective original
variance interval, including the fourth-moment cap. -/
open Set
𝚨

 theorem LowSmoothnessTernaryConstants.effective_interval
    (Q : LowSmoothnessTernaryConstants C)
    (hV : |𝖮₂| ≤ Q.ρ) : V ∈ 𝙸₁ := by
  have h := Q.legal 0 V  𝖤₃  hV
  have hp' : 0 < 1 - V / Q.a^2 := by simpa [ternaryMass] using Q.c_pos.trans_le $ h.2.2.1 1
  have hfourth : Q.a^2*V ≤ C.fourthBound := by
    have hf := h.2.2.2
    rw [ternary_fourth_central_moment Q.a 0 V Q.a_pos.ne'] at hf
    simpa using hf
  obtain ⟨θ,hθ,hθV⟩ := uniformZeroParameter_admissible C Q.a V Q.a_pos h.1.le h.2.1.le ((div_lt_one $ sq_pos_of_pos Q.a_pos ).mp 𝖡₄ ) hfourth
  simpa only [hθV,effectiveVarianceUpper] using admissible_variance_effective_interval C θ hθ
