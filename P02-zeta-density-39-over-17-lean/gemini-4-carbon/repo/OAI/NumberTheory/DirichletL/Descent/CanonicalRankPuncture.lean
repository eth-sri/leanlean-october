module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteRankNormalized

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseTerminalWidths
local notation "O"=>ActualEisensteinCubic.O

theorem actual_rank_parent_puncture (m:O)(hm:m≠0)(Z:ℝ)(hZ:1<Z):
    (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) :=by
  have hi :=Ideal.span_singleton_eq_bot.not.mpr hm
  have hle := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  unfold normWidth
  rw [Real.rpow_logb (by linarith:0<Z) (ne_of_gt hZ) (actual_ideal_norm_pos _ hi)]
  exact_mod_cast hle

end SevenEighths.InverseMoment

end

end OAI
