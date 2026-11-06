module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceState
public import OAI.NumberTheory.DirichletL.Moments.UniformRadialComparison

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyReferenceReflection
open CenteredMomentNaturalRowSource
local notation "O"=>HeckeFamily.O

lemma conductorFactor_pos : 0<(fixedConductorFactor:ℝ):=by
  unfold fixedConductorFactor
  norm_cast
  apply Nat.mul_pos
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero))
  simp

end SevenEighths.CenteredMomentEnergyReferenceReflection

end

end OAI
