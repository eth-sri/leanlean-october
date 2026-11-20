module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Energy.ReferenceState
public import OAI.NumberTheory.DirichletL.Moments.UniformRadialComparison

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentOriginalRadialComparison
open CenteredMomentCommonMaskExpansion CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=>HeckeFamily.O

lemma conductorFactor_pos : 0<(fixedConductorFactor:ℝ):=by
  unfold fixedConductorFactor
  norm_cast
  apply Nat.mul_pos
  · exact Ideal.absNorm_pos_of_ne_bot (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero)
  · exact Ideal.absNorm_pos_of_ne_bot (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

end SevenEighths.CenteredMomentEnergyReferenceReflection

end

end OAI
