module

public import OAI.NumberTheory.DirichletL.Moments.ReflectionTails

@[expose] public section

namespace OAI


open scoped ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson

lemma normalized_power_eq  Y  (hY : 0<Y) (B : ℕ) :
    Y^B/Real.sqrt Y=Y^((B:ℝ)-1/2) := by
  rw [Real.rpow_sub hY,Real.rpow_natCast,Real.sqrt_eq_rpow]

end SevenEighths.CenteredMomentComparisonReflection



end OAI
