module
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondPhysicalCost
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic CenteredMomentSupport
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma logb_sqrt (Z x:ℝ) (hx:0<x) : Real.logb Z (Real.sqrt x)=Real.logb Z x/2 := by
  rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hx]
  ring

end SevenEighths.CenteredMomentSecondPhysicalCost

end

end OAI
