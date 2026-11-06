module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighValuations
public import OAI.NumberTheory.DirichletL.Detector.EulerFinsupp
public import OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion

local notation "Id" => Ideal ActualEisensteinCubic.O

lemma bareIdealHighSummand_support (η : HeckeFamily.Character) (u : ActualEisensteinCubic.O) (x w z : ℂ)
     I J K L  (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  grind [highSupport, bareIdealHighSummand, bareIdealHighCoefficient]

end SevenEighths.ProbePhysical


end OAI
