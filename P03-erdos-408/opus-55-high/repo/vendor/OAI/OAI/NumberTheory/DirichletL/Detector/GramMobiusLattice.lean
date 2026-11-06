module

public import OAI.NumberTheory.DirichletL.Detector.GramIdealDilation
public import OAI.NumberTheory.DirichletL.Detector.GramLatticeSource

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : ActualEisensteinCubic.O) (hC : ConcretePrimeRowBridge.goodLambda^2∣C-1) (hd : ConcretePrimeRowBridge.goodLambda^2∣d-1) : ConcretePrimeRowBridge.goodLambda^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI
