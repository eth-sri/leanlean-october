module
public import OAI.NumberTheory.DirichletL.Detector.GramIdealDilation
public import OAI.NumberTheory.DirichletL.Detector.GramLatticeSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : O) (hC : λ₀^2∣C-1) (hd : λ₀^2∣d-1) : λ₀^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI
