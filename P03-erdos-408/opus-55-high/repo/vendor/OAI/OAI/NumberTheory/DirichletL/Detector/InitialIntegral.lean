module

public import OAI.NumberTheory.DirichletL.Detector.InitialMajorant
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def initialHighOnLines (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) (p : HeightSpace) : ℂ :=
  fullHighCoefficient S D η mask ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) i

lemma initialHighOnLines_continuous (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) :
    Continuous (initialHighOnLines S D η mask σ υ ξ i) := by
  unfold initialHighOnLines
  have hc : Continuous (fun p : HeightSpace =>
      (((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),(ξ:ℂ)+p.1.2*Complex.I)) := by fun_prop
  have hh := (fullHighCoefficient_continuous S D η mask i).comp hc
  simpa

lemma initialHighOnLines_norm_le (S : Finset (Ideal ActualEisensteinCubic.O)) (D : Ideal ActualEisensteinCubic.O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (σ υ ξ : ℝ)
    (i : FullHighIndex) (p : HeightSpace) :
    ‖initialHighOnLines S D η mask σ υ ξ i p‖≤ initialHighMajorant σ υ ξ i :=
  fullHighCoefficient_norm_le S D η mask hm _ _ _ σ υ ξ (by simp) (by simp) (by simp) i

end SevenEighths.ProbePhysical
end

end OAI
