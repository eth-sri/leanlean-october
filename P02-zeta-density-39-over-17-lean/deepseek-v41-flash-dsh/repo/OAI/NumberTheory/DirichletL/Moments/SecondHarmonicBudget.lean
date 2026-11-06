module
public import OAI.NumberTheory.DirichletL.Moments.SecondSquarefreeBlock
public import OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentSecondHarmonicBudget
open CenteredMomentSecondWindowBudget CenteredMomentMobiusHarmonicMass CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma paired_divisor (J₁ J₂:ℕ) (t E₁ E₂ n:ℝ) (hn:0≤n) :
    windowBudget J₁ t (E₁/n)*windowBudget J₂ t (E₂/n)=
      (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/n := by
  simp only [windowBudget,Real.sqrt_div' _ hn]
  calc
    _=(Real.sqrt E₁*heightEnvelope t^J₁*profileMoment J₁*
        (Real.sqrt E₂*heightEnvelope t^J₂*profileMoment J₂))/
          (Real.sqrt n*Real.sqrt n):=by ring
    _=_:=by rw [Real.mul_self_sqrt hn]

end SevenEighths.CenteredMomentSecondHarmonicBudget

end

end OAI
