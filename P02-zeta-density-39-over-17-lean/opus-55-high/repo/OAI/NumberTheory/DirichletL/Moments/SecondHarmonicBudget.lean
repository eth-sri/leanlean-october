module
public import OAI.NumberTheory.DirichletL.Moments.SecondSquarefreeBlock
public import OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentSecondHarmonicBudget
open CenteredMomentSecondWindowBudget CenteredMomentMobiusHarmonicMass
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma paired_divisor (J₁ J₂:ℕ) (t E₁ E₂ n:ℝ) (hn:0≤n) :
    windowBudget J₁ t (E₁/n)*windowBudget J₂ t (E₂/n)=
      (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/n := by
  simp only [windowBudget,Real.sqrt_div' _ hn]
  grind

end SevenEighths.CenteredMomentSecondHarmonicBudget

end

end OAI
