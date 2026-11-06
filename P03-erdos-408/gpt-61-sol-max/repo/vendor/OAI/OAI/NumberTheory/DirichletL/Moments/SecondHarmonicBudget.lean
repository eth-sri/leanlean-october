module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondSquarefreeBlock
public import OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

@[expose] public section

namespace OAI


open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentSecondHarmonicBudget
open CenteredMomentSecondWindowBudget CenteredMomentMobiusHarmonicMass
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid


lemma paired_divisor  J₁ J₂   t E₁ E₂ n  (hn:0≤n) :
    windowBudget J₁ t (E₁/n)*windowBudget J₂ t (E₂/n)=
      (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/n := by
  simp only [windowBudget,Real.sqrt_div' _ hn]
  grind

end SevenEighths.CenteredMomentSecondHarmonicBudget



end OAI
