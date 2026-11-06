module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource

@[expose] public section

namespace OAI


open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSymmetry
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonExceptionalSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily

universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma same_raw_better_cap (r c d:ℝ):
    max (max (r-c) 0) (max (r-d) 0)=max (r-min c d) 0:=by
  grind

end SevenEighths.CenteredMomentCommonExceptionalSymmetry



end OAI
