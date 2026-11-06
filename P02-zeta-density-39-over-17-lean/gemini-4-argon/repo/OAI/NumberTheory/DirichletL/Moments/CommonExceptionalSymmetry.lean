module
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSymmetry
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair CenteredMomentSecondHeightFamily
universe u

lemma same_raw_better_cap (r c d:ℝ):
    max (max (r-c) 0) (max (r-d) 0)=max (r-min c d) 0:=by
  rcases le_total c d with h|h
  · rw [min_eq_left h,max_eq_left (max_le_max_right 0 (by linarith))]
  · rw [min_eq_right h,max_eq_right (max_le_max_right 0 (by linarith))]
