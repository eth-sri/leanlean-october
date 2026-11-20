module

public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalMass
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSymmetry
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonLinearNormalization
open CenteredMomentCommonPairedSource CenteredMomentCommonExceptionalCost
open CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondHeightFamily
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma same_raw_better_cap (r c d:ℝ):
    max (max (r-c) 0) (max (r-d) 0)=max (r-min c d) 0:=by
  rcases le_total c d with h|h
  · rw [min_eq_left h,max_eq_left (max_le_max_right 0 (by linarith))]
  · rw [min_eq_right h,max_eq_right (max_le_max_right 0 (by linarith))]

end SevenEighths.CenteredMomentCommonExceptionalSymmetry

end

end OAI
