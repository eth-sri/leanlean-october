module
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalBudget
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondExceptionalBudget
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  pm_2881
  unfold forcingNorm at hf ⊢
  aesop

lemma column_cap_ledger (c d r:ℝ)(hc:0≤ c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by grind

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving

end

end OAI
