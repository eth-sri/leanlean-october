module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalBudget
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondExceptionalBudget
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical

universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma forcingNorm_ge_one  C D (hC:Supported C) U  :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

lemma column_cap_ledger (c d r:ℝ)(hc:0≤c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  
  have hc':min c d≤c:=min_le_left _ _
  have hd':min c d≤d:=min_le_right _ _
  by_cases hr:0≤r
  · rw [max_eq_left hr]
    by_cases hm:r≤min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤max (r-min c d) 0:=le_max_right _ _
    linarith

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving



end OAI
