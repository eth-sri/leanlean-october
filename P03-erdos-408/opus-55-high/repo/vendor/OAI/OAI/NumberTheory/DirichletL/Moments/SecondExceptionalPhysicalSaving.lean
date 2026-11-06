module

public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalBudget
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open CanonicalQuadraticSieve
open CenteredMomentSecondPhysicalLedger
open CenteredMomentCanonicalFirst
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma forcingNorm_ge_one (C D:Ideal HeckeFamily.O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

lemma column_cap_ledger (c d r:ℝ)(hc:0≤c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  grind

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving

end

end OAI
