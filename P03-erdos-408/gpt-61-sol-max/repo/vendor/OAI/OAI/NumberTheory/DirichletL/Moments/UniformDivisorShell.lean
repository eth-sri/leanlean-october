module

public import OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell

@[expose] public section

namespace OAI


open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios


theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
     Z  (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

theorem numerical_allowance  Z H  (hZ:1<Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

end SevenEighths.CenteredMomentUniformDivisorShell



end OAI
