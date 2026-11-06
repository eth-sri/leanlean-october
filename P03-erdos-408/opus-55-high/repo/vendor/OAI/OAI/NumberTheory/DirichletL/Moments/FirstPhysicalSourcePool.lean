module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CenteredMomentSourceRow CenteredMomentFirstSectors
local notation "O"=>ActualEisensteinCubic.O

theorem original_pool_restriction (C D:Ideal ActualEisensteinCubic.O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal ActualEisensteinCubic.O))(f:Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ):
    (∑a∈residualPool C hC (supportedColumns S),∑b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then f a b else 0)=
    ∑a:columns C C hC S,∑b:columns C D hD S,
      if IsCoprime (a:Ideal ActualEisensteinCubic.O) (b:Ideal ActualEisensteinCubic.O) then f a b else 0:=by
  rw [Finset.sum_coe_sort (columns C C hC S)
    (fun a:Ideal ActualEisensteinCubic.O=>∑b:columns C D hD S,if IsCoprime a (b:Ideal ActualEisensteinCubic.O) then f a b else 0)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hca:IsCoprime C a
  · simp only [hca,true_and,ite_true]
    rw [Finset.sum_coe_sort _ (fun b:Ideal ActualEisensteinCubic.O=>if IsCoprime a b then f a b else 0),Finset.sum_filter]
    grind
  simp_all

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
