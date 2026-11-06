module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy
open CenteredMomentFirstSectorTransform CenteredMomentFirstChildProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O

theorem original_pool_restriction (C D:Ideal O)(hC:C≠0)(hD:D ≠0)
    (S:Finset (Ideal O))(f:Ideal O→ Ideal O→ℂ):
    (∑a∈residualPool C hC (supportedColumns S),∑b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then f a b else 0)=
    ∑a:columns C C hC S,∑b:columns C D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then f a b else 0:=by
  rw [Finset.sum_coe_sort (columns C C hC S)
    (fun a:Ideal O=>∑b:columns C D hD S,if IsCoprime a (b:Ideal O) then f a b else 0)]
  pm_3809 columns Finset.sum_filter a ha
  by_cases hca:IsCoprime C a
  · simp only [hca,true_and,ite_true]
    rw [Finset.sum_coe_sort _ (fun b:Ideal O=>if IsCoprime a b then f a b else 0),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hcb:IsCoprime C b <;> simp [hcb]
  simp_all

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
