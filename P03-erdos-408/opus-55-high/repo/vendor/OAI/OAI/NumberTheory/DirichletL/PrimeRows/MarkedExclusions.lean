module

public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedProduct
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstBoundary

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical

theorem correctionTail_mono {S T : Finset (Ideal HeckeFamily.O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,by grind⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact by grind
  constructor
  · intro P hP
    exact hS.norm_four P (by grind)
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>globalPrimeDefectBound_nonneg P.val)
      (by grind) (globalPrimeDefectBound_summable.subtype _) hS.summable

theorem firstTail_mono {eps : ℝ} {S T : Finset (Ideal HeckeFamily.O)} (hS : FirstTail eps S) (hst : S⊆T) :
    FirstTail eps T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,by grind⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact by grind
  refine ⟨hS.positive,?_,?_⟩
  · intro P hP
    exact hS.norm_four P (by grind)
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>firstPrimeDefectBound_nonneg eps P.val)
      (by grind) ((firstPrimeDefectBound_summable eps hS.positive).subtype _) hS.summable

theorem markedSourceExclusions (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S) (T : Finset PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }

theorem marked_firstTail (eps : ℝ) (S : Finset (Ideal HeckeFamily.O)) (hS : FirstTail eps S) (T : Finset PrimeIdeal) :
    FirstTail eps (markExclusions S T) := firstTail_mono hS Finset.subset_union_left

end SevenEighths.ProbeHighRowFamily

end

end OAI
