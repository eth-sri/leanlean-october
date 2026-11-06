module

public import OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment
public import OAI.NumberTheory.DirichletL.Descent.Marks

@[expose] public section

namespace OAI



open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialEnergyCallerSelector


theorem mask_nonzero_coprime (F : Finset (Ideal ActualEisensteinCubic.O)) (j : Ideal ActualEisensteinCubic.O) (hj : Admissible j)
    (A : Finset (primePool F))
    (hm : rowCoprimeMask (fun i : primePool F=>i.val) A (primaryGenerator j)≠0) :
    IsCoprime (∏ i∈A,i.val) j := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : i.val.IsMaximal) htop
    (show (i.val : Ideal ActualEisensteinCubic.O) ≤ (i.val : Ideal ActualEisensteinCubic.O) ⊔ j from le_sup_left)
  have hmem : primaryGenerator j∈i.val := by
    rw [he]
    apply (show j ≤ (i.val : Ideal ActualEisensteinCubic.O) ⊔ j from le_sup_right)
    have hjmem : primaryGenerator j ∈ Ideal.span {primaryGenerator j} :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hspan] at hjmem
    exact hjmem
  apply hm
  unfold rowCoprimeMask
  exact ite_eq_left ⟨i,hi,hmem⟩

end SevenEighths.InverseInitialEnergyCallerSelector



end OAI
