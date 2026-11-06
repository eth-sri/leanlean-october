module

public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDivisors

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
variable {ι:Type*}[Fintype ι][DecidableEq ι]

abbrev Tuple (L:ι→Finset (Ideal HeckeFamily.O)) := ∀i,↥(L i)
abbrev Assigned (L:ι→Finset (Ideal HeckeFamily.O))(J:Finset ι) := ∀i:↥J,↥(L i.val)
abbrev Remaining (L:ι→Finset (Ideal HeckeFamily.O))(J:Finset ι) := ∀i:{i:ι // i∉J},↥(L i.val)

def joinTuple (L:ι→Finset (Ideal HeckeFamily.O))(J:Finset ι)(x:Assigned L J)(y:Remaining L J) : Tuple L :=
  (Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm (x,y)

theorem sum_tuple_split (L:ι→Finset (Ideal HeckeFamily.O))(J:Finset ι)(f:Tuple L→ℂ) :
    (∑q:Tuple L,f q)=∑x:Assigned L J,∑y:Remaining L J,f (joinTuple L J x y) := by
  rw [←(Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm.sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_tuple_original (L:ι→Finset (Ideal HeckeFamily.O))(f:(ι→Ideal HeckeFamily.O)→ℂ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈Fintype.piFinset L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,Fintype.mem_piFinset.mp hq i⟩)
  · simp
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · grind
  simp

theorem tuple_injective (L:ι→Finset (Ideal HeckeFamily.O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Function.Injective (fun i=>(q i).val) := by
  intro i j he
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i) (Finset.mem_univ j) hij)
    (q i).property (by simp_all)

theorem original_selected_subset_sum (S:Finset (Ideal HeckeFamily.O))
    (L:ι→Finset (Ideal HeckeFamily.O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal HeckeFamily.O→ℂ)
    (η:Ideal HeckeFamily.O→*ℂ)(a:Ideal HeckeFamily.O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:HeckeFamily.O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
  calc
    _ = ∑q:Tuple L,∑J∈Finset.univ.powerset,(∏i,coeff i (q i).val)*
        originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [originalTotal_slot_subsets S _ (by grind)
        (tuple_injective L hdis q) η a W Z r z hZ u,Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem original_selected_grouped (S:Finset (Ideal HeckeFamily.O))
    (L:ι→Finset (Ideal HeckeFamily.O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal HeckeFamily.O→ℂ)
    (η:Ideal HeckeFamily.O→*ℂ)(a:Ideal HeckeFamily.O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:HeckeFamily.O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,∑y:Remaining L J,
      (∏i,coeff i (joinTuple L J x y i).val)*
        originalFixedPolynomial S (∏i,(joinTuple L J x y i).val)
          (∏i∈J,(joinTuple L J x y i).val) η a W Z r z u := by
  rw [original_selected_subset_sum S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  exact sum_tuple_split L J _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
