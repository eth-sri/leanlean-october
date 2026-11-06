module

public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceTuples

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge InverseInitialOverlap

variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedIdeal (L)(J:Finset ι)(x:Assigned L J)  :=
  ∏i:↥J,(x i).val

def remainingIdeal (L)(J:Finset ι)(y:Remaining L J)  :=
  ∏i:{i:ι // i∉J},(y i).val

omit [Fintype ι] in
@[simp] theorem joinTuple_assigned (L:ι→Finset (Ideal HeckeFamily.O)) J 
    (x:Assigned L J) y  i  : joinTuple L J x y i.val=x i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
@[simp] theorem joinTuple_remaining (L:ι→Finset (Ideal HeckeFamily.O)) J 
    (x:Assigned L J) y  i  : joinTuple L J x y i.val=y i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
theorem joinTuple_assigned_product (L:ι→Finset (Ideal HeckeFamily.O)) J 
    (x:Assigned L J) y  :
    (∏i∈J,(joinTuple L J x y i).val)=assignedIdeal L J x := by
  rw [←Finset.prod_coe_sort J (fun i=>(joinTuple L J x y i).val)]
  simp only [joinTuple_assigned,assignedIdeal]

section
variable (L : ι→Finset (Ideal HeckeFamily.O)) (J : Finset ι) (x : Assigned L J) (y : Remaining L J)

theorem joinTuple_product   
       :
    (∏i,(joinTuple L J x y i).val)=assignedIdeal L J x*remainingIdeal L J y := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>(joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

theorem joinTuple_coefficient_product   
      (coeff:ι→Ideal HeckeFamily.O→ℂ) :
    (∏i,coeff i (joinTuple L J x y i).val)=
      (∏i:↥J,coeff i.val (x i).val)*(∏i:{i:ι // i∉J},coeff i.val (y i).val) := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>coeff i (joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  congr 2
  ext i
  simp

end

omit [Fintype ι] [DecidableEq ι] in
theorem assignedIdeal_ne_zero (L:ι→Finset (Ideal HeckeFamily.O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J) : assignedIdeal L J x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi=>(hprime i.val _ (x i).property).ne_zero)

theorem original_selected_grouped_products (S:Finset (Ideal HeckeFamily.O))
    (L:ι→Finset (Ideal HeckeFamily.O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal HeckeFamily.O→ℂ)
     η  a  W  Z r z (hZ:0<Z) u  :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*
      ∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
        originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
          (assignedIdeal L J x) η a W Z r z u := by
  rw [original_selected_grouped S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [joinTuple_coefficient_product,joinTuple_product,joinTuple_assigned_product]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
