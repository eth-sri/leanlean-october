module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.TupleFamily

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def slotChoiceSplit (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (T : Finset σ)  :=
  Equiv.piEquivPiSubtypeProd (fun i => i∈T) (fun i => L i)

omit [Fintype σ] in
lemma slotChoiceSplit_active (L : σ→Finset (Ideal ActualEisensteinCubic.O))  T 
     a   b   i  :
    (slotChoiceSplit L T).symm (a,b) i.val=a i := by
  simp_all [slotChoiceSplit]

omit [Fintype σ] in
lemma slotChoiceSplit_inactive (L : σ→Finset (Ideal ActualEisensteinCubic.O))  T 
     a   b   i  :
    (slotChoiceSplit L T).symm (a,b) i.val=b i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dite_eq_right i.property]

lemma slot_choice_inactive_weight  L   T 
     p  :
    (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)=
      ∏ i : {i // i∉T}, (Ideal.absNorm ((slotChoiceSplit L T p).2 i).val:ℂ)⁻¹ := by
  exact Finset.prod_subtype (Finset.univ\T) (fun i => by simp)
    (fun i => (Ideal.absNorm (p i).val:ℂ)⁻¹)

lemma slot_choice_coprime_split (L : σ→Finset (Ideal ActualEisensteinCubic.O))  T 
     a   b   K  :
    IsCoprime K (∏ i, ((slotChoiceSplit L T).symm (a,b) i).val) ↔
      IsCoprime K (∏ i : T, (a i).val) ∧ IsCoprime K (∏ i : {i // i∉T}, (b i).val) := by
  simp only [IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [slotChoiceSplit_active] using h i.val
    · intro i
      simpa only [slotChoiceSplit_inactive] using h i.val
  · rintro ⟨ha,hb⟩ i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb ⟨i,hi⟩
end
end SevenEighths.InverseReflectedPhase

end OAI
