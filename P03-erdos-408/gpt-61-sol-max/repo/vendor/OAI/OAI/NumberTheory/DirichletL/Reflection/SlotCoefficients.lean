module

public import OAI.NumberTheory.DirichletL.Reflection.SupportedChoices
public import OAI.NumberTheory.DirichletL.Reflection.TupleFamily

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma PrimeFamily.eq_of_ideal_eq {ι : Type*} (P Q : PrimeFamily ι) (h : P.ideal=Q.ideal) : P=Q := by
  cases P
  cases Q
  cases h
  rfl

def slotChoiceFamily (L : σ→Finset (Ideal ActualEisensteinCubic.O))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (p : ∀ i,L i) : PrimeFamily σ where
  ideal i := (p i).val
  maximal i := hmax i _ (p i).property
  good i := hgood i _ (p i).property


lemma slot_coefficient_split (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (T : Finset σ)
    (w : ∀ i,L i→ℂ)  a   b  :
    (∏ i,w i ((slotChoiceSplit L T).symm (a,b) i))=
      (∏ i : T,w i.val (a i))*(∏ i : {i // i∉T},w i.val (b i)) := by
  have he := Fintype.prod_subtype_mul_prod_subtype (fun i : σ => i∈T)
    (fun i => w i ((slotChoiceSplit L T).symm (a,b) i))
  simp only [slotChoiceSplit_active,slotChoiceSplit_inactive] at he
  refine he.symm.trans ?_
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_univ])
  intro i hi
  rfl

omit [DecidableEq σ] in
lemma slot_coefficient_norm (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : ∀ i,L i) : ‖∏ i,w i (p i)‖≤1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hw i (p i))
end
end SevenEighths.InverseReflectedPhase

end OAI
