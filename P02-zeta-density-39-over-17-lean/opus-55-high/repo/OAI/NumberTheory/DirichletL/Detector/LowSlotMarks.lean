module
public import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial
public import OAI.NumberTheory.DirichletL.Detector.CanonicalSlots

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

section
variable {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) (b : LowSelectedTuple slots J)
include K slots J b
lemma lowSelectedIdeal_eq_product :
    lowSelectedIdeal slots J b=∏i : SelectedSlot J,Ideal.span {(b i).val} := by
  change CanonicalRowCompletion.principalIdealHom (∏i : SelectedSlot J,(b i).val)=_
  aesop

lemma lowSelectedIdeal_dvd_iff
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) : lowSelectedIdeal slots J b∣A ↔ ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A := by
  rw [lowSelectedIdeal_eq_product]
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun i : SelectedSlot J=>Ideal.span {(b i).val}) (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hcop

lemma lowSelectedIdeal_mark
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) :
    (if lowSelectedIdeal slots J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_dvd_iff slots J b hcop]
  by_cases h : ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (fun hall=>hi (hall i))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm
end

def lowCanonicalSelectedPrime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) : PrimeIdeal :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).val

section
variable {K : ℕ} (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
include K T hT
lemma lowCanonicalSelectedPrime_mem (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    lowCanonicalSelectedPrime T hT J b i∈T i.val :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).property

lemma lowCanonicalSelectedPrime_span (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    Ideal.span {(b i).val}=(lowCanonicalSelectedPrime T hT J b i).val := by
  have hh := canonicalSlotEquiv_span (T i.val) (hT i.val)
    ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i))
  simpa only [Equiv.apply_symm_apply,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalSelectedPrime_injective (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Function.Injective (lowCanonicalSelectedPrime T hT J b) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hne) (lowCanonicalSelectedPrime_mem T hT J b i)
    (hij.symm ▸ lowCanonicalSelectedPrime_mem T hT J b j)

lemma lowCanonicalSelected_coprime (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})) := by
  intro i j hij
  rw [lowCanonicalSelectedPrime_span T hT J b i,lowCanonicalSelectedPrime_span T hT J b j]
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))
end

end SevenEighths.ProbePhysical
end

end OAI
