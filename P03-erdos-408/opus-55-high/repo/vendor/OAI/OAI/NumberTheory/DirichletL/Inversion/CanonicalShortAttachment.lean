module

public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool
public import OAI.NumberTheory.DirichletL.Descent.CompletionSplit
public import OAI.NumberTheory.DirichletL.Descent.ReopenedBins
public import OAI.NumberTheory.DirichletL.Inversion.ShortCanonicalNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseCanonicalShortAttachment
open ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment
universe u v

def idealLists {σ : Type u} (F : Finset (Ideal ActualEisensteinCubic.O))
    (lists : σ→Finset (primePool F)) (j : σ) : Finset (Ideal ActualEisensteinCubic.O) :=
  (lists j).image Subtype.val

def transportCoeff {σ : Type u} (F : Finset (Ideal ActualEisensteinCubic.O))
    (a : σ→primePool F→ℂ) (j : σ) (P : Ideal ActualEisensteinCubic.O) : ℂ :=
  if h:P∈primePool F then a j ⟨P,h⟩ else 0

@[simp] theorem transportCoeff_val {σ : Type u} (F : Finset (Ideal ActualEisensteinCubic.O))
    (a : σ→primePool F→ℂ) (j : σ) (i : primePool F) :
    transportCoeff F a j i.val=a j i := by simp [transportCoeff]

def idealWeights {σ : Type u} (F : Finset (Ideal ActualEisensteinCubic.O))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (j : σ) (P : idealLists F lists j) : ℂ := transportCoeff F a j P.val

lemma tuple_mark_product {σ : Type u} [Fintype σ] [DecidableEq σ]
    (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (w : ∀j,lists j→ℂ) (A : Ideal ActualEisensteinCubic.O) :
    tupleDivisibilityMark lists w A=
      ∏j,∑P:lists j,if P.val∣A then w j P else 0 := by
  unfold tupleDivisibilityMark
  calc
    _ = ∑p:∀j,lists j,∏j,if (p j).val∣A then w j (p j) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←Finset.prod_mul_distrib]
      simp
    _ = _ := (Fintype.prod_sum (fun j (P : lists j)=>if P.val∣A then w j P else 0)).symm

theorem indexed_mark_eq_tuple {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal ActualEisensteinCubic.O)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (a : σ→primePool F→ℂ) (A : Ideal ActualEisensteinCubic.O) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a A=
      tupleDivisibilityMark (fun j:slots=>idealLists F lists j.val)
        (fun j:slots=>idealWeights F lists a j.val) A := by
  rw [tuple_mark_product]
  unfold indexedIdealMark
  rw [←Finset.prod_coe_sort slots]
  apply Finset.prod_congr rfl
  intro j hj
  change _ = ∑P:idealLists F lists j.val,if P.val∣A then transportCoeff F a j.val P.val else 0
  rw [Finset.sum_coe_sort (idealLists F lists j.val) (fun P : Ideal ActualEisensteinCubic.O=>if P∣A then transportCoeff F a j.val P else 0)]
  change (∑i∈lists j.val,if i.val∣A then a j.val i else 0)=
    ∑P∈(lists j.val).image Subtype.val,if P∣A then transportCoeff F a j.val P else 0
  simp

lemma idealLists_disjoint {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal ActualEisensteinCubic.O)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (h : (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k))) :
    Pairwise (fun j k:slots=>Disjoint (idealLists F lists j.val) (idealLists F lists k.val)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hP
  obtain ⟨i',hi',he'⟩:=Finset.mem_image.mp hQ
  have hii : i=i' := by grind
  have hjk' : j.val≠k.val := by grind
  exact Finset.disjoint_left.mp (h j.property k.property hjk') hi (by grind)

lemma idealLists_prime_data {σ : Type u} (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (lists : σ→Finset (primePool F))
    (j : σ) (P : Ideal ActualEisensteinCubic.O) (hP : P∈idealLists F lists j) :
    P.IsMaximal ∧ goodLambda∉P ∧ Prime P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  refine ⟨inferInstance,poolGood F hF i,?_,poolOdd F hF i⟩
  exact Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI
