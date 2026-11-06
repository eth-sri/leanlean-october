module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LowTruePeriodPuncture

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowPrimeIdealList (T : Finset PrimeIdeal)  := T.image Subtype.val

def lowPrimeListEquiv (T : Finset PrimeIdeal) : T≃lowPrimeIdealList T :=
  Equiv.ofBijective (fun p=>⟨p.val.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩) (by
    constructor
    · intro p q h
      grind
    · intro I
      obtain ⟨P,hP,h⟩ := Finset.mem_image.mp I.property
      exact ⟨⟨P,hP⟩,Subtype.ext h⟩)

section
variable (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val) (η : HeckeFamily.Character) (W : ℝ→ℂ) (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) (hI : I∈lowPrimeIdealList T)



include hI in
lemma lowPrimeIdealList_prime       : Prime I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact P.property

include hT hI in
lemma lowPrimeIdealList_supported    
        : Supported I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

include hI in
lemma lowPrimeIdealList_maximal       : I.IsMaximal :=
  (Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI)).isMaximal (lowPrimeIdealList_prime T I hI).ne_zero

include hT hI in
lemma lowPrimeIdealList_good_odd    
        :
    ConcretePrimeRowBridge.goodLambda∉I ∧ ringChar (O⧸I)≠2 := by
  have hs := lowPrimeIdealList_supported T hT I hI
  exact hs.2 I ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI),le_rfl⟩)

lemma lowPrimeIdealList_disjoint {ι : Type*} (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPrimeIdealList (T i)) (lowPrimeIdealList (T j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro I hI hJ
  obtain ⟨P,hP,hPI⟩ := Finset.mem_image.mp hI
  obtain ⟨Q,hQ,hQI⟩ := Finset.mem_image.mp hJ
  have he : P=Q := Subtype.ext (hPI.trans hQI.symm)
  exact Finset.disjoint_left.mp (hT hij) hP (he.symm ▸ hQ)

lemma lowPrimeIdealList_norm   (H : ℝ)
    (hT : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) (I : Id) (hI : I∈lowPrimeIdealList T) :
    (Ideal.absNorm I:ℝ)≤H := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

theorem low_actual_ideal_polynomial {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*F (fun i=>Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val) := by
  let E := Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))
  rw [←Equiv.sum_comp E]
  simp only [E,Equiv.piCongrRight_apply,Pi.map_apply,canonicalSlotEquiv_val]
  have hspan (p : ∀i,T i) (i : ι) : Ideal.span {primaryGenerator (p i).val.val}=(p i).val.val :=
    span_primaryGenerator_of_supported _ (hT i _ (p i).property)
  simp_rw [hspan]
  rw [low_canonical_polynomial_period_filter η S hS hbad T hT hout W Y t (fun p=>F (fun i=>(p i).val))]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun i=>lowPrimeListEquiv (lowPeriodPrimeList η S hS (T i))))
    (fun p=>(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val))

include hW in
lemma low_actual_ideal_weight_bound    
          :
    ‖lowSingleSlotWeight η W Y t (primaryGenerator I)‖≤1 :=
  (lowSingleSlotWeight_norm η W Y t _).trans (hW _)

end

end SevenEighths.ProbePhysical
end

end OAI
