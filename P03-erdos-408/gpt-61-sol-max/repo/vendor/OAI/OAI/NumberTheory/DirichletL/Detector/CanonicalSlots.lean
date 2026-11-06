module

public import OAI.NumberTheory.DirichletL.Detector.TuplePrime

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve

local notation "Id" => Ideal ActualEisensteinCubic.O

def canonicalSlotSupport (T : Finset PrimeIdeal)  :=
  T.image (fun P=>primaryGenerator P.val)

lemma primaryPrime_injective {P Q : PrimeIdeal} (hP : Supported P.val) (hQ : Supported Q.val)
    (h : primaryGenerator P.val=primaryGenerator Q.val) : P=Q := by
  apply Subtype.ext
  have hh := congrArg (fun a : ActualEisensteinCubic.O=>Ideal.span {a}) h
  simpa only [span_primaryGenerator_of_supported _ hP,span_primaryGenerator_of_supported _ hQ] using hh

section
variable (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
include T hT

lemma canonicalSlotSupport_nonzero    
     a  (ha : a∈canonicalSlotSupport T) : a≠0 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact supported_primaryGenerator_ne_zero P.val (hT P hP)

def canonicalSlotEquiv (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val) :
    ↥T ≃ ↥(canonicalSlotSupport T) :=
  Equiv.ofBijective
    (fun P=>⟨primaryGenerator P.val.val,Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩⟩)
    ⟨by
      intro P Q h
      apply Subtype.ext
      exact primaryPrime_injective (hT P.val P.property) (hT Q.val Q.property) (congrArg Subtype.val h),by
      intro a
      obtain ⟨P,hP,he⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨P,hP⟩,Subtype.ext he⟩⟩

section
variable (P : T)
include P

@[simp] lemma canonicalSlotEquiv_val    
      : (canonicalSlotEquiv T hT P).val=primaryGenerator P.val.val := rfl

lemma canonicalSlotEquiv_span    
      : Ideal.span {(canonicalSlotEquiv T hT P).val}=P.val.val :=
  span_primaryGenerator_of_supported _ (hT P.val P.property)

lemma canonicalSlotEquiv_norm    
      : elementNorm (canonicalSlotEquiv T hT P).val=(Ideal.absNorm P.val.val:ℝ) :=
  primaryTuple_norm P.val (hT P.val P.property)

end

end

def canonicalTupleEquiv {K } (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)  :=
  Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))

section
variable {K : ℕ} (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
include K T hT



theorem sum_canonical_element_tuples    
     
    (F : (Fin K→ActualEisensteinCubic.O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),F (fun i=>primaryGenerator (P i).val.val) := ((canonicalTupleEquiv T hT).sum_comp (fun p=>F (fun i=>(p i).val))).symm

theorem sum_canonical_weighted_tuples    
      (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (F : (Fin K→ActualEisensteinCubic.O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),
      (∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*
        F (fun i=>primaryGenerator (P i).val.val) := by
  rw [sum_canonical_element_tuples T hT (fun p=>(∏i,W i (elementNorm (p i)/Y i))*F p)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [primaryTuple_norm (P _).val (hT _ _ (P _).property)]

end

end SevenEighths.ProbePhysical
end

end OAI
