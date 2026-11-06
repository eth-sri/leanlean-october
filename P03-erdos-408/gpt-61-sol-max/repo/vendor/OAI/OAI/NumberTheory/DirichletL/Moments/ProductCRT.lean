module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.HeterogeneousCRT

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentProductCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentHeterogeneousCRT
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

def productCRT (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))  :=
  (Ideal.quotEquivOfEq (Ideal.prod_span_singleton Finset.univ a).symm).trans
    (IdealGaussCRT.quotientProdEquivPi (fun i => Ideal.span {a i}) hcop)

omit [DecidableEq ι] in
@[simp] theorem productCRT_mk (a : ι → A)
     hcop 
    (x : A)  i  :
    productCRT a hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [productCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    IdealGaussCRT.quotientProdEquivPi_mk]

def jointCRT (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))  :=
  (Ideal.quotEquivOfEq (congrArg (fun x : A => Ideal.span {x})
    (Finset.prod_mul_distrib (s := Finset.univ) (f := a) (g := b)).symm)).trans
      (productCRT (fun i => a i * b i) hcop)

omit [DecidableEq ι] in
@[simp] theorem jointCRT_mk (a b : ι → A)
     hcop 
    (x : A)  i  :
    jointCRT a b hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [jointCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, productCRT_mk]

def cofactor (a : ι → A) (i : ι)  := ∏ j ∈ Finset.univ.erase i, a j

section
variable (a b : ι → A) (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i}))) (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) (x : Residue (∏ i, a i)) (y : Residue (∏ i, b i)) (i : ι)

theorem factor_mul_cofactor     : a i * cofactor a i = ∏ j, a j :=
  Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)

theorem left_crt_component  
     
     
        :
    jointCRT a b hab
      (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl x) i =
      scaledResidue (a i) (b i) (a i * b i) rfl
        (Ideal.Quotient.mk _ (cofactor b i) * productCRT a ha x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor b i]
  ring

theorem right_crt_component  
     
     
        :
    jointCRT a b hab
      (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _) y) i =
      scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
        (Ideal.Quotient.mk _ (cofactor a i) * productCRT b hb y i) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor a i]
  ring

include hab in
theorem fullModulusCorrelation_product  
     
     
     
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
     χ   ψ   h  :
    fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h =
      ∏ i, fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h) := by
  have hcrt := fullCorrelation_three_equiv (productCRT a ha).toEquiv (productCRT b hb).toEquiv
    (jointCRT a b hab)
    (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl)
    (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _))
    (fun i x => scaledResidue (a i) (b i) (a i * b i) rfl
      (Ideal.Quotient.mk _ (cofactor b i) * x))
    (fun i y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
      (Ideal.Quotient.mk _ (cofactor a i) * y))
    (left_crt_component a b ha hab) (right_crt_component a b hb hab)
    (fun i => χ i) (fun i => ψ i) (Ideal.Quotient.mk _ h)
  assumption

include hab in
theorem cross_cofactor_coprime  
     
      : IsCoprime (a i) (cofactor b i) := by
  unfold cofactor
  apply IsCoprime.prod_right
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hij := (Ideal.isCoprime_span_singleton_iff _ _).mp (hab hji.symm)
  exact (IsCoprime.mul_right_iff.mp (IsCoprime.mul_left_iff.mp hij).1).2

include hab in
theorem local_cofactor_norm  
     
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ)
     h   i  :
    ‖fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h)‖ =
      ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  obtain ⟨u, hu⟩ := isUnit_residue_of_coprime (a i) (cofactor b i)
    (cross_cofactor_coprime a b hab i)
  have hba : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i * a i})) := by
    simpa only [mul_comm] using hab
  obtain ⟨v, hv⟩ := isUnit_residue_of_coprime (b i) (cofactor a i)
    (cross_cofactor_coprime b a hba i)
  rw [← hu, ← hv, fullCorrelation_unit_change, norm_mul, norm_mul, norm_star,
    FiniteRayExpansion.norm_char_unit, FiniteRayExpansion.norm_char_unit, one_mul, one_mul]
  rfl

include hab in
theorem fullModulusCorrelation_product_norm  
     
     
     
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    ‖fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h‖ =
      ∏ i, ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  rw [fullModulusCorrelation_product a b ha hb hab χ ψ h, norm_prod]
  apply Finset.prod_congr rfl
  simp_all [local_cofactor_norm]

end


open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation


omit [DecidableEq ι] in
theorem supported_character_product (a : ι → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
     hprod 
     hcop  :
    supportedModulusCharacter (∏ i, a i) hprod =
      crtCharacter (productCRT a hcop) (fun i => supportedModulusCharacter (a i) (ha i)) := by
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [crtCharacter_apply, productCRT_mk, supportedModulusCharacter_mk]
  rw [← Ideal.prod_span_singleton Finset.univ a, map_prod]

theorem actualCorrelation_product_norm (a b : ι → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hb : ∀ i, Supported (Ideal.span {b i}))
    (hA : Supported (Ideal.span {∏ i, a i}))
    (hB : Supported (Ideal.span {∏ i, b i}))
    (hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) (h : ActualEisensteinCubic.O) :
    ‖actualCorrelation (∏ i, a i) (∏ i, b i) hA hB h‖ =
      ∏ i, ‖actualCorrelation (a i) (b i) (ha i) (hb i) h‖ := by
  let : ∀ i, Finite (Residue (a i)) := fun i => finite_quotient_span (supported_element_ne_zero (a i) (ha i))
  let : ∀ i, Finite (Residue (b i)) := fun i => finite_quotient_span (supported_element_ne_zero (b i) (hb i))
  let : ∀ i, Fintype (Residue (a i)) := fun i => Fintype.ofFinite _
  let : ∀ i, Fintype (Residue (b i)) := fun i => Fintype.ofFinite _
  let := finite_quotient_span (supported_element_ne_zero _ hA)
  let := finite_quotient_span (supported_element_ne_zero _ hB)
  let : Fintype (Residue (∏ i, a i)) := Fintype.ofFinite _
  let : Fintype (Residue (∏ i, b i)) := Fintype.ofFinite _
  change ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ hA)
    (supportedModulusCharacter _ hB) h‖ =
    ∏ i, ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ (ha i))
      (supportedModulusCharacter _ (hb i)) h‖
  simp_all [supported_character_product, fullModulusCorrelation_product_norm]



end SevenEighths.CenteredMomentProductCRT

end

end OAI
