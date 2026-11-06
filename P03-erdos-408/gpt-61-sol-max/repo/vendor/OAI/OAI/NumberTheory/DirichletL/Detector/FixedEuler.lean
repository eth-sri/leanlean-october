module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighExcludedLocal
public import OAI.NumberTheory.DirichletL.Hecke.RayFamily
public import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily

local notation "Id" => Ideal ActualEisensteinCubic.O

lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)

def fixedSourcePrincipal (S : Finset Id) (hS : ∀P∈S,Prime P)  :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  HeckeRayFamily.character (∏P∈S,P) 1

section
variable (η χ : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) (a : Id→ℂ) (ha : ∀P : PrimeIdeal,idealCoeff χ P.val=if P.val∈S then 0 else a P.val) (s : ℂ) (hs : 1<s.re)

include hS in
lemma prime_coprime_fixedProduct       :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_isUnit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=>h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime       :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime         :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

include ha hs in
theorem LFunction_hasProd_outside      
     
        :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs
  rw [←LFunction_eq_series χ hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (idealCoeff χ) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹ := by
    change (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹=_
    grind
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹)).mpr
  convert h using 1
  grind [Set.mulIndicator]

include hs in
theorem fixedSourcePrincipal_hasProd    
        :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction (fixedSourcePrincipal S hS) s) := by
  simpa only [one_mul] using
    LFunction_hasProd_outside (fixedSourcePrincipal S hS) S (fun _=>1) (fixedSourcePrincipal_prime S hS) s hs

include hs in
theorem excludedTarget_hasProd      
        :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (idealCoeff η) (excludedTarget_prime η S hS) s hs

end

end SevenEighths.ProbePhysical
end

end OAI
