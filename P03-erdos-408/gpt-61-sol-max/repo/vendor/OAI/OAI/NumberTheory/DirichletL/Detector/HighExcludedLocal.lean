module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighExcludedEuler
public import OAI.NumberTheory.DirichletL.Detector.HighEulerLocal

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic

local notation "Id" => Ideal ActualEisensteinCubic.O

section
variable (S : Finset Id) (hS : ∀P∈S,Prime P) (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal)

lemma highExclusion_prime       :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [ite_eq_right (fun h=>h P.val hP (dvd_refl _)),ite_eq_left hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        aesop
      exact (hS Q hQ).not_isUnit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [ite_eq_left houtside,ite_eq_right hP]

include hS in
lemma highIdealMask_prime_outside    
      (hP : P.val∉S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=1 := by
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,
    ite_eq_right hP,one_pow,one_mul]

include hS in
lemma highIdealMask_prime_inside    
      (hP : P.val∈S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=
      if b=0 then 1 else 0 := by
  rcases b with ⟨⟨e,l⟩,k,m⟩
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,ite_eq_left hP]
  by_cases he : e=0 <;> by_cases hl : l=0 <;> by_cases hk : k=0 <;> by_cases hm : m=0 <;>
    simp [he,hl,hk,hm,Prod.mk_eq_zero]

include hS hx hw hz in
theorem excludedHighLocalFactor    
       
            :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η 1 x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealHighLocalFactor η P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η 1 x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · bound
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

include hS hx hw hz in
theorem excludedIdealHighSeries_hasProd_outside    
       
          :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) := by
  have h := excludedIdealHighSeries_hasProd S hS η x w z hx hw hz
  simp only [excludedHighLocalFactor S hS η x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)).mpr
  convert h using 1
  funext P
  simp_all [Set.mulIndicator]

end

end SevenEighths.ProbePhysical


end OAI
