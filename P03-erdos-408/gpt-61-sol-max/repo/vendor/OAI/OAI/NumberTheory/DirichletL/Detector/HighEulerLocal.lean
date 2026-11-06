module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighEuler

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ProbeEuler ProbePrimePower ProbeRow

local notation "Id" => Ideal ActualEisensteinCubic.O

section
variable (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal)

include hx hw hz in
lemma highPrimeTerm_summable_norm    
            :
    Summable (fun b : HighValuation=>‖highPrimeTerm η x w z P b‖) := by
  have hs := (highValuationTerm_summable_norm η x w z hx hw hz).comp_injective
    (Finsupp.single_injective P)
  simpa only [Function.comp_def,highValuationTerm_eq_prod,
    Finsupp.prod_single_index (highPrimeTerm_zero η x w z P)] using hs

lemma highPrimeTerm_zero_of_two_le    
       e l k m  (he : 2≤e) :
    highPrimeTerm η x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η 1 x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

include hx hw hz in
theorem highPrimeTerm_tsum_eq_localFactor    
            :
    (∑' b : HighValuation,highPrimeTerm η x w z P b)=
      idealHighLocalFactor η P.val x w z := by
  have hs := (highPrimeTerm_summable_norm η x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, highPrimeTerm η x w z P ((e,l),b))=
        ∑' k,∑' m,highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp_all [highPrimeTerm_zero_of_two_le]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

end

end SevenEighths.ProbePhysical


end OAI
