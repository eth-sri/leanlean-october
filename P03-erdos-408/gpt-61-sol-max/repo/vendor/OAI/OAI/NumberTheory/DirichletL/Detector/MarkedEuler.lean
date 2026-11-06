module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.MarkedValuations

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEulerFinsupp

local notation "Id" => Ideal ActualEisensteinCubic.O

def excludedHighArray (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ) (a : HighIdeal)  :=
  markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2

section
variable (S : Finset Id) (hS : ∀P∈S,Prime P)
include S hS

section
variable (η : HeckeFamily.Character) (x w z : ℂ)
include η x w z

lemma excludedHighArray_one    
        : excludedHighArray S η x w z 1=1 := by
  simp only [excludedHighArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]

lemma excludedHighArray_mul    
         a b 
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedHighArray S η x w z (a*b)=excludedHighArray S η x w z a*excludedHighArray S η x w z b := by
  simp only [excludedHighArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedHighPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation)  :=
  excludedHighArray S η x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedHighArray_prod    
         v  :
    excludedHighArray S η x w z (highIdeals v)=v.prod (excludedHighPrimeTerm S η x w z) :=
  highArray_val_prod _ (excludedHighArray_one S hS η x w z) (excludedHighArray_mul S hS η x w z) v

end

section
variable (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (x w z : ℂ)
include T η x w z

lemma markedHighArray_val      
         v  :
    markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  solve_by_elim [highIdeals, excludedHighArray_prod]

theorem markedIdealHighSeries_hasProd    
         
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z) := by
  have h0 (P : PrimeIdeal) : excludedHighPrimeTerm S η x w z P 0=1 := by
    solve_by_elim [excludedHighArray_one]
  have hs := (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedHighArray S η x w z (highIdeals v)‖) at hs
  simp only [excludedHighArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedHighPrimeTerm S η x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z := by
    simp only [←markedHighArray_val S hS T η x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end

end

end SevenEighths.ProbePhysical
end

end OAI
