module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighEuler

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic

local notation "Id" => Ideal ActualEisensteinCubic.O

section
variable (F : HighIdeal→ℂ) (h1 : F 1=1) (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
include F h1 hmul

lemma highArray_val_prod    
     
     v  :
    F (highIdeals v)=v.prod (fun P b=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) := by
  have hzero (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    assumption
  induction v using Finsupp.induction with
  | zero => simp only [highIdeals_zero,h1,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hc := prime_coprime_highIdeals P v (Finsupp.notMem_support_iff.mp hP)
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (hzero P),←ih,
      highIdeals_add,highIdeals_single]
    exact hmul _ _ hpow

theorem highArray_hasProd    
     
    (hzero : ∀ a : HighIdeal,F a≠0 → a.1.1≠0 ∧ a.1.2≠0 ∧ a.2.1≠0 ∧ a.2.2≠0)
    (hs : Summable (fun a=>‖F a‖)) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) (∑' a,F a) := by
  have hv := hs.comp_injective highIdeals_injective
  have hp := highArray_val_prod F h1 hmul
  simp only [Function.comp_def,hp] at hv
  have hlocal (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    assumption
  have he := ProbeEulerFinsupp.hasProd_of_summable
    (fun (P : PrimeIdeal) (b : HighValuation)=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) hlocal hv
  have hsum : (∑' v : PrimeIdeal→₀HighValuation,F (highIdeals v))=∑' a,F a := by
    apply highIdeals_injective.tsum_eq
    intro a ha
    have hn := hzero a ha
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hn.1⟩,⟨a.1.2,hn.2.1⟩),(⟨a.2.1,hn.2.2.1⟩,⟨a.2.2,hn.2.2.2⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [←hp,hsum] using he

end

end SevenEighths.ProbePhysical


end OAI
