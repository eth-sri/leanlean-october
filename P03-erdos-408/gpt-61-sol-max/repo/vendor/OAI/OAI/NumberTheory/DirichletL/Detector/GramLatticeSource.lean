module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.GramPrimaryLattice

@[expose] public section

namespace OAI


open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion

local notation "Id" => Ideal ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]

section
variable (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : ActualEisensteinCubic.O) (hCd : ConcretePrimeRowBridge.goodLambda^2∣C*d-1) (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r : ActualEisensteinCubic.O) (hr : Supported (Ideal.span {r})) (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉P i) (c : ι→ℕ)
include S hS hbad σ C k d hCd u a b r hr P hg c

lemma jointExtension_zero_off_primary_left    
         
             
           
     n m  (hn : ¬(Supported (Ideal.span {n}) ∧ ConcretePrimeRowBridge.goodLambda^2∣n-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*n))=0 := by
    by_contra h
    apply hn
    apply primaryCoefficient_residual S hS hbad σ (C*d) n hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,zero_mul]

lemma jointExtension_zero_off_primary_right    
         
             
           
     n m  (hm : ¬(Supported (Ideal.span {m}) ∧ ConcretePrimeRowBridge.goodLambda^2∣m-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*m))=0 := by
    by_contra h
    apply hm
    apply primaryCoefficient_residual S hS hbad σ (C*d) m hCd
    simpa only [mul_assoc] using h
  simp_all [jointExtension, jointFixed]

theorem jointExtension_ideal_lattice    
         
             
            (W : ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      jointExtension S hS σ C k u a b r hr P hg c (d*primaryGenerator I.val) (d*primaryGenerator J.val)*
        W (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : ActualEisensteinCubic.O,∑'m : ActualEisensteinCubic.O,jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m := by
  apply primary_ideal_pair_tsum (fun n m=>jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m)
  · simp_all [jointExtension_zero_off_primary_left]
  simp_all [jointExtension_zero_off_primary_right]

end

end SevenEighths.ProbeGramCommon


end OAI
