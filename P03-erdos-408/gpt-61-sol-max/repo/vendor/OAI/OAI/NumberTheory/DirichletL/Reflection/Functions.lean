module

public import OAI.NumberTheory.DirichletL.Reflection.Transport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein




section
variable {κ : Type*} [Fintype κ] {p q : κ → ActualEisensteinCubic.O} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal] {a c : ActualEisensteinCubic.O} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {q i}) (j j' : κ → ℕ)
include κ p q a c mode s hp hg hq hqg j j'

lemma sourceRowPhase_congr_functions    
         
         
       
       
       R F   u   m  (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions    
         
         
       
       
       S F   u   m  (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

end


end SevenEighths.InverseReflectedPhase

end OAI
