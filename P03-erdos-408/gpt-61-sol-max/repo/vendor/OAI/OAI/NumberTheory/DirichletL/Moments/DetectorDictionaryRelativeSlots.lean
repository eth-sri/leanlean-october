module

public import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots

@[expose] public section

namespace OAI


open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

section
variable (M : Ideal O) (H : Subgroup (O⧸M)ˣ) (η χ ν : Character) (m A z : O) (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)

lemma normalizedSlot_character    
     S   β   t D  :
    normalizedSlot η m A z S (fun P=>idealCoeff ν P*β P) t D=
      normalizedSlot (η.product ν) m A z S β t D := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealCoeff_product]
  ring

include hrow in
lemma product_row_presentation    
      :
    ∀n,elementCoeff (χ.product ν) n=rowTwist (elementHom (η.product ν)) m 1 (A*z) n := by
  intro n
  rw [elementCoeff_product,hrow]
  change (elementCoeff η n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n)*elementCoeff ν n=
    elementCoeff (η.product ν) n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n
  rw [elementCoeff_product]
  ring

include hrow in
theorem relative_normalizedSlot_eq_ray    
       
     
     W   b D σ t v  (hD : 0<D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun P=>idealCoeff ν P*HeckePrimeAnnular.annularWeight W D σ v P) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product ν) W b D σ (t+v) := by
  rw [normalizedSlot_character]
  exact CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H (η.product ν) (χ.product ν)
    m A z (product_row_presentation η χ ν m A z hrow) W b D σ t v hD

end

end SevenEighths.CenteredMomentDetectorDictionary



end OAI
