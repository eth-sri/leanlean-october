module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.PrimaryCharacter
public import OAI.NumberTheory.DirichletL.Moments.FirstColumns

@[expose] public section

namespace OAI


open scoped Classical

namespace SevenEighths.CenteredMomentFirstFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimaryCharacter CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentCommonSupport RayFourExpansion



section
variable (η : Character) (m z e r : ActualEisensteinCubic.O) (hm : m≠0) (hz : Supported (Ideal.span {z})) (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r})) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m)

include hm hz hmLam hm2 in
theorem exists_supported_row_presentation    
            :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:ActualEisensteinCubic.O)}*Ideal.span {z} ∧
      ∀ n : ActualEisensteinCubic.O,elementCoeff τ n=rowTwist (elementHom η) m 1 z n := by
  let r := CompletedGauss.primaryGenerator (Ideal.span {z})
  have hr0 : r≠0 := supported_primaryGenerator_ne_zero _ hz
  have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {z}) hr0
  have hr : Supported (Ideal.span {r}) := hs.1 ▸ hz
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1
  have hx : (1:ActualEisensteinCubic.O)^4*z=(u:ActualEisensteinCubic.O)*ConcretePrimeRowBridge.goodLambda^0*(2:ActualEisensteinCubic.O)^0*r := by
    grind
  let M := η.modulus*Ideal.span {m}*Ideal.span {(72:ActualEisensteinCubic.O)}*Ideal.span {r}
  have hM : M≠⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))) (Ideal.span_singleton_eq_bot.not.mpr hr0)
  have hG := rowTwist_periodic η m 1 z hmLam hm2 u 0 0 r hr hs.2 hx
  refine ⟨rowCharacter M hM (rowTwist (elementHom η) m 1 z) hG (rowTwist_unit η m 1 z),?_,?_⟩
  · change M=_
    dsimp only [M]
    rw [hs.1]
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m 1 z n hmLam hm2 u 0 0 r hx h)))

include η m e r in
theorem first_period_contains     :
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:ActualEisensteinCubic.O)}*Ideal.span {e*r}
    M≤Ideal.span {3*r} ∧ M≤Ideal.span {(12:ActualEisensteinCubic.O)} := by
  dsimp only
  constructor
  · calc
      _ ≤ Ideal.span {(72:ActualEisensteinCubic.O)}*Ideal.span {e*r} := by
        rw [mul_assoc]
        exact Ideal.mul_le_right
      _ = Ideal.span {(72:ActualEisensteinCubic.O)*(e*r)} := Ideal.span_singleton_mul_span_singleton _ _
      _ ≤ _ := Ideal.span_singleton_le_span_singleton.mpr ⟨24*e,by ring⟩
  · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)

include hm he hr hmLam hm2 in
theorem exists_first_character    
         
       
     χ   ξ  :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:ActualEisensteinCubic.O)}*Ideal.span {e*r} ∧
      (∀ n : ActualEisensteinCubic.O,elementCoeff τ n=
        rowTwist (elementHom η) m 1 (e*r) n*maskedPrimaryHom r χ n*
          elementCoeff (primaryRayCharacter ξ) n) ∧
      ∀ n : ActualEisensteinCubic.O,Supported (Ideal.span {n}) → ConcretePrimeRowBridge.goodLambda^2∣n-1 →
        elementCoeff τ n=elementCoeff η n*coprimalityMask m n*
          idealRowHom (e*r) (Ideal.span {n})*χ (Ideal.Quotient.mk _ n)*rayCharacter ξ n := by
  obtain ⟨τ₀,hM,hτ⟩ := exists_supported_row_presentation η m (e*r) hm (supported_mul_elements e r he hr) hmLam hm2
  let τ := (τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ)
  have hp := first_period_contains η m e r
  refine ⟨τ,?_,?_,?_⟩
  · change (τ₀.modulus ⊓ Ideal.span {3*r}) ⊓ Ideal.span {12} = _
    simp_all
  · intro n
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_all]
  · intro n hn hpn
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_primary r _ χ n hpn,
      primaryRayCharacter_primary ξ n hn hpn,rowTwist_extract_sixth_mask _ m 1 (e*r) n hn]
    simp only [one_pow,one_mul]
    rfl

end

end SevenEighths.CenteredMomentFirstFamily



end OAI
