module

public import OAI.NumberTheory.DirichletL.Moments.FirstAssembly

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstFrequency
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstNormalization CenteredMomentFirstReduced CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem normalized_dilated_frequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
     hcop 
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
     j  (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
     e a b   ha   hb 
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
     k   h  :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    let ρ := finiteSexticRow P hg j
    tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
      ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
      tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
        (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)*
        originalPhase e r ρ a b*
        ((gaussRow a ha h/(‖eisEmbedding a‖:ℂ))*star (gaussRow b hb (-h)/(‖eisEmbedding b‖:ℂ))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have he := normalized_active_coefficient P hcop hg hchar j hj0 hj6 a b ha hb har hbr h
  dsimp only at he
  rw [Complex.ofReal_div]
  calc
    _ = (k:ℂ)*tripleRow a b (finitePrimeModulus P) (supportedModulusCharacter a ha)
        (supportedModulusCharacter b hb)⁻¹
        (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) e*
        (tripleFourier a b (finitePrimeModulus P) (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹
          (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) h /
          (‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2:ℝ)) := by ring
    _ = _ := by
      rw [he,tripleRow,← MulChar.star_apply',supportedModulusCharacter_mk,
        supportedModulusCharacter_mk,
        principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) e]
      simp only [originalPhase,Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring

def dilatedFrequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (j : ι → ℕ)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (k : ℝ) (h : O) : ℂ :=
  let r := finitePrimeModulus P
  let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
  tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
    ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h

end SevenEighths.CenteredMomentFirstFrequency

end

end OAI
