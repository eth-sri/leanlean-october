module

public import OAI.NumberTheory.DirichletL.Detector.GramJoint

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem jointExtension_source (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : ActualEisensteinCubic.O) (hC : Supported (Ideal.span {C}))
    (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r : ActualEisensteinCubic.O) (hr : Supported (Ideal.span {r}))
    (hpr : ConcretePrimeRowBridge.goodLambda^2∣r-1) (hk : k=u.val*ConcretePrimeRowBridge.goodLambda^a*(2:ActualEisensteinCubic.O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (ActualEisensteinCubic.O⧸∏i,P i^c i)] [∀i,Fintype (ActualEisensteinCubic.O⧸P i^c i)]
    (n₁ n₂ : ActualEisensteinCubic.O) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : ConcretePrimeRowBridge.goodLambda^2∣n₁-1) (hp₂ : ConcretePrimeRowBridge.goodLambda^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
        actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
          (supported_mul_elements C n₂ hC h₂) (C*k) := by
  rw [actual_common_lift C n₁ n₂ k hC h₁ h₂ hp₁ hp₂ hn,
    actualCommon_eq_globalExtension C hC P hg c hc hcop he n₁ n₂ k hn,
    ←numeratorExtension_primary u a b r k n₁ hr hpr hk h₁ hp₁,
    ←numeratorExtension_neg_primary u a b r k n₂ hr hpr hk h₂ hp₂]
  simp only [jointExtension,jointFixed,numeratorExtension,MonoidHom.mul_apply,
    movingNumeratorRow,MonoidHom.coe_mk,OneHom.coe_mk,star_mul]
  ring

lemma lowGramCoefficient_eq_primary (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      primaryCoefficient S hS σ (primaryGenerator s.val) := by
  have hp : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator s.val-1 := (primaryGenerator_spec s.val
    (supported_primaryGenerator_ne_zero s.val s.property)).2
  rw [primaryCoefficient,ite_eq_left hp]
  exact lowGramCoefficient_eq_extension S hS hbad σ s

end SevenEighths.ProbeGramCommon
end

end OAI
