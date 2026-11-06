module
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay

public import OAI.NumberTheory.DirichletL.Moments.AmplificationShortening

@[expose] public section

namespace OAI


open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocation
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentSupportedCorrelation


alias primaryGenerator_power := _root_.OAI.CubicEisenstein.primaryGenerator_pow

theorem primeRemainder_primary  p   hp  (hpp : goodLambda^2 ∣ p-1)
     a   ha  (hpa : goodLambda^2 ∣ a-1) :
    goodLambda^2 ∣ primeRemainder p hp a (supported_element_ne_zero a ha)-1 := by
  let r := primeRemainder p hp a (supported_element_ne_zero a ha)
  have hr := primeRemainder_supported p hp a ha
  have hgen := supported_primaryGenerator_ne_zero (Ideal.span {r}) hr
  have he : a = p^(multiplicity p a)*primaryGenerator (Ideal.span {r}) := by
    calc
      a = primaryGenerator (Ideal.span {a}) := (primaryGenerator_span a
        (supported_element_ne_zero a ha) hpa).symm
      _ = _ := by
        conv_lhs => rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1]
        rw [← Ideal.span_singleton_mul_span_singleton,primaryGenerator_mul,
          ← Ideal.span_singleton_pow,primaryGenerator_power,primaryGenerator_span p hp.ne_zero hpp]
  have hre : r = primaryGenerator (Ideal.span {r}) := by
    apply mul_left_cancel₀ (pow_ne_zero (multiplicity p a) hp.ne_zero)
    exact (primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1.symm.trans he
  change goodLambda^2 ∣ r-1
  rw [hre]
  exact (primaryGenerator_spec _ hgen).2

end SevenEighths.CenteredMomentAmplificationAllocation



end OAI
