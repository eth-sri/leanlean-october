module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
public import OAI.NumberTheory.DirichletL.Detector.GramMean

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT



def numeratorExtension (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r ) (hr : Supported (Ideal.span {r}))  :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr

section
variable (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r k n : ActualEisensteinCubic.O) (hr : Supported (Ideal.span {r})) (hpr : ConcretePrimeRowBridge.goodLambda^2∣r-1) (hk : k=u.val*ConcretePrimeRowBridge.goodLambda^a*(2:ActualEisensteinCubic.O)^b*r) (hn : Supported (Ideal.span {n})) (hpn : ConcretePrimeRowBridge.goodLambda^2∣n-1)

include hpr hk hn hpn in
lemma numeratorExtension_primary      
       
     
        :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm

include hpr hk hn hpn in
lemma numeratorExtension_neg_primary      
       
     
        :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  simp_all [numeratorExtension_primary]

include hk in
lemma numerator_good_norm_le      
      (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hk0))
  simp_all

end

end SevenEighths.ProbeGramCommon
end

end OAI
