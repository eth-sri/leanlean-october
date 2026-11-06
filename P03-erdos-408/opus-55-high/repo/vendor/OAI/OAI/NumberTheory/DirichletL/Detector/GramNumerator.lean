module

public import OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
public import OAI.NumberTheory.DirichletL.Detector.GramMean

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion

def numeratorExtension (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r : ActualEisensteinCubic.O) (hr : Supported (Ideal.span {r})) : ActualEisensteinCubic.O→*ℂ :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr

lemma numeratorExtension_primary (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r k n : ActualEisensteinCubic.O)
    (hr : Supported (Ideal.span {r})) (hpr : ConcretePrimeRowBridge.goodLambda^2∣r-1)
    (hk : k=u.val*ConcretePrimeRowBridge.goodLambda^a*(2:ActualEisensteinCubic.O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : ConcretePrimeRowBridge.goodLambda^2∣n-1) :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm

lemma numeratorExtension_neg_primary (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r k n : ActualEisensteinCubic.O)
    (hr : Supported (Ideal.span {r})) (hpr : ConcretePrimeRowBridge.goodLambda^2∣r-1)
    (hk : k=u.val*ConcretePrimeRowBridge.goodLambda^a*(2:ActualEisensteinCubic.O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : ConcretePrimeRowBridge.goodLambda^2∣n-1) :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp_all

lemma numerator_good_norm_le (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r k : ActualEisensteinCubic.O)
    (hk : k=u.val*ConcretePrimeRowBridge.goodLambda^a*(2:ActualEisensteinCubic.O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · simp_all
  simp_all

end SevenEighths.ProbeGramCommon
end

end OAI
