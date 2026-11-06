module
public import OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
public import OAI.NumberTheory.DirichletL.Detector.GramMean

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def numeratorExtension (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) : O→*ℂ :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr

section
variable (u : Oˣ) (a b : ℕ) (r k n : O) (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1)
include u a b r k n hr hpr hk hn hpn
lemma numeratorExtension_primary :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm

lemma numeratorExtension_neg_primary :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp only [Units.val_neg,hk]
  ring
end

lemma numerator_good_norm_le (u : Oˣ) (a b : ℕ) (r k : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  simp_all
  simp_all

end SevenEighths.ProbeGramCommon
end

end OAI
