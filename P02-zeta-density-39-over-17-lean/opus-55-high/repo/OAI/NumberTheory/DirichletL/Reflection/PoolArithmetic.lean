module
public import OAI.NumberTheory.DirichletL.Reflection.OriginalDictionary

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section
variable (R Q Q₀ : Ideal Eis)
include R Q Q₀
lemma poolPrimeFamily_pairwise :
    Pairwise (Function.onFun IsCoprime (poolPrimeFamily R Q Q₀).ideal) := by
  intro P T hPT
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPT)

lemma poolPrimeFamily_period (P : FreeReflection.pool R Q Q₀) :
    IsCoprime Q₀ ((poolPrimeFamily R Q Q₀).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  exact FreeReflection.pool_free R Q Q₀ P (Ideal.dvd_iff_le.mp h)

lemma poolPrimeFamily_odd (P : FreeReflection.pool R Q Q₀) :
    ringChar (Eis⧸(poolPrimeFamily R Q Q₀).ideal P)≠2 := FreeReflection.pool_odd R Q Q₀ P
end

section
variable (R I Q Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hQ : Q≠0) (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q) (P : FreeReflection.pool R Q Q₀)
include R I Q Q₀ hR hI hQ hpow hmask P
lemma poolPrimeFamily_fiber_row_coprime :
    IsCoprime ((poolPrimeFamily R Q Q₀).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_divides :
    (poolPrimeFamily R Q Q₀).ideal P∣I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)
end

lemma poolPrimeFamily_fiber_exponent (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    completedLocalExponent I F ((poolPrimeFamily R Q Q₀).ideal P)=completedLocalExponent R F P.val :=
  nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask P

end
end SevenEighths.InverseReflectedPhase

end OAI
