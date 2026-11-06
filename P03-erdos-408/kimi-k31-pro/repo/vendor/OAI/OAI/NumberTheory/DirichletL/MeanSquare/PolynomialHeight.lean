module

public import OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight

@[expose] public section

namespace OAI

noncomputable section

namespace CompletedHeight

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap



section

open CompletedGauss hiding O
open SecondPassArithmetic (normPhase normHeightTwist)
open FourierBridge (logPhase)

lemma logPhase_triple (t x : ℝ) : logPhase t (3*x)=(logPhase t x)^3 := by
  rw [show 3*x=x+x+x by ring,FourierBridge.logPhase_add,FourierBridge.logPhase_add]
  ring

lemma columnWeight_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) (I : Ideal ActualEisensteinCubic.O) :
    columnWeight (normHeightTwist Ψ t) I =
      logPhase t (Real.log (Ideal.absNorm I:ℝ))*columnWeight Ψ I := by
  by_cases hI : primaryGenerator I=0
  · have hz : squarefreeGaussCoefficient I=0 := by simp [squarefreeGaussCoefficient,hI]
    simp only [columnWeight,hz,zero_mul,mul_zero]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryGenerator I) hI
    rw [primaryGenerator_norm_sq I hI] at hn
    simp only [columnWeight,normHeightTwist,MonoidHom.mul_apply,hn]
    ring

lemma cubeWeight_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) (I : Ideal ActualEisensteinCubic.O) :
    cubeWeight (normHeightTwist Ψ t) I =
      logPhase t (3*Real.log (Ideal.absNorm I:ℝ))*cubeWeight Ψ I := by
  by_cases hI : primaryGenerator I=0
  · simp [cubeWeight,hI,FiniteGaussPhase.angularFactor]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryGenerator I) hI
    rw [primaryGenerator_norm_sq I hI] at hn
    change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
        (Ψ (primaryGenerator I)*normPhase t (primaryGenerator I))^3/(Ideal.absNorm I:ℂ)=_
    rw [hn,logPhase_triple]
    change _ = (logPhase t (Real.log (Ideal.absNorm I:ℝ)))^3*
      (star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
        Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ))
    ring

lemma summand_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X)
    (I J : Ideal ActualEisensteinCubic.O) :
    summand (normHeightTwist Ψ t) W X I J =
      logPhase t (Real.log X)*summand Ψ (normTwistedSource W t) X I J := by
  by_cases hI : I=0
  · simp only [hI,CompletedGauss.summand_zero_left,mul_zero]
  by_cases hJ : J=0
  · simp only [hJ,CompletedGauss.summand_zero_right,mul_zero]
  have hni : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hnj : 0<(Ideal.absNorm J:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one J hJ)
  have hl : Real.log X+Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)=
      Real.log (Ideal.absNorm I:ℝ)+3*Real.log (Ideal.absNorm J:ℝ) := by
    rw [Real.log_div (mul_pos hni (pow_pos hnj 3)).ne' hX.ne',
      Real.log_mul hni.ne' (pow_pos hnj 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (Real.log X)*
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)) =
      logPhase t (Real.log (Ideal.absNorm I:ℝ))*logPhase t (3*Real.log (Ideal.absNorm J:ℝ)) := by
    rw [←FourierBridge.logPhase_add,hl,FourierBridge.logPhase_add]
  simp only [summand,columnWeight_normHeight,cubeWeight_normHeight,Vstar,normTwistedSource]
  linear_combination -(columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I:ℝ):ℂ) * cubeWeight Ψ J *
    (Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X):ℂ)*
      W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X))*hphase

theorem completedT_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    completedT (normHeightTwist Ψ t) W X =
      logPhase t (Real.log X)*completedT Ψ (normTwistedSource W t) X := by
  simp only [completedT,summand_normHeight Ψ W t X hX,tsum_mul_left]

@[simp] theorem completedT_normHeight_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (t X : ℝ) (hX : 0<X) :
    ‖completedT (normHeightTwist Ψ t) W X‖=‖completedT Ψ (normTwistedSource W t) X‖ := by
  rw [completedT_normHeight Ψ W t X hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem shortCompletedSum_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X H₀ : ℝ) (hX : 0<X) :
    shortCompletedSum (normHeightTwist Ψ t) W X H₀ =
      logPhase t (Real.log X)*shortCompletedSum Ψ (normTwistedSource W t) X H₀ := by
  rw [shortCompletedSum_eq,shortCompletedSum_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hn : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one
    (norm_at_least_one H ((mem_shortCubeRange H₀ H).mp hH).1)
  rw [cubeWeight_normHeight,completedT_normHeight Ψ W t _ (div_pos hX (pow_pos hn 3))]
  have hl : 3*Real.log (Ideal.absNorm H:ℝ)+Real.log (X/(Ideal.absNorm H:ℝ)^3)=Real.log X := by
    rw [Real.log_div hX.ne' (pow_pos hn 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (3*Real.log (Ideal.absNorm H:ℝ))*
      logPhase t (Real.log (X/(Ideal.absNorm H:ℝ)^3))=logPhase t (Real.log X) := by
    rw [←FourierBridge.logPhase_add,hl]
  linear_combination (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedT Ψ (normTwistedSource W t) (X/(Ideal.absNorm H:ℝ)^3)*hphase

@[simp] theorem shortCompletedSum_normHeight_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (t X H₀ : ℝ) (hX : 0<X) :
    ‖shortCompletedSum (normHeightTwist Ψ t) W X H₀‖=
      ‖shortCompletedSum Ψ (normTwistedSource W t) X H₀‖ := by
  rw [shortCompletedSum_normHeight Ψ W t X H₀ hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end

open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O

end CompletedHeight

end

end OAI
