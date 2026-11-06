module

public import OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex

open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics

open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid


namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

variable (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

end

end InitialMeanSquare

end

end OAI
