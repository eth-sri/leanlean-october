module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicSectors

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar

open Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex


open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics

open Filter
open MulChar AddChar
open MulChar AddChar

open Filter Asymptotics MeasureTheory

open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory

open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory

open Filter Asymptotics MeasureTheory

open Filter Asymptotics MeasureTheory

open MeasureTheory Real














open MeasureTheory Set



open ActualEisensteinCubic UniqueFactorizationMonoid


namespace SecondPassArithmetic


open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

section


open MeasureTheory
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter crossCoeff)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel
  actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

structure SquarefreeBudgetData where
  windows : Fin 7 → ℝ → ℂ
  arithmetic : ℝ
  smooth : ℝ
  windowBound : ℝ
  tail : ℝ
  arithmetic_pos : 0 < arithmetic
  smooth_nonneg : 0 ≤ smooth
  windowBound_nonneg : 0 ≤ windowBound
  tail_pos : 0 < tail

end SecondPassArithmetic

namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

end

open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

end FirstPassCubeLabels
end


namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

end

end OAI
