module

public import OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open ActualEisensteinCubic ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open scoped ContDiff
open Set


namespace InitialMeanSquare

section
open ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

end

end InitialMeanSquare

end

end OAI
