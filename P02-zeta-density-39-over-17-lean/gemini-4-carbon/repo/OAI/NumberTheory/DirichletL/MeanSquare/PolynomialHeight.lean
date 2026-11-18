module
public import OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight

@[expose] public section

namespace OAI

noncomputable section

namespace CompletedHeight

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set
open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff

section

open CompletedGauss hiding O
open CompletedDyadic
open CanonicalQuadraticSieve hiding O

end

section

open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O

end

section

open CompletedGauss hiding O
open SecondPassArithmetic (normPhase normHeightTwist)
open FourierBridge (logPhase)

end

open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O

end CompletedHeight

end

end OAI
