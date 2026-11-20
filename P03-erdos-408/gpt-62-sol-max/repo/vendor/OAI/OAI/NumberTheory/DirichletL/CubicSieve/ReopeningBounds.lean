module

public import OAI.NumberTheory.DirichletL.Eisenstein.BarrierPotential

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex
open scoped Classical
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding
open ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace SecondPassArithmetic


end SecondPassArithmetic

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation

def progressingCubes (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (H₀ : ℝ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)) :=
  Q.filter (fun v=>H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))

end CanonicalRowCompletion

namespace SecondPassArithmetic


end SecondPassArithmetic

end

end OAI
