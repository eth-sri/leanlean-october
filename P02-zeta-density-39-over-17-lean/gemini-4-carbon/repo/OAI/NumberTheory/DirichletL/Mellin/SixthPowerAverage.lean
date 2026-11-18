module
public import OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity

@[expose] public section

namespace OAI

noncomputable section

namespace SixthPowerAverage

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set
open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff

section

open Metric EisensteinSchwartzPoisson

end

section

open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge

lemma prime_coprime_span_iff (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (b : ActualEisensteinCubic.O) : IsCoprime P (Ideal.span {b}) ↔ b∉P := by
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint,
    Ideal.span_singleton_le_iff_mem]

end

section


section
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

end

open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open InitialMeanSquare
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion

end

section

open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open IdealMobiusDivisorSum hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion InitialMeanSquare

def weightedMoebius {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  baseChangeWeight χ I*totientDensity I

def outsideWeight {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O→ℂ :=
  FiniteSFactor.outsideWeight S (weightedMoebius χ)

end

open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion InitialMeanSquare CompactMellinBridge

end SixthPowerAverage

end

end OAI
