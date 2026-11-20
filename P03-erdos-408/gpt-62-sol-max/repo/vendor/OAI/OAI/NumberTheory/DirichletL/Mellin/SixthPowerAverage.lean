module

public import OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity

@[expose] public section

namespace OAI

noncomputable section

namespace SixthPowerAverage

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex
open scoped Classical
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding
open ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set


section

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge

lemma prime_coprime_span_iff (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (b : ActualEisensteinCubic.O) : IsCoprime P (Ideal.span {b}) ↔ b∉P := by
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint,
    Ideal.span_singleton_le_iff_mem]

end


end SixthPowerAverage

end

end OAI
