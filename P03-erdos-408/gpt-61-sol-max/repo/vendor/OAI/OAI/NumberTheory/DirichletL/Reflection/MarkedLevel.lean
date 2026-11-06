module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedActualSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment



lemma PrimeFamily.level_coprime {ι : Type*} (P : PrimeFamily ι)
    (Q : Ideal ActualEisensteinCubic.O)  c  (hcQ : Ideal.span {c}=Ideal.span {(9:ActualEisensteinCubic.O)}*Q)
    (hQ : ∀ i, IsCoprime Q (P.ideal i))  i  :
    IsCoprime (Ideal.span {(9:ActualEisensteinCubic.O)*c}) (P.ideal i) := by
  have h9 : IsCoprime (Ideal.span {(9:ActualEisensteinCubic.O)}) (P.ideal i) := by
    rw [← P.generator_span i]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (ShortDraftCRT.primary_coprime_nine _ (P.generator_primary i)).symm
  rw [← Ideal.span_singleton_mul_span_singleton,hcQ]
  exact h9.mul_left (h9.mul_left (hQ i))

lemma markedRowFamily_period {σ : Type*} {m f z : ActualEisensteinCubic.O}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ)  Q 
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) (S.ideal i))
     c  (hcQ : Ideal.span {c}=Ideal.span {(9:ActualEisensteinCubic.O)}*(Q*Ideal.span {(72:ActualEisensteinCubic.O)})) :
    ∀ i, IsCoprime (Ideal.span {(9:ActualEisensteinCubic.O)*c}) ((markedRowFamily D S Q).ideal i) := by
  apply PrimeFamily.level_coprime _ _ _ hcQ
  intro i
  cases i with
  | inl P => exact freePrimeIndex_coprime _ _ P
  | inr i => exact hS i


end SevenEighths.InverseReflectedPhase

end OAI
