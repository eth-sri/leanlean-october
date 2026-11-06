module

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalFrozenEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CompletedFiberSource
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalCellArithmetic

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CompletedGauss
noncomputable section
universe v

lemma maximal_prime_level_coprime (P : Ideal ActualEisensteinCubic.O) (hP : P.IsMaximal)
    (hg : ConcretePrimeRowBridge.goodLambda∉P) (Q₀ : Ideal ActualEisensteinCubic.O) (c : ActualEisensteinCubic.O)
    (hc : Ideal.span {c}=Ideal.span {(9:ActualEisensteinCubic.O)}*Q₀) (hQ : IsCoprime Q₀ P) :
    IsCoprime (Ideal.span {(9:ActualEisensteinCubic.O)*c}) P := by
  let S : PrimeFamily Unit := ⟨fun _ => P,by grind,by grind⟩
  exact S.level_coprime Q₀ c hc (by grind) ()

lemma original_powerful_norm_le (J : Ideal ActualEisensteinCubic.O) (hJ : J≠0) :
    (Ideal.absNorm (rowPowerfulPart J):ℝ)≤(Ideal.absNorm J:ℝ) := by
  have he := congrArg (fun I : Ideal ActualEisensteinCubic.O => (Ideal.absNorm I:ℝ)) (row_powerful_simple_product J hJ)
  simp only [map_mul,Nat.cast_mul] at he
  have hs := QuadraticMainBoundary.norm_one_le (rowSimplePart_ne_zero J)
  nlinarith

end
end SevenEighths.InverseReflectedPhase

end OAI
