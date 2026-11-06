module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalFrozenEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CompletedFiberSource
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalCellArithmetic

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment


universe v

lemma maximal_prime_level_coprime  P  (hP : P.IsMaximal)
    (hg : ConcretePrimeRowBridge.goodLambda∉P) (Q₀ : Ideal ActualEisensteinCubic.O)  c 
    (hc : Ideal.span {c}=Ideal.span {(9:ActualEisensteinCubic.O)}*Q₀) (hQ : IsCoprime Q₀ P) :
    IsCoprime (Ideal.span {(9:ActualEisensteinCubic.O)*c}) P := OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.level_coprime { ideal := fun x => P, maximal := fun x => hP, good := fun x => hg } Q₀ c hc (fun x => hQ) ()

lemma original_powerful_norm_le  J  (hJ : J≠0) :
    (Ideal.absNorm (rowPowerfulPart J):ℝ)≤(Ideal.absNorm J:ℝ) := by
  have he := congrArg (fun I : Ideal ActualEisensteinCubic.O => (Ideal.absNorm I:ℝ)) (row_powerful_simple_product J hJ)
  simp only [map_mul,Nat.cast_mul] at he
  have hs := QuadraticMainBoundary.norm_one_le (rowSimplePart_ne_zero J)
  
  nlinarith


end SevenEighths.InverseReflectedPhase

end OAI
