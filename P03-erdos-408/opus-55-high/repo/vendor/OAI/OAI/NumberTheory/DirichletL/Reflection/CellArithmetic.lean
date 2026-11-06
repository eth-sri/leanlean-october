module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
public import OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic
public import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel
public import OAI.NumberTheory.DirichletL.Reflection.ChoiceTransport
public import OAI.NumberTheory.DirichletL.Reflection.TupleSectors

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section

lemma residual_level_coprime (K Q₀ : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (c : ActualEisensteinCubic.O) (hc : Ideal.span {c}=Ideal.span {(9:ActualEisensteinCubic.O)}*Q₀) (hcop : IsCoprime Q₀ K) :
    IsCoprime (Ideal.span {(9:ActualEisensteinCubic.O)*c}) K := by
  rw [←PrimeFamily.residual_product K hK]
  apply IsCoprime.prod_right_iff.mpr
  intro i hi
  exact (PrimeFamily.residual K hK).level_coprime Q₀ c hc
    (fun i => hcop.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK i)) i

variable {φ σ : Type*} [Fintype σ] [DecidableEq σ]

end
end SevenEighths.InverseReflectedPhase

end OAI
