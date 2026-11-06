module
public import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
public import OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic
public import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel
public import OAI.NumberTheory.DirichletL.Reflection.ChoiceTransport
public import OAI.NumberTheory.DirichletL.Reflection.TupleSectors

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve
noncomputable section
open scoped EisensteinEis

lemma residual_level_coprime (K Q₀ : Ideal Eis) (hK : Admissible K)
    (c : Eis) (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hcop : IsCoprime Q₀ K) :
    IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  rw [←PrimeFamily.residual_product K hK]
  apply IsCoprime.prod_right_iff.mpr
  intro i hi
  exact (PrimeFamily.residual K hK).level_coprime Q₀ c hc
    (fun i => hcop.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK i)) i

variable {φ σ : Type*} [Fintype σ] [DecidableEq σ]





