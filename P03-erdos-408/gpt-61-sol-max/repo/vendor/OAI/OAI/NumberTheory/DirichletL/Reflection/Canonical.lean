module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.Common

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section



structure PrimeFamily (ι : Type*) where
  ideal : ι → Ideal ActualEisensteinCubic.O
  maximal : ∀ i, (ideal i).IsMaximal
  good : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ ideal i

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)
instance idealMaximal (i : ι) : (G.ideal i).IsMaximal := G.maximal i

def generator (i : ι)  := primaryPrime (G.ideal i)

lemma generator_ne_zero  i  : G.generator i ≠ 0 := primaryPrime_ne_zero _ (G.good i)
lemma generator_span  i  : Ideal.span {G.generator i} = G.ideal i :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.1
lemma generator_primary  i  : ConcretePrimeRowBridge.goodLambda^2 ∣ G.generator i-1 :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.2
instance generatorMaximal (i : ι) : (Ideal.span {G.generator i}).IsMaximal :=
  G.generator_span i ▸ G.maximal i
lemma generator_good  i  : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {G.generator i} := by
  rw [G.generator_span]
  exact G.good i

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

lemma generator_product_primary [Fintype ι] : ConcretePrimeRowBridge.goodLambda^2 ∣ (∏ i, G.generator i)-1 :=
  OAI.CubicEisenstein.primary_finset_product Finset.univ G.generator fun i x => OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.generator_primary G i

lemma generator_coprime_period  N 
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i))  i  :
    IsCoprime N (G.generator i) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [G.generator_span]
  exact hN i

lemma generator_product_coprime_period [Fintype ι]  N c  (hc : c ∣ N)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    IsCoprime (∏ i, G.generator i) (N*c) := by
  have hh : IsCoprime N (∏ i, G.generator i) :=
    IsCoprime.prod_right (fun i _ => G.generator_coprime_period N hN i)
  exact hh.symm.mul_right (hh.symm.of_isCoprime_of_dvd_right hc)

theorem exists_controlled [Fintype ι]  N a c   mode 
    (hc : c ≠ 0) (hN : (9:ActualEisensteinCubic.O)*c ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime G.ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    Nonempty (ControlledStratumArithmetic G.generator N a c mode) := by
  apply exists_controlledStratumArithmetic G.generator G.generator_ne_zero
  · intro i k hik
    simpa only [G.generator_span] using hcop hik
  · exact G.generator_primary
  · exact hc
  · exact hN
  · exact hbase
  · exact hac
  · exact G.generator_coprime_period N hNp

end PrimeFamily

end
end SevenEighths.InverseReflectedPhase

end OAI
