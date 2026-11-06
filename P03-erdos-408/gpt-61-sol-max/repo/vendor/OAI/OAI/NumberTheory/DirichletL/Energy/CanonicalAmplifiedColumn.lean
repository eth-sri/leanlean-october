module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget
open CenteredMomentSourceLiveColumn




section
variable (p : HeckeFamily.O) (k : ℕ) (q Z K ell deficit paid saving r : ℝ) (hq : 0≤q) (hZ : 0≤Z) (hK : 0≤K)

include hq hZ hK in
lemma main_coefficients_nonneg  
       :∀j,0≤mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

include hq hZ hK in
lemma error_coefficients_nonneg    
       :∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

end

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

end

end OAI
