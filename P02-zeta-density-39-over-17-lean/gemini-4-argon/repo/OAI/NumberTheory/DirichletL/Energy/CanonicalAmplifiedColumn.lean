module
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget CenteredMomentSourceLiveColumn
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma main_coefficients_nonneg (q Z K ell deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

lemma error_coefficients_nonneg (p:O)(k:ℕ)(q Z K deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity
