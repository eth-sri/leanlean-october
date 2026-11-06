module
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget
open CenteredMomentSourceLiveColumn
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma main_coefficients_nonneg (q Z K ell deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤ mainPowers q Z K ell deficit paid saving r j:=by
  pm_7705 mainPowers

lemma error_coefficients_nonneg (p:O)(k:ℕ)(q Z K deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  pm_7705 errorPowers

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

end

end OAI
