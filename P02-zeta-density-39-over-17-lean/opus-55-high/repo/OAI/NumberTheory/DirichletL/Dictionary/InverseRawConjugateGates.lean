module
public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
public import OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

section
variable (η:Ideal O→*ℂ)
include η
theorem conjugate_element_apply(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]
end

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  pm_3698 hq he hn hp raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  grind

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI
