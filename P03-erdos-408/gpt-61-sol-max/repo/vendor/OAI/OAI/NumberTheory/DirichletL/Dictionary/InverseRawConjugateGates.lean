module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
public import OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds

@[expose] public section

namespace OAI



open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile


theorem conjugate_element_apply  η  x :
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors  η  Q 
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=fun x y hxy => congrArg Star.star (h x y hxy)

theorem conjugate_element_norm  η  x :
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates  data :
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  simp_all [conjugate_element_factors, conjugate_element_norm]

theorem raw_conjugate_zero_outside  data  I 
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate  W  θ :
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

end SevenEighths.DetectorDictionaryInverseRawConjugateGates



end OAI
