module

public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial
public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawFiberSource
public import OAI.NumberTheory.DirichletL.Descent.Basic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection ConcreteTraceCRT CanonicalQuadraticSieve ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def radialMajorant  :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

theorem radialMajorant_nonneg  x  : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one  x  (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI
