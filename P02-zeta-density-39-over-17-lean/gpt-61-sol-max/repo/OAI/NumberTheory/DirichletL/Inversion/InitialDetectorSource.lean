module
public import OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
public import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
public import OAI.NumberTheory.DirichletL.Detector.RayPoolGood

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace SevenEighths.InverseInitialDetectorSource
open HeckeFamily HeckeInverseAmplification
open InverseInitialRawDictionary
open scoped HeckeO

def baseCharacter (data : RowData) : Character := data.character ⟨1,one_ne_zero⟩

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

theorem base_nonzero_prime (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    fixedBase data.η data.m data.f P≠0 := by
  rw [←baseCharacter_coeff]
  exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hN)

def primeProfile (V : ℝ→ℂ) (D : ℝ) (ζ : ℂ) (P : Ideal O) : ℂ :=
  V ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(ζ-1)






