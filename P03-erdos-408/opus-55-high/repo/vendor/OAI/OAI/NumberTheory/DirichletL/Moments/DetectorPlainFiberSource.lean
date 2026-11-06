module

public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource
public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeInverseAmplification
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal
open CenteredMomentNaturalFixedRaySource HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot
open CenteredMomentSecondHeightFamily
variable {M:Ideal HeckeFamily.O}{H:Subgroup (HeckeFamily.O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def plainProfile (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (j:ℕ)(σ t:ℝ):ℝ→ℂ:=
  twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
    (orientedFrequency F.reverse t)

def slotWindow (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)(x:ℝ):ℂ:=
  conj (F.profile s x*(x:ℂ)^(F.external s-1))

def fiberPool (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot):
    Finset (CenteredMomentAddedZeroUniform.Tuple selected):=
  completePool (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (9/4) (9/4) (U^F.m) (U^F.m)

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ):Ideal HeckeFamily.O→ℂ:=
  finiteColumnCoefficient (fiberPool F selected)
    (uncenteredProfileCoefficient 1 (fun _:selected=>idealCoeff η.inverse)
      (fun s:selected=>slotWindow F s.val) (fun s:selected=>U^(F.widths s.val))
      (plainProfile F j σ t) (plainProfile F k σ t) (U^F.m) (U^F.m) 1 1 1)

theorem detector_row_eq_source (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(u:FreeRow)(hU:0<U):
    detectorPositiveRow F η selected j k σ t u=
      (Real.sqrt ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):ℂ)⁻¹*
      ∑I∈finiteColumns (fiberPool F selected),fiberCoefficient F η selected j k σ t I*
        CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I:=by
  have he:=positiveSlotRow_eq_complete_source η fixedBadMask 1 u.val 0
    (dvd_mul_right _ _) (dvd_mul_left _ _)
    (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (by positivity) (by positivity)
  rw [natural_unit_mask_positive (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1)] at he
  unfold detectorPositiveRow
  rw [rowMaskElement_eq_fixed]
  exact he

def radialMajorant : 𝓢(ℝ,ℂ):=
  Classical.choose DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant

lemma radialMajorant_compact : HasCompactSupport (radialMajorant:ℝ→ℂ):=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).1

lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x

lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI
