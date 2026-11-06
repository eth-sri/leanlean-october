module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainStateDictionary
open HeckeFamily HeckeDetectorRawFiber HeckePrimeAnnular
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

section
variable (F:Fiber M H Label Slot U a ε tstar T allowance i)

lemma plainProfile_eq_detectorSchwartz
      j  σ t :
    plainProfile F j σ t=(detectorSchwartz F.reverse j σ t:ℝ→ℂ):=by
  funext x
  exact (detectorSchwartz_apply F.reverse j σ t x).symm

theorem retainedSourceEnergy_eq_energy
     keep (F:Fiber M H Label Slot U a ε tstar T allowance i)
     η (selected:Finset Slot) j k  σ t  Φ (hU:0<U):
    retainedSourceEnergy keep F η selected j k σ t Φ=
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (plainProfile F j σ t) (plainProfile F k σ t)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m) keep Φ U:=(positive_energy_eq_complete_source η 0 keep
    (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (fun _=>Real.rpow_pos_of_pos hU _)
    (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) Φ U).symm

theorem retainedSourceEnergy_empty_eq_plainEnergy
     
     η  Q  Φ  bΦ δ 
     hU  hδ  hs 
     hp  hη 
     j k  σ t :
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (initialState η Q Φ bΦ U δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=by
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  rfl

end

end SevenEighths.CenteredMomentDetectorPlainStateDictionary



end OAI
