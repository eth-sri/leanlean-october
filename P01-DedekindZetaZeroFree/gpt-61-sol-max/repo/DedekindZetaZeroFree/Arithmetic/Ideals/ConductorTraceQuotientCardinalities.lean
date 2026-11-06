module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.IdealRatioEquivalence
public import DedekindZetaZeroFree.Arithmetic.Ideals.TracePhaseAnnihilator

@[expose] public section


/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

section
variable (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0)
include m hm a ha
def conductorScaledIdeal_ne_zero
       := mul_ne_zero ha (FractionalIdeal.coeIdeal_ne_zero.mpr hm)

theorem conductorScaledIdeal_le
      :
    a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) ≤ a := by
  simpa only [mul_one] using
    mul_le_mul_right (FractionalIdeal.coeIdeal_le_one (I := m)) a

def traceDualFractionalIdeal_le_conductorScaled
       := (FractionalIdeal.dual_le_dual ℤ ℚ ha
    (conductorScaledIdeal_ne_zero m hm a ha)).mpr (conductorScaledIdeal_le m hm a ha)

theorem traceDualFractionalIdeal_conductorScaled_mul
      :
    traceDualFractionalIdeal (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) *
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) =
        traceDualFractionalIdeal a := by
  unfold traceDualFractionalIdeal
  rw [FractionalIdeal.dual_eq_mul_inv, FractionalIdeal.dual_eq_mul_inv ℤ ℚ a,
    mul_inv, mul_assoc, mul_assoc,
    inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hm), mul_one]

def conductorIdealQuotient_finite
       := fractionalIdealQuotient_finite_of_ratio m hm a _ ha
    (conductorScaledIdeal_le m hm a ha) rfl

def conductorTraceQuotient_finite
       := fractionalIdealQuotient_finite_of_ratio m hm _ _
    (traceDualFractionalIdeal_ne_zero _ (conductorScaledIdeal_ne_zero m hm a ha))
    (traceDualFractionalIdeal_le_conductorScaled m hm a ha)
    (traceDualFractionalIdeal_conductorScaled_mul m hm a ha)

def conductorIdealQuotient_card
       := fractionalIdealQuotient_card_of_ratio m hm a _ ha
    (conductorScaledIdeal_le m hm a ha) rfl

def conductorTraceQuotient_card
       := fractionalIdealQuotient_card_of_ratio m hm _ _
    (traceDualFractionalIdeal_ne_zero _ (conductorScaledIdeal_ne_zero m hm a ha))
    (traceDualFractionalIdeal_le_conductorScaled m hm a ha)
    (traceDualFractionalIdeal_conductorScaled_mul m hm a ha)
end


theorem traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    traceDualFractionalIdeal (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) =
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F := by
  unfold traceDualFractionalIdeal codifferentFractionalIdeal
  rw [FractionalIdeal.dual_eq_mul_inv, mul_comm]
  rfl

end DedekindZetaZeroFree.Hecke

end
