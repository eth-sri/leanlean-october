module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.LocalFields.RootsOfUnityAndPowerClasses
public import ClassFieldTheory.All

@[expose] public section


open scoped NumberField Classical
open NumberField IsDedekindDomain
open LocalFieldTheory.DiscreteValuationField

namespace DedekindZetaZeroFree
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false






namespace SArithmeticData
variable {F : Type} [Field F] [NumberField F]

section
variable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
include F v
abbrev finiteCompletionLocalField   :=
  LocalField.ofWithZeroValuation
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))

abbrev finiteCompletionResidueChar    :=
  (finiteCompletionLocalField F v).residueCharacteristic

def finiteCompletionDegree    :=
  let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  letI : LocalField.MixedWithZeroValuationContext ν :=
    LocalField.mixedWithZeroValuationContext ν
  letI : Valued (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.mk' ν
  Module.finrank ℚ_[finiteCompletionResidueChar F v] (v.adicCompletion F)
end


private lemma isLocalRootOrder_of_hn {n : ℕ+} (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) :
    IsLocalRootOrder (n : ℕ) := by
  rcases hn with h | h <;> simp [IsLocalRootOrder, h]

private lemma primitiveRoots_nonempty (A : SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) :
    (primitiveRoots (n : ℕ) F).Nonempty :=
  ⟨A.zeta12 ^ (12 / (n : ℕ)),
    (mem_primitiveRoots n.pos).2 (A.primitive_root (n : ℕ) (isLocalRootOrder_of_hn hn))⟩

private def residueChar_prime (v : HeightOneSpectrum (𝓞 F))  :=
  (finiteCompletionLocalField F v).residueCharacteristic_prime

section
variable (A : SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) (v : HeightOneSpectrum (𝓞 F))
include A n hn v
private lemma card_powerClass_eq   :
    Nat.card (ClassFieldTheory.PowerClassGroup (v.adicCompletion F) n) =
      (n : ℕ) * ((n : ℕ) *
        finiteCompletionResidueChar F v ^
          (finiteCompletionDegree F v *
            padicValNat (finiteCompletionResidueChar F v) (n : ℕ))) := by
  have hcard := GlobalClassFieldTheory.ClassFieldAxiom.card_finitePlace_nthPowerQuotient
    (K := F) n (primitiveRoots_nonempty A n hn) v
  exact hcard

theorem finite_power_class_finite   (hv : v ∈ A.Sf) :
    Finite (ClassFieldTheory.PowerClassGroup (v.adicCompletion F) n) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_powerClass_eq A n hn v]
  exact Nat.mul_ne_zero n.ne_zero
    (Nat.mul_ne_zero n.ne_zero (pow_ne_zero _ (residueChar_prime v).ne_zero))
end


end SArithmeticData
end
end DedekindZetaZeroFree
