module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualIdeal

@[expose] public section


/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

def traceDualFractionalIdeal
    (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)  :=
  FractionalIdeal.dual ℤ ℚ I

def codifferentFractionalIdeal (F : Type) [Field F] [NumberField F]  :=
  traceDualFractionalIdeal (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)

section
variable (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
include I J
@[reducible] def fractionalIdealQuotient
      :=
  I.coeToSubmodule ⧸ J.coeToSubmodule.comap I.coeToSubmodule.subtype

def fractionalIdealQuotientMk
      :
    I.coeToSubmodule →ₗ[NumberField.RingOfIntegers F] fractionalIdealQuotient I J :=
  (J.coeToSubmodule.comap I.coeToSubmodule.subtype).mkQ












@[simp] theorem fractionalIdealQuotientMk_smul
     
    (a : NumberField.RingOfIntegers F) (x : I.coeToSubmodule) :
    fractionalIdealQuotientMk I J (a • x) = a • fractionalIdealQuotientMk I J x := rfl

theorem fractionalIdealQuotientMk_surjective
      :
    Function.Surjective (fractionalIdealQuotientMk I J) := by
  intro y
  exact Submodule.mkQ_surjective _ y

@[simp] theorem fractionalIdealQuotientMk_eq_zero_iff
      (x : I.coeToSubmodule) :
    fractionalIdealQuotientMk I J x = 0 ↔ (x : F) ∈ J := by
  rw [fractionalIdealQuotientMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  rfl
end


end DedekindZetaZeroFree.Hecke

end
