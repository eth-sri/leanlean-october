module

public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

def classGroupTwoTorsion : Subgroup (ClassGroup (𝓞 K)) :=
  (powMonoidHom 2).ker

def classGroupTwoTorsionCard : ℕ := Nat.card (classGroupTwoTorsion K)

lemma classGroupTwoTorsionCard_le_classNumber :
    classGroupTwoTorsionCard K ≤ NumberField.classNumber K := by
  classical
  simpa [classGroupTwoTorsionCard, NumberField.classNumber, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective
      (fun c : classGroupTwoTorsion K => (c : ClassGroup (𝓞 K))) Subtype.val_injective

end
end CCDN
