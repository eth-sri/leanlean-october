module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.UnitFractionalIdealResidueEquivalence

@[expose] public section


noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

section
variable (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J)
include m hm I J hI hJI hratio
def idealRatioResidueEquiv
       := (FractionalIdeal.quotientEquiv I J 1
    (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (by simpa using hratio) hJI (residueFractionalIdeal_le_one m)
    ((residueFractionalIdeal_ne_zero_iff m).2 hm) hI).trans
    (residueFractionalOneEquiv m).symm

theorem fractionalIdealQuotient_finite_of_ratio
      :
    Finite (fractionalIdealQuotient I J) := by
  letI  :=
    m.finiteQuotientOfFreeOfNeBot hm
  exact Finite.of_equiv (NumberField.RingOfIntegers F ⧸ m)
    (idealRatioResidueEquiv m hm I J hI hJI hratio).symm.toEquiv

theorem fractionalIdealQuotient_card_of_ratio
      :
    Nat.card (fractionalIdealQuotient I J) = Ideal.absNorm m := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (idealRatioResidueEquiv m hm I J hI hJI hratio).toEquiv
end


end DedekindZetaZeroFree.Hecke

end
