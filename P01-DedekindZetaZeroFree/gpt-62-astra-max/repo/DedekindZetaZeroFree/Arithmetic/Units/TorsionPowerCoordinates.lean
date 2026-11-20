module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.All

@[expose] public section

namespace DedekindZetaZeroFree.SArithmeticData

variable {F : Type} [Field F] [NumberField F] (A : DedekindZetaZeroFree.SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) ∣ 12)

include A hn in
theorem primitive_roots_of_dvd_twelve :
    (primitiveRoots (n : ℕ) F).Nonempty := ⟨A.zeta12 ^ (12 / (n : ℕ)), (mem_primitiveRoots n.pos).2
    (A.primitive_zeta12.pow (by decide) (Nat.div_mul_cancel hn).symm)⟩

noncomputable def torsionPowerQuotientEquiv :
    (NumberField.Units.torsion F ⧸
      (powMonoidHom (n : ℕ) :
        NumberField.Units.torsion F →* NumberField.Units.torsion F).range) ≃*
      Multiplicative (ZMod (n : ℕ)) := KummerTheory.numberFieldTorsionNthPowerQuotientEquivZMod n
    (A.primitive_roots_of_dvd_twelve n hn)

end DedekindZetaZeroFree.SArithmeticData
