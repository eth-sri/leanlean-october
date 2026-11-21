module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.WeightedCoefficients
public import DedekindZetaZeroFree.Arithmetic.Kummer.SexticFrequencyCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.AllRowEuler.UnitCovariance

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def residueCoefficient (σ : F →+* ℂ) (I : A.Exterior) (u : A.R) : ℂ :=
  A.sexticResiduePowerChar σ I 1 (Ideal.Quotient.mk (A.extendIdeal I) u)

theorem residueCoefficient_eq (I : A.Exterior) (u : A.R) :
    residueCoefficient σ I u = σ (A.sexticResidue I u) := by
  simp only [residueCoefficient, SArithmeticData.sexticResiduePowerChar,
    SArithmeticData.sexticExponent, show (1 : ℤ) % 6 = 1 from rfl,
    Int.toNat_one, pow_one]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) u)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]


end DedekindZetaZeroFree.AllRowEuler.UnitCovariance

end
