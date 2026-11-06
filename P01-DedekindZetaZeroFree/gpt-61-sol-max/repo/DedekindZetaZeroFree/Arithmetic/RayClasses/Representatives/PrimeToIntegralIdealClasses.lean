module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup

@[expose] public section


noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

section
variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤)
include m hm I hI hcop
def idealToPrimeTo   :
    ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) :=
  ⟨integralIdealUnit I hI, by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv
    rw [fullModulus_finitePart] at hv
    have hm0 : m ≠ 0 := hm
    have hI0 : I ≠ 0 := hI
    have hle_m  :=
      Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hm0 v.irreducible).mp hv)
    have hcoe : ((integralIdealUnit I hI :
        ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := rfl
    rw [hcoe, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
    by_contra hne
    have hle_I  :=
      Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne)
    have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rw [← hcop]
      exact sup_le hle_I hle_m
    exact v.isPrime.ne_top (top_le_iff.mp htop)⟩

def idealClass   :
    ClassFieldTheory.RayClassGroup (fullModulus m hm) :=
  QuotientGroup.mk'
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus m hm))
    (idealToPrimeTo m hm I hI hcop)

@[simp] theorem idealToPrimeTo_coe   :
    (idealToPrimeTo m hm I hI hcop :
      ClassFieldTheory.NumberFieldFractionalIdealGroup F) = integralIdealUnit I hI :=
  rfl
end


theorem ideal_mul_ne_bot (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := by
  intro h
  exact (Ideal.mul_eq_bot.mp h).elim hI hJ

theorem ideal_mul_coprime (m I J : Ideal (𝓞 F))
    (hIm : I ⊔ m = ⊤) (hJm : J ⊔ m = ⊤) :
    (I * J) ⊔ m = ⊤ := by
  have hcomm : m ⊔ I = ⊤ := by rw [sup_comm]; exact hIm
  have h : m ⊔ I * J = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left hcomm, sup_comm, hJm]
  rw [sup_comm]
  exact h

@[simp] theorem idealToPrimeTo_top (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    idealToPrimeTo m hm ⊤ (top_ne_bot) (by simp) = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_one, idealToPrimeTo_coe]
  apply Units.ext
  show ((⊤ : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1
  apply FractionalIdeal.coeIdeal_top

@[simp] theorem idealClass_top (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    idealClass m hm ⊤ (top_ne_bot) (by simp) = 1 := by
  rw [idealClass, idealToPrimeTo_top, map_one]

section
variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIm : I ⊔ m = ⊤) (hJm : J ⊔ m = ⊤)
    (hIJ : I * J ≠ ⊥) (hIJm : (I * J) ⊔ m = ⊤)
include m hm I J hI hJ hIm hJm hIJ hIJm
@[simp] theorem idealToPrimeTo_mul   :
    idealToPrimeTo m hm (I * J) hIJ hIJm =
      idealToPrimeTo m hm I hI hIm * idealToPrimeTo m hm J hJ hJm := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, idealToPrimeTo_coe]
  apply integralIdealUnit_mul

@[simp] theorem idealClass_mul   :
    idealClass m hm (I * J) hIJ hIJm =
      idealClass m hm I hI hIm * idealClass m hm J hJ hJm := by
  rw [idealClass, idealClass, idealClass, idealToPrimeTo_mul, map_mul]
end


end DedekindZetaZeroFree.LargeSieve.RayBridge

end
