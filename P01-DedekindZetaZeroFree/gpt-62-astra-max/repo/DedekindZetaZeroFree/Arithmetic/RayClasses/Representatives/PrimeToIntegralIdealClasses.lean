module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

section

variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤)

def idealToPrimeTo :
    ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) :=
  ⟨integralIdealUnit I hI, by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv
    rw [fullModulus_finitePart] at hv
    have hI0 : I ≠ 0 := by exact hI
    have hcoe : ((integralIdealUnit I hI :
        ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        I := rfl
    rw [hcoe, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
    by_contra hne
    refine v.isPrime.ne_top (top_le_iff.mp ?_)
    rw [← hcop]
    exact sup_le (Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne)) (Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd (by exact hm) v.irreducible).mp hv))⟩

def idealClass :
    ClassFieldTheory.RayClassGroup (fullModulus m hm) :=
  QuotientGroup.mk'
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus m hm))
    (idealToPrimeTo m hm I hI hcop)

@[simp] theorem idealToPrimeTo_coe :
    (idealToPrimeTo m hm I hI hcop :
      ClassFieldTheory.NumberFieldFractionalIdealGroup F) = integralIdealUnit I hI :=
  rfl

end

theorem ideal_mul_ne_bot (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ

theorem ideal_mul_coprime (m I J : Ideal (𝓞 F))
    (hIm : I ⊔ m = ⊤) (hJm : J ⊔ m = ⊤) :
    (I * J) ⊔ m = ⊤ := by
  rw [sup_comm]
  exact by
    rw [Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact hIm), sup_comm, hJm]

section

variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)

@[simp] theorem idealToPrimeTo_top :
    idealToPrimeTo m hm ⊤ (by exact top_ne_bot) (by simp) = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_one, idealToPrimeTo_coe]
  apply Units.ext
  show ((⊤ : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1
  apply FractionalIdeal.coeIdeal_top

@[simp] theorem idealClass_top :
    idealClass m hm ⊤ (by exact top_ne_bot) (by simp) = 1 := by
  simp [idealClass]

end

variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIm : I ⊔ m = ⊤)
    (hJm : J ⊔ m = ⊤) (hIJ : I * J ≠ ⊥) (hIJm : (I * J) ⊔ m = ⊤)

@[simp] theorem idealToPrimeTo_mul :
    idealToPrimeTo m hm (I * J) hIJ hIJm =
      idealToPrimeTo m hm I hI hIm * idealToPrimeTo m hm J hJ hJm := by
  solve_by_elim [integralIdealUnit_mul, Subtype.ext]

@[simp] theorem idealClass_mul :
    idealClass m hm (I * J) hIJ hIJm =
      idealClass m hm I hI hIm * idealClass m hm J hJ hJm := by
  simp_all [idealClass]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
