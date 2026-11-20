module

public import ClassFieldTheory.Definitions.All
public import ClassFieldTheory.Theorems.All
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.RayClassBridge

 theorem modulus_support_finite
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) :
    (Function.support (fun v : HeightOneSpectrum (𝓞 F) =>
      Int.toNat (FractionalIdeal.count F v
        (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)))).Finite := by
  have hf := FractionalIdeal.finite_factors
    (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  rw [Filter.eventually_cofinite] at hf
  exact hf.subset (fun v hv hz => hv (by simp [hz]))

section

variable (F : Type) [Field F] [NumberField F]

def narrowIdealModulus
    (𝔪 : Ideal (𝓞 F)) (_h𝔪 : 𝔪 ≠ ⊥) : ClassFieldTheory.RayClassModulus F where
  finitePart := Finsupp.ofSupportFinite
    (fun v => Int.toNat (FractionalIdeal.count F v
      (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)))
    (modulus_support_finite F 𝔪)
  infinitePart := Finset.univ

def integralUnit
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

@[simp] theorem integralUnit_val
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (integralUnit F I hI : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = I := rfl

end

section

variable (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)

@[simp] theorem narrowIdealModulus_finitePart (v : HeightOneSpectrum (𝓞 F)) :
    (narrowIdealModulus F 𝔪 h𝔪).finitePart v =
      Int.toNat (FractionalIdeal.count F v
        (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := rfl

@[simp] theorem narrowIdealModulus_infinitePart :
    (narrowIdealModulus F 𝔪 h𝔪).infinitePart = Finset.univ := rfl

theorem narrowIdealModulus_support :
    (↑(narrowIdealModulus F 𝔪 h𝔪).finitePart.support : Set (HeightOneSpectrum (𝓞 F))) =
      {v | 𝔪 ≤ v.asIdeal} := by
  ext v
  rw [Finset.mem_coe, Finsupp.mem_support_iff, narrowIdealModulus_finitePart,
    Set.mem_setOf_eq]
  rw [ne_eq, Int.toNat_eq_zero, not_le,
    FractionalIdeal.count_coe F v h𝔪, Int.natCast_pos,
    Nat.pos_iff_ne_zero, Associates.count_ne_zero_iff_dvd h𝔪 v.irreducible, Ideal.dvd_iff_le]

private theorem mem_finitePart_support_iff (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support ↔ 𝔪 ≤ v.asIdeal := by
  rw [← Finset.mem_coe, narrowIdealModulus_support, Set.mem_setOf_eq]

end

@[simp] theorem narrowIdealModulus_top_finitePart
    (F : Type) [Field F] [NumberField F] (h : (⊤ : Ideal (𝓞 F)) ≠ ⊥) :
    (narrowIdealModulus F ⊤ h).finitePart = 0 := by
  ext v
  rw [narrowIdealModulus_finitePart, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
  rfl

section

variable (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥)

theorem integralUnit_mem_primeTo_iff :
    integralUnit F I hI ∈ ClassFieldTheory.rayClassPrimeToIdeals
      (narrowIdealModulus F 𝔪 h𝔪) ↔ I ⊔ 𝔪 = ⊤ := by
  simp only [ClassFieldTheory.rayClassPrimeToIdeals, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (I ⊔ 𝔪) hne
    have hne_bot : I ⊔ 𝔪 ≠ ⊥ := fun hb =>
      hI (le_bot_iff.mp (hb ▸ le_sup_left))
    have hpne : p ≠ ⊥ := fun hb => hne_bot (le_bot_iff.mp (hb ▸ hle))
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp.isPrime, hpne⟩
    have hcount := h v ((mem_finitePart_support_iff F 𝔪 h𝔪 v).mpr (le_trans le_sup_right hle))
    rw [integralUnit_val, FractionalIdeal.count_coe F v hI, Int.natCast_eq_zero] at hcount
    have hnd := fun hd =>
      ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mpr hd) hcount
    rw [Ideal.dvd_iff_le] at hnd
    exact hnd (le_trans le_sup_left hle)
  · intro hcop v hv
    rw [integralUnit_val]
    by_contra hc
    rw [FractionalIdeal.count_coe F v hI, Int.natCast_eq_zero] at hc
    have hdvd := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc
    rw [Ideal.dvd_iff_le] at hdvd
    exact Ideal.IsMaximal.ne_top inferInstance (top_le_iff.mp (hcop ▸ sup_le hdvd ((mem_finitePart_support_iff F 𝔪 h𝔪 v).mp hv)))

def integralPrimeTo (hcop : I ⊔ 𝔪 = ⊤) :
    ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) :=
  ⟨integralUnit F I hI, (integralUnit_mem_primeTo_iff F 𝔪 h𝔪 I hI).mpr hcop⟩

def integralRayClass (hcop : I ⊔ 𝔪 = ⊤) :
    ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪) :=
  QuotientGroup.mk (integralPrimeTo F 𝔪 h𝔪 I hI hcop)

end

variable (F : Type) [Field F] [NumberField F]

@[simp] theorem integralUnit_top (h : (⊤ : Ideal (𝓞 F)) ≠ ⊥) :
    integralUnit F ⊤ h = 1 := by
  ext
  simp [integralUnit]

theorem integralUnit_mul
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    integralUnit F (I * J) hIJ = integralUnit F I hI * integralUnit F J hJ := by
  ext
  simp [integralUnit, FractionalIdeal.coeIdeal_mul]

end DedekindZetaZeroFree.RayClassBridge

end
