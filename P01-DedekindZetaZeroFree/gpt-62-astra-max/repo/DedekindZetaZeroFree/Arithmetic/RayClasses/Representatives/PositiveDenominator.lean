module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FieldDenominatorIdeal
public import DedekindZetaZeroFree.Arithmetic.Ideals.TotallyPositiveChineseRemainder
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.DenominatorIdealCoprimality

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem positiveRayDenominator
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (x : Kˣ)
    (hx : ClassFieldTheory.IsRayCongruent (narrowIdealModulus K m hm) x) :
    ∃ a d : 𝓞 K, a ≠ 0 ∧ d ≠ 0 ∧
      (a : K) = (d : K) * (x : K) ∧ a - 1 ∈ m ∧ d - 1 ∈ m ∧
      (∀ φ : K →+* ℝ, 0 < φ (a : K)) ∧
      (∀ φ : K →+* ℝ, 0 < φ (d : K)) := by
  obtain ⟨D, hDne, hDmem⟩ := fieldDenominatorIdeal K (x : K)
  obtain ⟨d, hdne, hdD, hdm, hdpos⟩ := positiveIdealCRT K D m hDne hm (rayDenominatorIdealCoprime K m hm x hx D hDmem)
  obtain ⟨a, haeq⟩ := (hDmem d).mp hdD
  have hdK := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hdne
  have haK : (a : K) ≠ 0 := by rw [haeq]; exact mul_ne_zero hdK x.ne_zero
  let du := Units.mk0 (d : K) hdK
  let au := Units.mk0 (a : K) haK
  have heq : du * x = au := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, du, au]
    rw [haeq]
  have hau :=
    heq ▸ (((integralNarrowRayCongruence K m hm d hdK).mpr ⟨hdm, hdpos⟩).mul hx)
  obtain ⟨ham, hapos⟩ := (integralNarrowRayCongruence K m hm a haK).mp hau
  exact ⟨a, d, (NumberField.RingOfIntegers.coe_ne_zero_iff.mp haK), hdne, haeq, ham, hdm, hapos, hdpos⟩

end DedekindZetaZeroFree.AbelianQuotient
