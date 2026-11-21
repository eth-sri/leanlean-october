module

public import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts

@[expose] public section

namespace DedekindZetaZeroFree.ExteriorIdealEuler

open scoped NumberField Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] {cS : Ideal (𝓞 F)}
variable {M : Type*} [MulZeroClass M]

/-- Extend a coefficient by zero on ideals that are not exterior. -/
def extendZero (f : ExteriorIdeal cS → M) (I : Ideal (𝓞 F)) : M :=
  if h : I ≠ ⊥ ∧ I ⊔ cS = ⊤ then f ⟨I, h⟩ else 0

theorem extendZero_mul {f : ExteriorIdeal cS → M}
    (hf : ∀ I J, f (mul I J) = f I * f J) (I J : Ideal (𝓞 F)) :
    extendZero f (I * J) = extendZero f I * extendZero f J := by
  have he : (I * J ≠ ⊥ ∧ I * J ⊔ cS = ⊤) ↔
      (I ≠ ⊥ ∧ I ⊔ cS = ⊤) ∧ (J ≠ ⊥ ∧ J ⊔ cS = ⊤) := by
    change (I * J ≠ 0 ∧ _) ↔ (I ≠ 0 ∧ _) ∧ (J ≠ 0 ∧ _)
    simp only [mul_ne_zero_iff, ← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_left_iff]
    tauto
  unfold extendZero
  by_cases hI : I ≠ ⊥ ∧ I ⊔ cS = ⊤
  · by_cases hJ : J ≠ ⊥ ∧ J ⊔ cS = ⊤
    · rw [dif_pos (he.mpr ⟨hI, hJ⟩), dif_pos hI, dif_pos hJ]
      exact hf ⟨I, hI⟩ ⟨J, hJ⟩
    · rw [dif_neg (hJ ∘ fun h => (he.mp h).2), dif_pos hI, dif_neg hJ, mul_zero]
  · rw [dif_neg (hI ∘ fun h => (he.mp h).1), dif_neg hI, zero_mul]

end

end DedekindZetaZeroFree.ExteriorIdealEuler
