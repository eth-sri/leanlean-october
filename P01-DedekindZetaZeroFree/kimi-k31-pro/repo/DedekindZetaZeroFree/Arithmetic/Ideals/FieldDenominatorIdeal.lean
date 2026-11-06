module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

def fieldDenomIdeal (K : Type) [Field K] [NumberField K] (y : K) : Ideal (𝓞 K) where
  carrier := {d | ∃ a : 𝓞 K, (a : K) = (d : K) * y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro d₁ d₂ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
    refine ⟨a₁ + a₂, ?_⟩
    grind
  smul_mem' := by
    rintro c d ⟨a, h⟩
    refine ⟨c * a, ?_⟩
    simp only [smul_eq_mul, map_mul]
    grind

theorem fieldDenominatorIdeal
    (K : Type) [Field K] [NumberField K] (y : K) :
    ∃ D : Ideal (𝓞 K), D ≠ ⊥ ∧
      ∀ d : 𝓞 K, d ∈ D ↔ ∃ a : 𝓞 K, (a : K) = (d : K) * y := by
  refine ⟨fieldDenomIdeal K y, ?_, fun d => Iff.rfl⟩
  rw [Submodule.ne_bot_iff]
  by_cases hy : y = 0
  · refine ⟨1, ⟨0, ?_⟩, one_ne_zero⟩
    grind
  · obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) y
    exact ⟨d, ⟨n, by grind⟩, mem_nonZeroDivisors_iff_ne_zero.mp d.2⟩

end DedekindZetaZeroFree.AbelianQuotient
