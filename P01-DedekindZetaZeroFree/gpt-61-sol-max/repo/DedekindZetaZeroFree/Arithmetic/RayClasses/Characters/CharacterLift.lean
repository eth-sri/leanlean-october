module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ProductConductorComparison

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve.Sieve.Initial

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]

section
variable {f m : Ideal (𝓞 F)} (hfm : f ∣ m)
    (ψ : RayClassCharacter F f)
include f m hfm ψ
noncomputable def liftCharacter   : RayClassCharacter F m where
  toFun I := if I ⊔ m = ⊤ then ψ I else 0
  map_mul' := fun I J => by
    have hcop : I * J ⊔ m = ⊤ ↔ I ⊔ m = ⊤ ∧ J ⊔ m = ⊤ := by
      constructor
      · intro h
        exact ⟨top_unique (le_trans (le_of_eq h.symm)
            (sup_le_sup_right (Ideal.mul_le_left (I := I) (J := J)) m)),
          top_unique (le_trans (le_of_eq h.symm)
            (sup_le_sup_right (Ideal.mul_le_right (I := I) (J := J)) m))⟩
      · rintro ⟨hI, hJ⟩
        rw [Ideal.mul_sup_eq_of_coprime_left hI, hJ]
    by_cases hI : I ⊔ m = ⊤
    · by_cases hJ : J ⊔ m = ⊤
      · simp only [hcop, hI, hJ, and_self, ↓reduceIte, ψ.map_mul' I J]
      · have hIJ : I * J ⊔ m ≠ ⊤ := by simpa [hcop, hI] using hJ
        simp [hIJ, hI, hJ]
    · have hIJ : I * J ⊔ m ≠ ⊤ := by
        intro h
        apply hI <;> aesop
      simp [hIJ, hI]
  map_top' := by simp [ψ.map_top']
  eq_zero_iff' := fun I => by
    by_cases hIm : I ⊔ m = ⊤
    · have hIf : I ⊔ f = ⊤ := by
        have hmf  := Ideal.dvd_iff_le.mp hfm
        exact top_unique (le_trans (le_of_eq hIm.symm) (sup_le_sup_left hmf I))
      simp only [hIm, if_pos, not_true_eq_false, or_false]
      simpa [ψ.eq_zero_iff' I, hIf]
    · simp [hIm]
  map_span' := fun α hα hmem hpos => by
    have hcop : Ideal.span {α} ⊔ m = ⊤ := by
      apply (Ideal.eq_top_iff_one _).mpr
      have ha  := Ideal.mem_span_singleton_self α
      exact (Submodule.mem_sup.mpr ⟨α, ha, 1 - α, by
        simpa only [neg_sub] using m.neg_mem hmem, by ring⟩)
    simp [hcop, ψ.map_span' α hα (Ideal.dvd_iff_le.mp hfm hmem) hpos]

@[simp] theorem liftCharacter_apply   (I : Ideal (𝓞 F)) :
    liftCharacter hfm ψ I = if I ⊔ m = ⊤ then ψ I else 0 := rfl

theorem liftCharacter_apply_of_coprime   (I : Ideal (𝓞 F)) (hIm : I ⊔ m = ⊤) :
    liftCharacter hfm ψ I = ψ I := by
  rw [liftCharacter_apply, if_pos hIm]
end










end DedekindZetaZeroFree.LargeSieve.Sieve.Initial
