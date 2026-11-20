module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CoprimeInverseRepresentatives
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOperations

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

variable {F : Type} [Field F] [NumberField F]

theorem rayCharacter_eq_of_eq_away {m q : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hq : q ≠ ⊥)
    (η θ : DedekindZetaZeroFree.RayClassCharacter F m)
    (h : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (m * q) = ⊤ → η I = θ I) :
    ∀ I : Ideal (𝓞 F), η I = θ I := by
  intro I
  by_cases hI : I = ⊥
  · rw [(η.eq_zero_iff' I).mpr (Or.inl hI), (θ.eq_zero_iff' I).mpr (Or.inl hI)]
  by_cases hIm : I ⊔ m = ⊤
  ·
    obtain ⟨J, a, hJ0, hJcop, ha0, ha1, hpos, hIJ⟩ :=
      exists_ray_inverse_coprime F m q I hm hq hI hIm

    have eη : η I * η J = 1 := by
      rw [← RayOperations.map_mul η I J, hIJ, (η.map_span' a ha0 ha1 hpos)]
    have eθ : θ I * θ J = 1 := by
      rw [← RayOperations.map_mul θ I J, hIJ, (θ.map_span' a ha0 ha1 hpos)]
    have key : η I * η J = θ I * η J := by
      rw [eη, (h J hJ0 hJcop), eθ]
    exact mul_right_cancel₀ (fun hz =>
      (η.eq_zero_iff' J).mp hz |>.elim hJ0 (fun hc => hc (le_antisymm le_top
        (le_trans (le_of_eq hJcop.symm) (sup_le_sup_left Ideal.mul_le_left J))))) key
  ·
    rw [(η.eq_zero_iff' I).mpr (Or.inr hIm), (θ.eq_zero_iff' I).mpr (Or.inr hIm)]

end DedekindZetaZeroFree.LargeSieve
