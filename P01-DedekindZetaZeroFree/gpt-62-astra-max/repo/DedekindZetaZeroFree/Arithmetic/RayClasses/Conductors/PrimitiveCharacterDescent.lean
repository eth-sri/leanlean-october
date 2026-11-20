module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.CharacterModulusDescent
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.InductionAndPrincipality

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical
open DedekindZetaZeroFree

theorem initial_ray_primitive_descent
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m) :
    ∃ f : Ideal (𝓞 F), f ≠ ⊥ ∧ f ∣ m ∧
      ∃ η0 : RayClassCharacter F f, η0.IsPrimitive ∧
        (∀ I : Ideal (𝓞 F), η I = if I = ⊥ ∨ I ⊔ m ≠ ⊤ then 0 else η0 I) ∧
        (η.IsPrincipal ↔ η0.IsPrincipal) := by
  classical

  let P := fun f =>
    ∃ θ : RayClassCharacter F f, ∀ I : Ideal (𝓞 F),
      η I = if I = ⊥ ∨ I ⊔ m ≠ ⊤ then 0 else θ I

  have hmP : P m := ⟨η, fun I => by
    by_cases h : I = ⊥ ∨ I ⊔ m ≠ ⊤
    · rw [if_pos h]
      exact (RayOperations.eq_zero_iff η I).mpr h
    · rw [if_neg h]⟩
  obtain ⟨f, hfS, hfmax⟩ := Finset.exists_maximal (⟨m, Finset.mem_filter.mpr ⟨((mem_idealDivisors hm).mpr dvd_rfl), hmP⟩⟩)
  obtain ⟨hfm_mem, hfP⟩ := Finset.mem_filter.mp hfS
  have hfm := (mem_idealDivisors hm).mp hfm_mem
  have hfne := ne_bot_of_mem_idealDivisors hfm_mem
  obtain ⟨θ, hθ⟩ := hfP

  have hprim : θ.IsPrimitive := by
    intro g hfg
    by_contra hno
    have hfg_le := le_of_lt hfg
    have htriv : ∀ a : 𝓞 F, a ≠ 0 → a - 1 ∈ g →
        (∀ φ : F →+* ℝ, 0 < φ (a : F)) →
        Ideal.span {a} ⊔ f = ⊤ → θ (Ideal.span {a}) = 1 := by
      intro a ha hmem hpos hcop
      by_contra hne
      exact hno ⟨a, ha, hmem, hpos, hcop, hne⟩
    obtain ⟨θg, hθg⟩ :=
      initial_ray_one_step_descent F f g hfne (fun hg => hfne (le_bot_iff.mp (hg ▸ hfg_le))) hfg_le θ htriv

    have hgP : P g := ⟨θg, fun I => by
      by_cases hcond : I = ⊥ ∨ I ⊔ m ≠ ⊤
      · rw [if_pos hcond]
        exact (RayOperations.eq_zero_iff η I).mpr hcond
      · have hIcop : I ⊔ m = ⊤ := by
          by_contra h; exact hcond (Or.inr h)
        have hcond' : ¬ (I = ⊥ ∨ I ⊔ f ≠ ⊤) := by
          rintro (h | h)
          · exact (fun h => hcond (Or.inl h)) h
          · exact h (top_unique (le_trans (le_of_eq hIcop.symm) (sup_le_sup_left (Ideal.dvd_iff_le.mp hfm) I)))
        rw [if_neg hcond, hθ I, if_neg hcond, hθg I, if_neg hcond']⟩
    exact hfg.2 (hfmax (Finset.mem_filter.mpr ⟨(mem_idealDivisors hm).mpr (dvd_trans (Ideal.dvd_iff_le.mpr hfg_le) hfm), hgP⟩) hfg_le)
  exact ⟨f, hfne, hfm, θ, hprim, hθ,
    initial_ray_principal_descent_equiv hm hfne hfm η θ hθ⟩

end DedekindZetaZeroFree.LargeSieve
