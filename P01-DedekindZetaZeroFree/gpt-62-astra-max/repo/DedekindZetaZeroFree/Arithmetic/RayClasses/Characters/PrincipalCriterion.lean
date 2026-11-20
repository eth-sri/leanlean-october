module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupHomExtFinitePrime

@[expose] public section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayCharacterPrincipalCriterion
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m)
    (ψ : RayIdealClass K m hm →* ℂ)
    (h : ∀ I : Ideal (𝓞 K), χ I =
      match rayIdealClass K m hm I with
      | none => 0
      | some c => ψ c) :
    χ.IsPrincipal ↔ ψ = 1 := by
  constructor
  · intro hχ
    let μ := narrowIdealModulus K m hm
    have key : ψ.toHomUnits = (1 : RayIdealClass K m hm →* ℂˣ) := by
      apply ClassFieldTheory.rayClassGroup_hom_ext_finitePrime K μ
      intro v hv
      have hv' := hv
      apply Units.ext
      rw [MonoidHom.coe_toHomUnits]
      show ψ (ClassFieldTheory.rayClassOfFinitePrime μ v hv) = 1
      have hnot : ¬ m ≤ v.asIdeal := by
        intro hle
        apply hv'
        rw [Finsupp.mem_support_iff, narrowIdealModulus_finitePart]
        exact Multiset.count_ne_zero.mpr
          ((Ideal.mem_normalizedFactors_iff hm).mpr ⟨v.isPrime, hle⟩)
      have hcoprime : v.asIdeal ⊔ m = ⊤ := by
        by_contra hne
        exact hnot ((v.isMaximal.eq_of_le hne le_sup_left) ▸ le_sup_right)
      have hd := h v.asIdeal
      rw [(hχ v.asIdeal v.ne_bot hcoprime), (rayIdealClass_of_finitePrime K m hm v hv')] at hd
      exact hd.symm
    apply MonoidHom.ext
    intro c
    have h1 : ψ.toHomUnits c = 1 := by simp [key]
    rw [← MonoidHom.coe_toHomUnits ψ c, h1]
    simp
  · intro hψ I hI hcoprime
    rw [h I, rayIdealClass_eq_some K m hm I hI hcoprime]
    simp [hψ]

end DedekindZetaZeroFree.AbelianQuotient
