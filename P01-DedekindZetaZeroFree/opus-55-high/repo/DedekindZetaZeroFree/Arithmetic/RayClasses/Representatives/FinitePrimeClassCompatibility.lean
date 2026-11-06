module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescentUniqueness

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

theorem prime_not_mem_fullModulus_support_iff
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    p ∉ (fullModulus f hf).finitePart.support ↔ p.asIdeal ⊔ f = ⊤ := by
  rw [Finsupp.mem_support_iff, fullModulus_finitePart,
    Associates.count_ne_zero_iff_dvd hf p.irreducible, Ideal.dvd_iff_le]
  constructor
  · intro h
    apply (Ideal.isMaximal_def.mp (p.isPrime.isMaximal p.ne_bot)).lt_iff.mp
    simp_all
  · intro h hle
    have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
      simp_all
    exact p.isPrime.ne_top (top_le_iff.mp ht)

theorem idealClass_eq_rayClassOfFinitePrime
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hp : p.asIdeal ⊔ f = ⊤) :
    idealClass f hf p.asIdeal p.ne_bot hp =
      ClassFieldTheory.rayClassOfFinitePrime (fullModulus f hf) p
        ((prime_not_mem_fullModulus_support_iff f hf p).2 hp) := by
  rfl

@[simp] theorem descendedCharacter_apply_finitePrime
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hp : p.asIdeal ⊔ f = ⊤) :
    (descendedCharacter f hf η
      (ClassFieldTheory.rayClassOfFinitePrime (fullModulus f hf) p
        ((prime_not_mem_fullModulus_support_iff f hf p).2 hp)) : ℂ) =
      η p.asIdeal := by
  rw [← idealClass_eq_rayClassOfFinitePrime f hf p hp]
  exact descendedCharacter_apply_idealClass f hf η p.asIdeal p.ne_bot hp
