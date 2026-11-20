module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.ExtensionConductorCharacter
public import DedekindZetaZeroFree.Arithmetic.Ideals.MultiplicativeCharacterPrimeAgreement

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField Classical
open IsDedekindDomain

theorem conductor_frobenius_agreement
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) (d : QuadraticRayExtensionData η)
    (c : ClassFieldTheory.RayClassModulus F)
    (hc : ClassFieldTheory.IsAbelianConductor F d.extension c) :
    let g := finiteModulusIdeal c
    ∀ θ : DedekindZetaZeroFree.RayClassCharacter F g,
      (∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ⊔ g = ⊤ →
        ∀ Q : HeightOneSpectrum (𝓞 d.extension),
          Q.asIdeal.LiesOver p.asIdeal →
            θ p.asIdeal =
              (d.character (ClassFieldTheory.arithmeticFrobeniusAt (K := F) Q) : ℂ)) →
      ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (f * g) = ⊤ → η I = θ I := by
  classical
  intro g θ hθ I hI hIcop
  have hg := finiteModulusIdeal_ne_bot c

  have hprime : ∀ p : HeightOneSpectrum (𝓞 F),
      p.asIdeal ⊔ (f * g) = ⊤ → η p.asIdeal = θ p.asIdeal := by
    intro p hp
    obtain ⟨Q, hQmax, hQlies⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 d.extension) p.asIdeal
    have hQne : Q ≠ ⊥ := by
      intro hbot
      have h1 : Q.under (𝓞 F) = ⊥ := by
        rw [hbot]
        exact Ideal.under_bot (𝓞 F) (𝓞 d.extension)
      exact p.ne_bot (by rw [hQlies.over, h1])
    let Q' : HeightOneSpectrum (𝓞 d.extension) := ⟨Q, hQmax.isPrime, hQne⟩
    have hlies' := hQlies
    refine (d.frobenius p ?_ Q' hlies').symm.trans (hθ p ?_ Q' hlies').symm
    · refine le_antisymm le_top ?_
      calc _ = p.asIdeal ⊔ f * g := hp.symm
        _ ≤ p.asIdeal ⊔ f := sup_le_sup_left Ideal.mul_le_left _
    · refine le_antisymm le_top ?_
      calc _ = p.asIdeal ⊔ f * g := hp.symm
        _ ≤ p.asIdeal ⊔ g := sup_le_sup_left Ideal.mul_le_right _
  exact prime_agreement hf hg
    (fun h => (Ideal.mul_eq_bot.mp h).elim hf hg)
    η θ hprime I hI hIcop

end DedekindZetaZeroFree.LargeSieve.RootNumber
