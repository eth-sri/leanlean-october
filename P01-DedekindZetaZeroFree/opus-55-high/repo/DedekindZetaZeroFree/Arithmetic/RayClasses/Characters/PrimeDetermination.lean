module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayCharacterIntegralPrimeReduction
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (χ : DedekindZetaZeroFree.RayClassCharacter K m)
    (H : ClassFieldTheory.NumberFieldFractionalIdealGroup K →* ℂˣ)
    (hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      χ v.asIdeal ≠ 0 →
        (H (ClassFieldTheory.finitePrimeFractionalIdeal v) : ℂ) = χ v.asIdeal) :
    ∀ I : Ideal (𝓞 K), χ I ≠ 0 →
      ∀ J : ClassFieldTheory.NumberFieldFractionalIdealGroup K,
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) →
        (H J : ℂ) = χ I := by
  classical
  let P : Ideal (𝓞 K) → Prop := fun I =>
    χ I ≠ 0 → ∀ J : ClassFieldTheory.NumberFieldFractionalIdealGroup K,
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) →
      (H J : ℂ) = χ I
  have hP : ∀ I, P I := by
    intro I
    refine UniqueFactorizationMonoid.induction_on_prime I ?h0 ?hunit ?hstep
    · intro hzero
      simp
    · intro x hx hxne J hJ
      have hxtop : x = ⊤ := Ideal.isUnit_iff.mp hx
      have hJone : J = 1 := by simp_all
      rw [hJone, map_one, hxtop]
      simp [χ.map_top']
    · intro a p ha0 hp hPa hne J hJ
      rw [χ.map_mul'] at hne
      have hpne : χ p ≠ 0 := by simp_all
      have hane : χ a ≠ 0 := by simp_all
      have hp0 : p ≠ 0 := hp.ne_zero
      have hprime_p : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨p, hprime_p, hp0⟩
      let A : ClassFieldTheory.NumberFieldFractionalIdealGroup K :=
        Units.mk0 (a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr ha0)
      have hAval : (A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
        rfl
      have hJA : J = ClassFieldTheory.finitePrimeFractionalIdeal v * A := by
        apply Units.ext
        rw [Units.val_mul, hAval, hJ, FractionalIdeal.coeIdeal_mul]
        congr 1
      rw [hJA, map_mul, Units.val_mul, hprime v hpne, hPa hane A hAval, χ.map_mul']
  omega
