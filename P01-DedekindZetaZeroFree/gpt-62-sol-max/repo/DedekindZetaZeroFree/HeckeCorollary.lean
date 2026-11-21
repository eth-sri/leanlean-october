module

public import DedekindZetaZeroFree.Nonvanishing.Hecke.GaloisCharacter
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.RayCharacterGaloisRealization
public import DedekindZetaZeroFree.LFunctions.Hecke.EulerProducts.RayCharacterFiniteCorrection

@[expose] public section

namespace DedekindZetaZeroFree

open scoped NumberField
open AbelianQuotient HeckeCorollary IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

/-- Move the continuation for a character agreeing off the bad primes to the
original modulus by restoring the finite Euler correction. -/
theorem heckeL_ne_zero (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  let S := (narrowIdealModulus K m hm).finitePart.support
  suffices h : ∃ (m₀ : Ideal (𝓞 K)) (χ₀ : RayClassCharacter K m₀) (f : ℂ → ℂ),
      m₀ ≠ ⊥ ∧ (∀ P ∉ S, χ P.asIdeal = χ₀ P.asIdeal) ∧
      DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧ (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I => χ₀ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 by
    obtain ⟨m₀, χ₀, f, hm₀, hagree, hf, hdiff, hsum, hnz⟩ := h
    have hc := finiteEulerCorrection_differentiable K χ₀ S
    refine ⟨_, hf.mul hc.differentiableOn, fun h => (hdiff h).mul hc, ?_, ?_⟩
    · intro s hs
      have h := (weightedIdealSummability K χ χ.map_mul' χ.map_top'
        ((χ.eq_zero_iff' ⊥).mpr (Or.inl rfl)) (rayCharacter_norm_le_one K m hm χ) s hs).of_norm.hasSum
      rw [rayCharacter_eulerCorrection K m m₀ hm hm₀ χ χ₀ S
        (rayCharacter_eq_zero_of_mem_modulus_support K m hm χ) hagree s hs, (hsum s hs).tsum_eq] at h
      exact h
    · intro s hs hreg
      exact mul_ne_zero (hnz s hs hreg) (finiteEulerCorrection_ne_zero K χ₀
        (rayCharacter_norm_le_one K m₀ hm₀ χ₀) S s (by linarith))
  by_cases hχ : χ.IsPrincipal
  · obtain ⟨f, hf, hseries, hnz⟩ := dedekindZeta_ne_zero K
    refine ⟨⊤, trivialRayCharacter K, f, top_ne_bot, ?_, hf, fun h => (h hχ).elim, ?_, ?_⟩
    · intro p hp
      have hcoprime : p.asIdeal ⊔ m = ⊤ := by
        by_contra hne
        have hnone := rayIdealClass_eq_none K m hm p.asIdeal (Or.inr hne)
        rw [rayIdealClass_of_finitePrime K m hm p hp] at hnone
        contradiction
      simp [hχ p.asIdeal p.ne_bot hcoprime, trivialRayCharacter_apply, p.ne_bot]
    · intro s hs
      rw [hseries s hs]
      apply (Odlyzko.hasSum_idealInverseNormPower K hs).congr_fun
      intro I
      by_cases hI : I = ⊥
      · simp [trivialRayCharacter_apply, hI, Odlyzko.idealInverseNormPower]
      · simp [trivialRayCharacter_apply, hI, Odlyzko.idealInverseNormPower_of_ne_zero K s hI]
    · exact fun s hs h => hnz s hs (h.resolve_right (not_not.mpr hχ))
  · obtain ⟨R, ρ, hρ, hρprime⟩ := exists_rayCharacter_galoisRealization K m hm χ
    obtain ⟨m₀, χ₀, f, hm₀, _, hprime, hf, hsum, hnz⟩ :=
      galoisCharacter_ne_zero K R.extension ρ (fun h => hχ (hρ.mp h))
    refine ⟨m₀, χ₀, f, hm₀, ?_, hf.differentiableOn, fun _ => hf, hsum, fun s hs _ => hnz s hs⟩
    intro p hp
    obtain ⟨Q⟩ := Ideal.nonempty_primesOver (R := 𝓞 K) (S := 𝓞 R.extension) p.asIdeal
    let W : HeightOneSpectrum (𝓞 R.extension) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩
    exact (hρprime p hp W Q.2.2).trans (hprime p W Q.2.2).symm

end DedekindZetaZeroFree
