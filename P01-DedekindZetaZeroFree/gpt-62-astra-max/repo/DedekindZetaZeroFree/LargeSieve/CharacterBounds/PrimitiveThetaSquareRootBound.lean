module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SmoothThetaAndGramKernels
public import DedekindZetaZeroFree.Theta.Profiles.AnnularTransformIdealMass
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.NonprincipalHeckeSummation

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical ContDiff

noncomputable section

private lemma finsum_subtype_ne_bot {F : Type} [Field F] [NumberField F]
    (g : Ideal (𝓞 F) → ℂ) :
    (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥}, g I.val)
      = ∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else g I := by
  rw [finsum_subtype_eq_finsum_cond]
  apply finsum_congr
  intro I
  rw [finsum_eq_if]
  by_cases hI : I = ⊥ <;> simp [hI]

theorem initial_primitive_sqrt_bound (F : Type) [Field F] [NumberField F]
    (hTC : NumberField.IsTotallyComplex F)
     :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Ideal (𝓞 F), f ≠ ⊥ →
      ∀ η : DedekindZetaZeroFree.RayClassCharacter F f,
        η.IsPrimitive → ¬ η.IsPrincipal →
        ∀ X : ℝ, 0 < X →
          ‖initialTheta F (fun I => η I) X‖ ≤ A * Real.sqrt (Ideal.absNorm f : ℝ) := by
  classical
  obtain ⟨B, hB0, hB⟩ := initial_annular_transform_mass F hTC
  refine ⟨B, hB0, ?_⟩
  intro f hf η hprim hnonprincipal X hX
  have hq : 0 < (Ideal.absNorm f : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by
      simpa [Ideal.absNorm_eq_zero_iff] using hf)
  set h : ℝ → ℂ := fun x => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ) with hh
  have hh_cd : ContDiff ℝ ∞ h := by
    rw [hh]
    exact Complex.ofRealCLM.contDiff.comp DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_contDiff
  have hh_cs : HasCompactSupport h := by
    rw [hh]
    exact DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_hasCompactSupport.comp_left
      (g := fun x : ℝ => (x : ℂ)) (by simp)
  obtain ⟨W, hW, hPoisson⟩ :=
    DedekindZetaZeroFree.LargeSieve.nonprincipalPoisson F hTC f hf η hprim hnonprincipal
  obtain ⟨hSnorm, hSsum, hEq⟩ := hPoisson h hh_cd hh_cs X hX
  have hLHS : (∑ᶠ I : Ideal (𝓞 F), DedekindZetaZeroFree.LargeSieve.idealMellinWeight η.toFun h X I)
      = initialTheta F (fun I => η I) X := by
    rw [initialTheta_eq_finsum F (fun I => η I) hX]
    rw [finsum_subtype_ne_bot (g := fun I : Ideal (𝓞 F) =>
      (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight (Ideal.absNorm I / X) : ℂ) * η I)]
    apply finsum_congr
    intro I
    by_cases hI : I = ⊥
    · simp [DedekindZetaZeroFree.LargeSieve.idealMellinWeight, hI]
    · simp only [hI, ↓reduceIte, DedekindZetaZeroFree.LargeSieve.idealMellinWeight, if_false, hh]
      ring
  have harg : ∀ I : Ideal (𝓞 F),
      X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm f : ℝ)
        = (Ideal.absNorm I : ℝ) / ((Ideal.absNorm f : ℝ) / X) := by
    intro I
    field_simp
  have hv : ∀ I : Ideal (𝓞 F), ‖(starRingEnd ℂ) (η I)‖ ≤ 1 := by
    intro I
    rw [starRingEnd_apply, norm_star]
    exact DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η I
  have hdual_bound :
      (∑' I : Ideal (𝓞 F), ‖if I = ⊥ then 0
        else (starRingEnd ℂ) (η I) *
          DedekindZetaZeroFree.LargeSieve.fieldTransform ((|NumberField.discr F| : ℤ) : ℝ)
            (NumberField.InfinitePlace.nrComplexPlaces F) h
            (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm f : ℝ))‖)
        ≤ B * ((Ideal.absNorm f : ℝ) / X) := by
    refine (le_of_eq ?_).trans (hB ((Ideal.absNorm f : ℝ) / X) (div_pos hq hX)
      (fun I : Ideal (𝓞 F) => (starRingEnd ℂ) (η I)) hv).2.2
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥
    · simp [hI]
    · simp only [hI, ↓reduceIte]
      rw [harg I]
  have hcoef : ‖W * (X : ℂ) / (Real.sqrt (Ideal.absNorm f : ℝ) : ℂ)‖
      = X / Real.sqrt (Ideal.absNorm f : ℝ) := by
    rw [norm_div, norm_mul, hW, one_mul]
    simp [RCLike.norm_ofReal, abs_of_nonneg hX.le, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc _
      = ‖(W * (X : ℂ) / (Real.sqrt (Ideal.absNorm f : ℝ) : ℂ)) *
          ∑' I : Ideal (𝓞 F), (if I = ⊥ then 0
            else (starRingEnd ℂ) (η I) *
              DedekindZetaZeroFree.LargeSieve.fieldTransform ((|NumberField.discr F| : ℤ) : ℝ)
                (NumberField.InfinitePlace.nrComplexPlaces F) h
                (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm f : ℝ)))‖ := by
        rw [← hLHS, hEq]
    _ = ‖W * (X : ℂ) / (Real.sqrt (Ideal.absNorm f : ℝ) : ℂ)‖ *
          ‖∑' I : Ideal (𝓞 F), (if I = ⊥ then 0
            else (starRingEnd ℂ) (η I) *
              DedekindZetaZeroFree.LargeSieve.fieldTransform ((|NumberField.discr F| : ℤ) : ℝ)
                (NumberField.InfinitePlace.nrComplexPlaces F) h
                (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm f : ℝ)))‖ := norm_mul _ _
    _ = (X / Real.sqrt (Ideal.absNorm f : ℝ)) *
          ‖∑' I : Ideal (𝓞 F), (if I = ⊥ then 0
            else (starRingEnd ℂ) (η I) *
              DedekindZetaZeroFree.LargeSieve.fieldTransform ((|NumberField.discr F| : ℤ) : ℝ)
                (NumberField.InfinitePlace.nrComplexPlaces F) h
                (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm f : ℝ)))‖ := by rw [hcoef]
    _ ≤ (X / Real.sqrt (Ideal.absNorm f : ℝ)) * (B * ((Ideal.absNorm f : ℝ) / X)) :=
        mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hSnorm).trans hdual_bound) (by positivity)
    _ = B * Real.sqrt (Ideal.absNorm f : ℝ) := by
        field_simp
        nlinarith [(Real.sq_sqrt hq.le)]

end

end DedekindZetaZeroFree.LargeSieve.Sieve
