module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

 local instance fourierCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

 local instance fourierCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (v : HeightOneSpectrum (𝓞 F))

def localFourierIntegral
    (f : v.adicCompletion F → ℂ) : v.adicCompletion F → ℂ :=
  Fourier.fourierIntegral (localFiniteCharacter F v) (localNormalizedHaar F v) f

theorem localFourierIntegral_apply
    (f : v.adicCompletion F → ℂ) (y : v.adicCompletion F) :
    localFourierIntegral F v f y =
      ∫ x : v.adicCompletion F,
        f x * (localFiniteCharacter F v (-x * y) : ℂ) ∂localNormalizedHaar F v := by
  rw [localFourierIntegral, Fourier.fourierIntegral_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [Circle.smul_def, smul_eq_mul, neg_mul, mul_comm]

@[simp] theorem localFourierIntegral_zero :
    localFourierIntegral F v (0 : v.adicCompletion F → ℂ) = 0 := by
  simpa [localFourierIntegral] using
    Fourier.fourierIntegral_const_smul (localFiniteCharacter F v) (localNormalizedHaar F v)
      (0 : v.adicCompletion F → ℂ) (0 : ℂ)

theorem localFourierIntegral_smul
    (a : ℂ) (f : v.adicCompletion F → ℂ) :
    localFourierIntegral F v (a • f) = a • localFourierIntegral F v f := by
  simpa only [localFourierIntegral] using
    Fourier.fourierIntegral_const_smul (localFiniteCharacter F v) (localNormalizedHaar F v) f a

theorem localFourierIntegral_add
    (f g : v.adicCompletion F → ℂ)
    (hf : f ∈ localSchwartz F v) (hg : g ∈ localSchwartz F v) :
    localFourierIntegral F v (f + g) =
      localFourierIntegral F v f + localFourierIntegral F v g := by
  obtain ⟨h1f, h2f⟩ := hf
  obtain ⟨h1g, h2g⟩ := hg
  simp only [localFourierIntegral]
  exact VectorFourier.fourierIntegral_add (continuous_localFiniteCharacter F v)
    (by simpa using continuous_mul) (h1f.continuous.integrable_of_hasCompactSupport h2f) (h1g.continuous.integrable_of_hasCompactSupport h2g)

theorem localFourierIntegral_finset_sum_smul
    {ι : Type*} (T : Finset ι) (a : ι → ℂ) (f : ι → v.adicCompletion F → ℂ)
    (hf : ∀ i ∈ T, f i ∈ localSchwartz F v) :
    localFourierIntegral F v (∑ i ∈ T, a i • f i) =
      ∑ i ∈ T, a i • localFourierIntegral F v (f i) := by
  classical
  refine Finset.induction_on T ?_ ?_ hf
  · intro _
    simp [localFourierIntegral_zero]
  · intro b T hb ih hf'
    rw [Finset.sum_insert hb]
    rw [localFourierIntegral_add F v (a b • f b) (∑ i ∈ T, a i • f i) ((localSchwartz F v).smul_mem (a b) (hf' b (Finset.mem_insert_self b T))) ((localSchwartz F v).sum_mem fun i hi => (localSchwartz F v).smul_mem (a i)
      (hf' i (Finset.mem_insert_of_mem hi))),
      localFourierIntegral_smul F v (a b) (f b),
      ih fun i hi => hf' i (Finset.mem_insert_of_mem hi)]
    rw [Finset.sum_insert hb]

end DedekindZetaZeroFree

end
