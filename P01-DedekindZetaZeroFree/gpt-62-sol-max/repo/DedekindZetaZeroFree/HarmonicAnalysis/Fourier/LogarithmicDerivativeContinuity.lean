module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TensorLogarithmicDerivatives

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory NumberField.InfinitePlace
variable {F : Type} [Field F] [NumberField F]

namespace DerivativeContinuityProof
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

local instance (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

open ProbeSheetVerticalDecay (SchwartzTensorWith fourier_tensor_of_local)

abbrev ContinuousSchwartzTensor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  SchwartzTensorWith F S (fun _ g => Continuous g)

private theorem fourier_tensor
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F S) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F S) _ _ (borel _) μ)
    (W : SLocalProduct F S → ℂ)
    (hW : ProbeWeight.IsAnnularTensor F S W) : ContinuousSchwartzTensor F S (ProbeWeight.fourier F S e μ W) := by
  apply fourier_tensor_of_local S e μ hμ W hW
  intro v ν _ f hf hc
  change Continuous (fun y => ∫ x, f x * (e v (-x * y) : ℂ) ∂ν)
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  · intro y
    exact (hf.continuous.mul
      (continuous_subtype_val.comp ((he v).comp
        (continuous_neg.mul continuous_const)))).aestronglyMeasurable
  · intro y
    exact Filter.Eventually.of_forall fun x => by simp [norm_mul]
  · exact (hf.continuous.integrable_of_hasCompactSupport hc).norm
  · exact Filter.Eventually.of_forall fun x =>
      continuous_const.mul (continuous_subtype_val.comp
        ((he v).comp (continuous_const.mul continuous_id)))

private theorem tensor_continuous (A : SArithmeticData F)
    (f : SLocalProduct F A.Sf → ℂ) (hf : ContinuousSchwartzTensor F A.Sf f) :
    Continuous f := by
  obtain ⟨c, gr, gc, gf, hgf, hf⟩ := hf
  have hm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  rw [show f = _ from funext hf]
  apply Continuous.mul continuous_const
  apply Continuous.mul
  · apply Continuous.mul
    · apply continuous_finset_prod
      intro v hv
      exact (gr v).continuous.comp
        ((continuous_apply v).comp (continuous_fst.comp (hm.comp continuous_fst)))
    · apply continuous_finset_prod
      intro v hv
      exact (gc v).continuous.comp
        ((continuous_apply v).comp (continuous_snd.comp (hm.comp continuous_fst)))
  · apply continuous_finset_prod
    intro v hv
    exact (hgf v).comp ((continuous_apply v).comp continuous_snd)

end DerivativeContinuityProof

theorem raw_fourier_log_derivative_continuous
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (w : InfinitePlace F) (k : ℕ)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (_hcompact : HasCompactSupport W0) :
    Continuous (logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)) := by
  exact DerivativeContinuityProof.tensor_continuous A _
    (logDerivative_tensor A w k _
      (DerivativeContinuityProof.fourier_tensor A.Sf e he μ hμ W0 hW0))

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
