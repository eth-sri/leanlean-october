module

public import Mathlib

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.RayParityKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RayParityTensorTransform
public import DedekindZetaZeroFree.LFunctions.Hecke.ParityReciprocalGammaFactors
public import DedekindZetaZeroFree.Theta.Unfolding.RayParityProductMellin

@[expose] public section


noncomputable section

open Classical NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.FourierMellin

variable (K : Type) [Field K] [NumberField K]

theorem fourier (δ : Finset (RayCoset.RealPlaces K)) :
    FourierTransform.fourier (gδ K δ) = fun x ↦ εδ K δ * gδ K δ x := by
  funext x
  apply fourier_gδ

alias mellinFactor_mul_reciprocalGamma := _root_.DedekindZetaZeroFree.AbelianQuotient.RayParity.κδ_mul_hδ

end DedekindZetaZeroFree.AbelianQuotient.RayParity.FourierMellin

end
