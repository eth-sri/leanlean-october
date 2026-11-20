module
public import DedekindZetaZeroFree.Theta.Profiles.PrincipalIdealCenteredShapeCovariance

public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.RayLatticePeriodization
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitTorsionFibers

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

section

variable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

theorem mixedThetaCovolume_pos :
    0 < DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaCovolume F I := by apply @DedekindZetaZeroFree.Hecke.PrincipalIdealCenteredShapeCovariance.covariance_covolume_pos <;> assumption

def centeredLogShape
    (t : ℝ) (h : RayCoset.logHyperplane F) (v : NumberField.InfinitePlace F) : ℝ :=
  (t / DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaCovolume F I) ^
    ((Module.finrank ℚ F : ℝ)⁻¹) * Real.exp (h.val v)

theorem centeredLogShape_pos
    {t : ℝ} (ht : 0 < t) (h : RayCoset.logHyperplane F)
    (v : NumberField.InfinitePlace F) : 0 < centeredLogShape F I t h v := mul_pos (Real.rpow_pos_of_pos (div_pos ht (mixedThetaCovolume_pos F I)) _)
    (Real.exp_pos _)

def centeredLogIdealTheta
    (t : ℝ) (h : RayCoset.logHyperplane F) : ℂ :=
  if ht : 0 < t then
    DedekindZetaZeroFree.AbelianQuotient.Theta.fractionalShapeIdealTheta F I
      (centeredLogShape F I t h)
      (fun v => ne_of_gt (centeredLogShape_pos F I ht h v))
  else 0

end

def topLogIdealAverage (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) : ℂ :=
  (RayCoset.rayUnitTorsionCard F ⊤ : ℂ)⁻¹ *
    ∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht,
      centeredLogIdealTheta F I t h
      ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F

end DedekindZetaZeroFree.Hecke.Theta

end
