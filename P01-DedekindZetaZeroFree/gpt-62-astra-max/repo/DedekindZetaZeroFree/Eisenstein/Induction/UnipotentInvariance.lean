module
public import DedekindZetaZeroFree.Eisenstein.Induction.MetaplecticSectionCovariance
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarRealizationAndCompactFiniteness

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem sqrt_eq_halfPower (r : ℝ) (hr : 0 < r) :
    (Real.sqrt r : ℂ) = KPGlobalExceptionalParameter.realLogPower r (1 / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp]
  unfold KPGlobalExceptionalParameter.realLogPower
  congr 1
  push_cast
  ring
 alias normalized_multiplier := DedekindZetaZeroFree.EisensteinReferenceSections.SeedScalarTransport.normalized_multiplier

def literalSource (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ) :
    KPMsRationalCompactCrossPairing.Source F ζ hζ s := by
  refine ⟨f.val s, ?_⟩
  intro r x g
  have h := (f.property.1 s).2 r x g
  rw [normalized_multiplier] at h
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
    ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s r.val) * f.val s g
  rw [h]
  ring

alias literal_unipotent_invariance := DedekindZetaZeroFree.KPLiteralExceptionalResidue.val_N_invariant
end DedekindZetaZeroFree.KPLiteralChamber

end
