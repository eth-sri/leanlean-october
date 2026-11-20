module
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.BruhatTwoCellIntegral

public import DedekindZetaZeroFree.Eisenstein.Induction.MetaplecticSectionCovariance
public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem rationalLift_eq_constructed (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    rationalLift F ζ hζ γ =
      (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting F ζ hζ).lift γ := by
  have h := (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting F ζ hζ).on_matrix
    (Quotient.out γ)
  change _ = _ at h
  have he : Matrix.ProjGenLinGroup.mk (Quotient.out γ) = γ := Quotient.out_eq γ
  rw [he] at h
  exact h.symm

theorem rationalLift_mul (a b : Matrix.ProjGenLinGroup (Fin 2) F) :
    rationalLift F ζ hζ (a * b) = rationalLift F ζ hζ a * rationalLift F ζ hζ b := by
  simp only [rationalLift_eq_constructed, map_mul]

theorem rationalLift_diagonal (y : Fˣ) :
    rationalLift F ζ hζ
      (Matrix.ProjGenLinGroup.mk (KPGlobalTorusFunctionData.rationalDiagonal F y)) =
      (KPGlobalTorusFunctionData.s F ζ hζ y).val := by
  rw [rationalLift_eq_constructed]
  rfl

theorem rationalLift_unipotent (t : F) :
    rationalLift F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F t) =
      KPGlobalTorusFunctionData.N F ζ hζ
        (algebraMap F (KPGlobalTorusFunctionData.Adeles F) t) := by
  rw [rationalLift_eq_constructed]
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (KPRationalAdelicSplitting.N_rational F ζ hζ t).symm

theorem val_rational_diagonal_invariant (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (y : Fˣ) (g : G F ζ hζ) :
    f.val s ((KPGlobalTorusFunctionData.s F ζ hζ y).val * g) = f.val s g := by
  let r := KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y
  have h := (f.property.1 s).2 r 0 g
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hchar := KPGlobalCenterRationalCharacter.lambdaR_rational F ζ hζ y r rfl
  rw [hchar] at h
  simpa only [r, KPGlobalTorusPeriodizationInverse.rationalLift, hN, mul_one,
    KPGlobalTorusBorelTwistCompatibility.delta_rational, Units.val_one, NNReal.coe_one,
    KPGlobalExceptionalParameter.realLogPower, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul] using h

private alias upper_matrix_factorization := DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.BruhatTwoCellIntegral.upper_matrix_factorization

theorem val_rational_borel_invariant (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ)
    (b : KPChamberBruhatTwoCells.rationalBorel F) (g : G F ζ hζ) :
    f.val s (rationalLift F ζ hζ b.val * g) = f.val s g := by
  obtain ⟨B, hB, he⟩ := b.property
  obtain ⟨y, t, ht⟩ := upper_matrix_factorization F ⟨B, hB⟩
  rw [← he, ht, rationalLift_mul, rationalLift_diagonal, rationalLift_unipotent, mul_assoc]
  rw [val_rational_diagonal_invariant, val_N_invariant]

theorem literal_scalar_rational_borel_invariant (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) :
    KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F
      (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting F ζ hζ).lift
      (f.val s) := by
  intro b g
  rw [← rationalLift_eq_constructed]
  exact val_rational_borel_invariant F ζ hζ K f s b g

theorem val_rationalCoset_out_eq (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ)
    (a : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ) :
    f.val s (rationalLift F ζ hζ
      (Quotient.out (KPChamberBruhatTwoCells.rationalCoset F a)) * g) =
      f.val s (rationalLift F ζ hζ a * g) := by
  simp only [rationalLift_eq_constructed]
  exact KPChamberBruhatTwoCells.rationalTerm_eq F _ (f.val s)
    (literal_scalar_rational_borel_invariant F ζ hζ K f s) g a

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end

section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 abbrev rational :=
  (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting F ζ hζ).lift

private alias section_unipotent_invariant := DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.section_unipotent_invariant

private theorem rational_unipotent (t : F) :
    rational F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F t) =
      KPGlobalTorusFunctionData.Nhom F ζ hζ
        (Multiplicative.ofAdd (algebraMap F (KPGlobalTorusFunctionData.Adeles F) t)) := by apply @DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational_unipotent <;> assumption

 theorem compatible_unipotent :
    KPChamberBruhatTwoCells.CompatibleUnipotentLift F (rational F ζ hζ)
      (KPGlobalTorusFunctionData.Nhom F ζ hζ) := rational_unipotent F ζ hζ

private theorem unsigned_weyl :
    rational F ζ hζ (Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap F)) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) := by apply @DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.unsigned_weyl <;> assumption

private theorem section_rational_diagonal_invariant (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (y : Fˣ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    v.val ((KPGlobalTorusFunctionData.s F ζ hζ y).val * g) = v.val g := by
  let t : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
    KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y
  have h := v.property t 0 g
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hchar : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character t : ℂ) = 1 := by
    change ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
      (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y) *
      KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (KPGlobalTorusFunctionData.s F ζ hζ y)) : ℂ) = 1
    rw [(KPGlobalTorusPeriodizationInverse.rational_representative_character F ζ hζ y),
      KPGlobalTorusBorelTwistCompatibility.normCharacter_rational]
    simp
  rw [hchar] at h
  simpa only [t, KPGlobalTorusPeriodizationInverse.rationalLift, hN, mul_one,
    KPGlobalTorusFunctionData.deltaHalf,
    KPGlobalTorusBorelTwistCompatibility.delta_rational, Units.val_one,
    NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, hchar, one_mul] using h

 theorem section_signed_weyl (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    v.val (rational F ζ hζ (KPChamberBruhatTwoCells.rationalWeyl F) * g) =
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * g) := by apply @DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.section_signed_weyl <;> assumption

private alias upper_matrix_factorization := DedekindZetaZeroFree.KPLiteralExceptionalResidue.upper_matrix_factorization

 theorem scalar_rational_borel_invariant (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s) :
    KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F (rational F ζ hζ) v.val := by apply @DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.scalar_rational_borel_invariant <;> assumption

end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual

end
end
