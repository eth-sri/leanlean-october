module

public import DedekindZetaZeroFree.Theta.Profiles.ReflectedOrbitSmoothing
public import DedekindZetaZeroFree.Theta.Periods.RationalDilation
public import DedekindZetaZeroFree.Moments.Reflected.FrequencyTerm

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

def groupedOrbitTerm {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ThetaReflectionData.Frequency R.A) : ℂ :=
  ∑' γ : ThetaReflectionData.rationalGamma R.A, orbitTerm R C v m b Z hZ (ξ, γ)

theorem orbit_fiber_norm_summable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z)
    (ξ : ThetaReflectionData.Frequency R.A) :
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A =>
      ‖orbitTerm R C v m b Z hZ (ξ, γ)‖) :=
  ((hx v m b Z hZ).2.2.1).prod_factor ξ

theorem groupedOrbitTerm_norm_summable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun ξ => ‖groupedOrbitTerm R C v m b Z hZ ξ‖) := by
  exact ((hx v m b Z hZ).2.2.1).prod.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ =>
    norm_tsum_le_tsum_norm (orbit_fiber_norm_summable R C hx v m b Z hZ ξ))

theorem groupedOrbitTerm_hasSum {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z) :
    HasSum (groupedOrbitTerm R C v m b Z hZ)
      (∑' i : OrbitIndex R, orbitTerm R C v m b Z hZ i) := by
  convert (groupedOrbitTerm_norm_summable R C hx v m b Z hZ).of_norm.hasSum using 1
  exact ((hx v m b Z hZ).2.2.1).of_norm.tsum_prod

theorem reverse_orbit_evaluation_of_fiber_identity {N : TraceHaarTransport R}
    (C : JointUpperVanishingSources R N) (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z)
    (heval : ∀ ξ, actualReflectedTerm R C v m Z ξ =
      groupedOrbitTerm R C v m false Z hZ ξ) :
    Summable (fun ξ => ‖actualReflectedTerm R C v m Z ξ‖) ∧
      HasSum (actualReflectedTerm R C v m Z)
        (∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i) := by
  rw [(funext heval)]
  exact ⟨groupedOrbitTerm_norm_summable R C hx v m false Z hZ,
    groupedOrbitTerm_hasSum R C hx v m false Z hZ⟩

theorem exterior_sheet_smoothing {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (Z : ℝ) (hZ : 0 < Z) :
    (∫ t : PositiveAxis, C.packet.kernel t.val *
      (exteriorDigitCoefficient R C m (Quotient.out ξ) * (Characters.L R v (Quotient.out ξ))⁻¹ *
        C.realization.sheet C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
          (q R.A (Quotient.out ξ) / ⟨t.val / Z, div_pos t.property hZ⟩)) ∂positiveHaar) =
      actualReflectedTerm R C v m Z ξ := by
  have hi := reverse_sheet_smoothing R C v ξ Z hZ
  have he (t : PositiveAxis) : C.packet.kernel t.val *
      (exteriorDigitCoefficient R C m (Quotient.out ξ) * (Characters.L R v (Quotient.out ξ))⁻¹ *
        C.realization.sheet C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
          (q R.A (Quotient.out ξ) / ⟨t.val / Z, div_pos t.property hZ⟩)) =
      (exteriorDigitCoefficient R C m (Quotient.out ξ) * (Characters.L R v (Quotient.out ξ))⁻¹) *
        (C.packet.kernel t.val * C.realization.sheet C.packet v
          (ThetaReflectionData.frequencyClass R.A ξ)
          ⟨Z * ThetaReflectionData.frequencyNorm R.A ξ / t.val,
            div_pos (mul_pos hZ (ThetaReflectionData.frequencyNorm_pos R.A ξ)) t.property⟩) := by
    rw [reflected_scale R ξ Z hZ t]
    ring
  simp_rw [he]
  exact by rw [integral_const_mul, hi.2]; rfl

end DedekindZetaZeroFree.OrbitExpansion

end
