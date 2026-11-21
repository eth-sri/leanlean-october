module

public import DedekindZetaZeroFree.Theta.Profiles.FourierRootCovariance
public import DedekindZetaZeroFree.Theta.Periods.UpperCurveDifferentiation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem fourier_upper_translation (dq : Measure (KPAdditiveQuotient F))
    (hHaar : dq.IsAddHaarMeasure) (f : Functions R)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (g : Group R) :
    MomentSources.fourier R dq f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      (adelicTraceCharacter F x : ℂ) * MomentSources.fourier R dq f g := by
  letI := hHaar
  exact MomentSources.fourier_left_root R dq f
    (fun t g => by rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]; exact hr _ _) x g

theorem diagonal_upper (y : KPAdelicCoverRestrictedProduct.Ideles F) (x : KPAdeles F) :
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12 y *
      KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 x =
    KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 ((y : KPAdeles F) * x) *
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12 y := by
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
    ((y : KPAdeles F) * x) y
  have he : (y : KPAdeles F) * x * (↑y⁻¹ : KPAdeles F) = x := by
    rw [mul_comm (y : KPAdeles F) x, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [he] at h
  exact h.symm

end DedekindZetaZeroFree.RootDerivatives

end
