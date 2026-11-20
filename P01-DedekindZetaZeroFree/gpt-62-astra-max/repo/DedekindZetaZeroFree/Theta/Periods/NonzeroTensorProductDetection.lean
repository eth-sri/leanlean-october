module

public import DedekindZetaZeroFree.Theta.Periods.RankOne.ComplexSliceSpans
public import DedekindZetaZeroFree.Theta.Periods.RankOne.FiniteSliceSpans
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.ExteriorSphericalVectors
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.HarishChandraHeckeGeneration
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.LocalAndSU2Actions
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.NonzeroTraceDetection
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.ScalarCore

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end DedekindZetaZeroFree.ThetaExpansion

section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_period_factorization
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (JointRealizedFlatSources R N)) :
    Nonempty (JointHaarFactorizedSources R N) := by
  obtain ⟨D⟩ := tensorLocalLines_nonempty R hR N (tensorFiniteLines_nonempty R hR N (tensorSpherical_nonempty R hR N (tensorDetected_nonempty R hR N (tensorActions_nonempty R hR N (tensorHC_nonempty R hR N (tensorSeed_nonempty R hR N prior))))))
  exact ⟨FourierContinuation.jointHaarFactorizedSources_of_factorization D.toJointRealizedFlatSources D.factorization⟩
end DedekindZetaZeroFree.ThetaExpansion

end
