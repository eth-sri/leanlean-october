module

public import GS.Shared.FactorCoordinates
public import GS.OverlapGeometry.HorizontalModel

@[expose] public section


/-!
# Horizontal coordinates for an actual shared orbit

The complement and its continuous ambient left inverse reuse the general
finite-dimensional constructions.  The differential is the actual derivative
of the shared factor map.  The carrier P need not be unitary.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.OverlapGeometry (horizontalComplement complementKernelEquiv horizontalLeftInverse
  horizontalLeftInverse_apply)
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

section
variable (right left : Pattern 𝕜 n) (P : 𝕄)
/-- The actual differential of the original factor parametrization. -/
def orbitDerivative :
    PairGenerator right left →L[ℝ] 𝕄 :=
  fderiv ℝ (orbitParam (1 : Factors right left) P) 0

abbrev OrbitKernel :=
  LinearMap.ker (orbitDerivative right left P).toLinearMap

abbrev HorizontalModel :=
  horizontalComplement (orbitDerivative right left P)

def horizontalKernelEquiv :
    (HorizontalModel right left P × OrbitKernel right left P) ≃L[ℝ] PairGenerator right left :=
  complementKernelEquiv (orbitDerivative right left P)

def orbitHorizontalInverse :
    𝕄 →L[ℝ] HorizontalModel right left P :=
  horizontalLeftInverse (orbitDerivative right left P)


end

end GS.Shared
