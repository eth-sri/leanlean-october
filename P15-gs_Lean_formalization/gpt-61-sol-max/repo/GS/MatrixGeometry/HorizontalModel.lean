import GS.MatrixGeometry.Base

import GS.MatrixGeometry.FactorCoordinates
import GS.OverlapGeometry.HorizontalModel

open GS.MatrixBase


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
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]

variable (right left : Pattern 𝕜 n)

variable (P : KMat 𝕜 n)

/-- The actual differential of the original factor parametrization. -/
def orbitDerivative   :
    PairGenerator right left →L[ℝ] KMat 𝕜 n :=
  fderiv ℝ (orbitParam (1 : Factors right left) P) 0

abbrev OrbitKernel   :=
  LinearMap.ker (orbitDerivative right left P).toLinearMap

abbrev HorizontalModel   :=
  horizontalComplement (orbitDerivative right left P)

def horizontalKernelEquiv := complementKernelEquiv (orbitDerivative right left P)

def orbitHorizontalInverse := horizontalLeftInverse (orbitDerivative right left P)



end GS.MatrixGeometry
