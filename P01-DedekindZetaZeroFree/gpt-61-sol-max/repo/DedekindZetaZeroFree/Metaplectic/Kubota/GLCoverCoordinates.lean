module

public import Mathlib

public import DedekindZetaZeroFree.Theta.Whittaker.ArithmeticCompletionCoordinates

@[expose] public section


noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.KPReferenceChange.StandardCover
open ThetaActualArithmeticBinding
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : KPPlace F)

abbrev GLCover := KPLocalCover.CubicGL2Raw F ζ hζ (actualPlace v)
abbrev G := KPPGLLocalCover.CubicPGL2 F ζ hζ (actualPlace v)

abbrev topGL  :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ (actualPlace v)
attribute [local instance] topGL

abbrev topG : TopologicalSpace (G F ζ hζ v) := inferInstance
attribute [local instance] topG

abbrev w := KPPGLLocalCover.W F ζ hζ (actualPlace v)









end DedekindZetaZeroFree.KPReferenceChange.StandardCover

end
