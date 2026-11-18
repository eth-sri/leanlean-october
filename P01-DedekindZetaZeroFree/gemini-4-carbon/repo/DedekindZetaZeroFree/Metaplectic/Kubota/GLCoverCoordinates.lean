module

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

abbrev topGL : TopologicalSpace (GLCover F ζ hζ v) :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ (actualPlace v)
attribute [local instance] topGL

abbrev topG : TopologicalSpace (G F ζ hζ v) := inferInstance
attribute [local instance] topG

abbrev w := KPPGLLocalCover.W F ζ hζ (actualPlace v)

instance topGroupG : IsTopologicalGroup (G F ζ hζ v) := by
  cases v with
  | inl p =>
    let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ p
    have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ p
    exact (KPPGLLocalCover.finite_topological_cover F ζ hζ p m hm).2.2.1
  | inr w => exact (KPPGLLocalCover.complex_topological_cover F ζ hζ w).2.2.1

end DedekindZetaZeroFree.KPReferenceChange.StandardCover

end
