module

public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.RootAndTorusCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem localValue_reference_one (p : KPHilbert.Place F) (hp : p ∉ bad R P C) :
    localValue R N P C p 1 (plusReference R N P C p) = reference R P C p := by
  cases p with
  | inl w => exact False.elim (hp (arch_bad R P C w))
  | inr q =>
    change (plusReference R N P C (Sum.inr q)).val
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) 1) = _
    rw [map_one]
    exact plusReference_one R N P C q hp

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
