module

public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.LocalCovariance
public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.CovariantExtension
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LocalEvaluations
public import DedekindZetaZeroFree.Theta.Periods.RepeatedCorePeriod
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.Injectivity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)






















































end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
