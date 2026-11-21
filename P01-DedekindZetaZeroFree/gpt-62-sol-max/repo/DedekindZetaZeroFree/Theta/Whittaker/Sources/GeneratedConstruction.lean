module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LocalEvaluations
public import DedekindZetaZeroFree.Theta.Whittaker.Sources.FaithfulConstruction

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
set_option maxHeartbeats 250000
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

def generatedFromInitialPlus (N : TraceHaarTransport R) (hC : C.exceptional = R.A.Sf)
    (u : ∀ j : bad R.A P C, Plus R.A P C j.val)
    (D : NonDegenerate.PeriodSource R N)
    (hD : ∀ v, D.realization.theta v = coreResidue R P C (initialPlusCore R P C u)) :
    NonDegenerate.Generated R N :=
  HCGeneration.faithfulGeneratedOfNativeSlots
    (faithfulFromInitialPlus R P C μ hμ N hC u D hD)
    (actualCoreResidue_native_slots R P C μ hμ N)

include μ hμ in
theorem exists_generated_from_initial_plus
    (hR : RootAligned R) (N : TraceHaarTransport R) (hC : C.exceptional = R.A.Sf)
    (u : ∀ j : bad R.A P C, Plus R.A P C j.val)
    (hspherical : InitialPlusSpherical R P C u)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C (initialPlusCore R P C u)) 1 ≠ 0) :
    Nonempty (NonDegenerate.Generated R N) := by
  obtain ⟨D, hD, _⟩ := exists_repeated_core_period_source R P C hR N
    (initialPlusCore R P C u) hspherical hx
  exact ⟨generatedFromInitialPlus R P C μ hμ N hC u D hD⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
