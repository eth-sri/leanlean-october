module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.ChamberHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.NormOneTorus
public import DedekindZetaZeroFree.Metaplectic.Torus.NormOneEvaluationAlgebra

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators NNReal ENNReal
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField MeasureTheory KPGlobalTorusFiniteStages KPLiteralRaw KPAdelicCoverRestrictedProduct
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open KPGlobalTorusPeriodizationInverse hiding productModel
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem integrable_idele_mul (a : (KPGlobalTorusFunctionData.Adeles F)ˣ)
    (f : KPGlobalTorusFunctionData.Adeles F → ℂ) :
    Integrable (fun x => f (x * a.val)) (KPAdditiveHaar.adelicMeasure F) ↔
      Integrable f (KPAdditiveHaar.adelicMeasure F) := by
  let μ := KPAdditiveHaar.adelicMeasure F
  let e := ContinuousAddEquiv.mulLeft a
  let := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let : μ.Regular := inferInstance
  have he : Integrable f (Measure.map e μ) ↔ Integrable (f ∘ e) μ :=
    e.toHomeomorph.measurableEmbedding.integrable_map_iff
  have hi : Integrable f μ ↔ Integrable f (Measure.map e μ) := by
    nth_rw 1 [← (addEquivAddHaarChar_smul_map μ e)]
    exact integrable_smul_measure (by exact_mod_cast (addEquivAddHaarChar_pos e).ne') ENNReal.coe_ne_top
  rw [hi, he]
  simp only [μ, e, Function.comp_def, ContinuousAddEquiv.mulLeft_apply, mul_comm]

theorem coreFlatFiber_chamber_shift (x : Core) (z : ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1)
    (y : KPGlobalTorusFunctionData.Adeles F) :
    (coreFlatInsertion R P C x).val z
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y *
        NormOneTorusAlgebra.rightEvaluation F ζ hζ e) =
      (coreFlatFiber R P C x z (CofactorChamber.chamberRaw F ζ hζ
        (y * (KPGlobalTorusFunctionData.p F ζ hζ
          (KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ e))⁻¹.val))).val.val e := by
  rw [coreFlatFiber_chamber_normOne_value R P C x z _ e hδ]
  apply congrArg ((coreFlatInsertion R P C x).val z)
  simpa only [mul_one, KPRationalAdelicSplitting.pglW, KPCubicCoverConstruction.adelicW] using NormOneTorusAlgebra.chamber_rightEvaluation F ζ hζ e y 1

theorem coreFlatFiber_chamber_integrable (x : Core) (z : ℂ) (hz : (1/3 : ℝ) < z.re)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1) :
    Integrable (fun y : KPGlobalTorusFunctionData.Adeles F =>
      (coreFlatFiber R P C x z (CofactorChamber.chamberRaw F ζ hζ y)).val.val e)
      (KPAdditiveHaar.adelicMeasure F) := by
  exact (integrable_idele_mul (KPGlobalTorusFunctionData.p F ζ hζ
    (KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ e))⁻¹ _).mp ((coreScattering_integrable R P C x z hz (NormOneTorusAlgebra.rightEvaluation F ζ hζ e)).congr (Filter.Eventually.of_forall (coreFlatFiber_chamber_shift R P C x z e hδ)))

theorem coreFlatFiber_chamber_integral (x : Core) (z : ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1) :
    coreScattering R P C x z (NormOneTorusAlgebra.rightEvaluation F ζ hζ e) =
      ∫ y : KPGlobalTorusFunctionData.Adeles F,
        (coreFlatFiber R P C x z (CofactorChamber.chamberRaw F ζ hζ y)).val.val e
        ∂KPAdditiveHaar.adelicMeasure F := by
  let := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  unfold coreScattering
  simp_rw [coreFlatFiber_chamber_shift R P C x z e hδ]
  rw [KPGlobalResidualKernel.ScatteringResidue.idele_integral_mul_inv
    (KPAdditiveHaar.adelicMeasure F)
    (KPGlobalTorusFunctionData.p F ζ hζ (KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ e))
    (fun y => (coreFlatFiber R P C x z (CofactorChamber.chamberRaw F ζ hζ y)).val.val e),
    NormOneTorusAlgebra.rightEvaluation_abs F ζ hζ e hδ]
  simp

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
