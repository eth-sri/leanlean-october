module
public import DedekindZetaZeroFree.Theta.Periods.WeightedQuotientIntegrability

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitSheetMajorants
public import DedekindZetaZeroFree.Theta.Periods.RationalPeriodContinuity
public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderLocalRegularity
public import DedekindZetaZeroFree.Adeles.Quotients.PGLContinuity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

private alias sixthPowers_measurable := DedekindZetaZeroFree.DigitMasks.WeightedQuotientIntegrability.sixthPowers_measurable

private alias class_measurableSingleton := DedekindZetaZeroFree.DigitMasks.WeightedQuotientIntegrability.class_measurableSingleton

theorem classMask_measurable : Measurable (fun y : R.A.G =>
    if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then (1 : ℂ) else 0) := by
  letI := class_measurableSingleton R.A
  letI := R.A.V_finite
  exact (measurable_of_finite (fun q : R.A.V =>
    if q ∈ R.probe.correction.B then (1 : ℂ) else 0)).comp
      (measurable_quotient_mk'')

private theorem correctionLS_continuous :
    Continuous (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
      R.probe.correction.η_id) := by
  unfold SArithmeticData.correctionLS SArithmeticData.ideleSInverseProduct
  have hθ := SArithmeticData.CorrectionAssembly.correctionTheta_continuous R.A
    R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id
    R.probe.correction.Λ_continuous R.probe.correction.G_continuous
    R.probe.correction.eta_continuous
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w hw
    exact (hθ.comp ((SArithmeticData.CorrectionTopology.infinite_embedding_continuous w).comp
      ((continuous_apply w).comp continuous_fst))).inv
  · apply continuous_finset_prod
    intro v hv
    exact (hθ.comp ((SArithmeticData.CorrectionTopology.finite_embedding_continuous v.val).comp
      ((continuous_apply v).comp continuous_snd))).inv

alias branch_measurable := DedekindZetaZeroFree.DigitMasks.branch_measurable

def sheetMultiplier {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹

theorem sheetMultiplier_measurable {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) : Measurable (sheetMultiplier R P v) :=
  (classMask_measurable R).mul (branch_measurable R P v).inv

theorem sheetMultiplier_norm_le {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ‖sheetMultiplier R P v y‖ ≤ 1 := by
  unfold sheetMultiplier
  split_ifs <;> simp [branch_norm_one R P]

alias localIdele_continuous := DedekindZetaZeroFree.DigitMasks.localIdele_selected_continuous

alias signedArgument_continuous := DedekindZetaZeroFree.DigitMasks.signedArgument_continuous

theorem orbitSheet_measurable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) : Measurable (orbitSheet R C v m b i l) := by
  have hd : Measurable (fun z : Sheet R.A l =>
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)) := by
    apply Finset.measurable_sum
    intro d hd
    exact measurable_const.mul (((orbitFrequencyValue_continuous R C.realization v i).comp
      ((signedArgument_continuous R m b d).comp continuous_subtype_val)).measurable)
  convert ((sheetMultiplier_measurable R C.packet v).comp measurable_subtype_coe).mul hd using 1
  rfl

end DedekindZetaZeroFree.OrbitExpansion

end
