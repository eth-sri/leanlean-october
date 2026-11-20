module

public import NearlyMinimax.HigherBandRows
public import NearlyMinimax.HighUnionSource


@[expose] public section

/-! Original source primitive legality for each actual higher-target
cardinal/cardinal-band row. The selected family supplies positive actual
variation; all law, centering, Borel, and reset facts are derived. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def higherBandSourceRow {d : ℕ} (C : ModelConstants d) (k r m D q : ℕ)
    (M Cfr lam L T : ℝ) (fine : Bool) :
    HighUnionRowData d k D Unit (fun _ => HigherBandRowMark d r m D q fine) :=
  higherBandRowData d k r m D q (C.densityLower+1/M) (C.densityUpper-1/M) Cfr lam L T fine

/-- Every actual selected positive-mass higher-band row satisfies the
source's primitive probability, reset, and mean-one balancing inputs. -/
theorem higherBandSourceRow_guards {d : ℕ} (C : ModelConstants d)
    (k r m D q : ℕ) (hr : 1 ≤ r) (M Cfr lam L T : ℝ) (fine : Bool)
    (hM : highCenterResolutionThreshold C ≤ M) (hCfr : 1 ≤ Cfr) (hT : 1 ≤ T)
    (hpos : 0 < higherBandRowMass d r m D q (C.densityLower+1/M)
      (C.densityUpper-1/M) Cfr lam L T fine) :
    HighUnionSourceGuards C M Cfr (higherBandSourceRow C k r m D q M Cfr lam L T fine) := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  refine highPacketRowData_guards C M hM k m r D q hr Cfr hCfr _ _
    (higherBandCarrierAmplitude_integrable d r D lam L T hT fine) hpos
    (fun j ζ x l => higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x)) ?_ ?_
  · intro j l
    exact (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  · intro j ζ x l
    exact higherBandCarrierFactor_bound d r lam fine ζ l _ (fun i =>
      (highLocalCoordinates_abs_le_one d k j x i).trans (by norm_num))


end NearlyMinimax
