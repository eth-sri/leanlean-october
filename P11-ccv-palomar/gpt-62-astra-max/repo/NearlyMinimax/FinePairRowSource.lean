module

public import NearlyMinimax.FinePairRowNondegenerate
public import NearlyMinimax.HighUnionSource


@[expose] public section

/-! Concrete source guards for all three actual fine-pair rows. No row-law,
mean-zero, positive variation or reset legality premise is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

def finePairSourceRows (C : ModelConstants d) (k D M q : ℕ)
    (Cfr T₀ N : ℝ) :
    HighUnionRowData d k D FinePairRowTag (FinePairRowMark d D M q) :=
  finePairRowData d k D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr T₀ N

/-- The three true unit/coarse/fine packet rows satisfy every primitive
source guard under their physical numerical parameter conditions. -/
theorem finePairSourceRows_guards {C : ModelConstants d} [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    {Cfr : ℝ} (hCfr : 1 ≤ Cfr) {T₀ N : ℝ} (hT₀ : 0 < T₀) (hTN : T₀ < N) :
    HighUnionSourceGuards C (M : ℝ) Cfr (finePairSourceRows C k D M q Cfr T₀ N) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  obtain ⟨ha, hab⟩ := high_source_interval_numeric hM
  have hCf : 0 < Cfr := by linarith
  have hpos := finePairRowMass_positive d hD M q hq ha hab hCf hT₀ hTN
  refine {
    resolution := hM
    frame := hCfr
    row_probability := ?_
    mass_nonneg := ?_
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := ?_
    activation_centered := ?_
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := ?_
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · solve_by_elim [finePairRowLaw_probability]
  · apply finePairRowMass_nonneg
  · exact Finset.sum_pos' (fun i _ => (hpos i).le) ⟨.unit, Finset.mem_univ _, hpos .unit⟩
  · solve_by_elim [finePairRowActivation_measurable]
  · apply finePairRowActivation_bound
  · solve_by_elim [finePairRowActivation_centered]
  · apply finePairRowSlope_joint_measurable
  · solve_by_elim [finePairRowSlope_integrable]
  · solve_by_elim [finePairRowSlope_centered]
  · exact finePairRowIntercept_measurable d D M q a b
  · exact finePairRowIntercept_mem d D M q hab.le
  · solve_by_elim [finePairRow_reset_interval]
  · exact finePairRowVector_measurable d D M q Cfr
  · exact finePairRowTime_measurable d D M q
  · exact finePairRowVector_ball d D M q hCf
  · exact finePairRowTime_unit d D M q

end NearlyMinimax
