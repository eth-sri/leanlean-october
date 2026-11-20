module

public import NearlyMinimax.SourceRows
public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.HigherBandRowSource


@[expose] public section

/-! All primitive source guards for the complete singleton, pair, and
higher coarse/fine row family. Numerical guards are the only inputs. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def completeSourceRows {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (Cfr lam ℓ N μ : ℝ) :=
  sourceRowData d k D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ

/-- Histories for the full singleton, pair, and higher-band source family. -/
abbrev HighCompleteSourceHistory {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    [NeZero k] [LinearOrder (HighWindowLabels d k)] (Cfr lam ℓ N μ : ℝ) :=
  HighUnionHistory d k (SourceRowMark d D M q (C.densityLower + 1/(M : ℝ))
    (C.densityUpper - 1/(M : ℝ)) Cfr lam ℓ N μ)

/-- The actual singleton response/density row satisfies every source
primitive guard; its nondegeneracy and centering follow from finite rules. -/
theorem singletonRowSource_guards {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr : ℝ) (hCfr : 1 ≤ Cfr) :
    HighUnionSourceGuards C (M : ℝ) Cfr
      (singletonRowData d k D q (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr) := by
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  exact highPacketRowData_guards C M hM k D 1 D q (by decide) Cfr hCfr (Measure.dirac ())
    (fun _ => finePairUnitMatrix d D) (SeparatedMatrixIntegrable.const _ _)
    (singletonRowMass_positive d D q hq _ _ ha hab Cfr (by linarith))
    (fun _ _ _ _ => 1) (fun _ _ => measurable_const) (by simp)

/-- Restricting primitive guards to one genuine positive row preserves
all of them. The one-row total is its actual variation mass. -/
theorem HighUnionSourceGuards.restrict {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] {C : ModelConstants d} {M Cfr : ℝ}
    {R : HighUnionRowData d k F I E} (G : HighUnionSourceGuards C M Cfr R)
    (i : I) (hpos : 0 < R.rowMass i) :
    HighUnionSourceGuards C M Cfr (highUnionRowRestrict R i) where
  resolution := G.resolution
  frame := G.frame
  row_probability := fun _ => G.row_probability i
  mass_nonneg := fun _ => G.mass_nonneg i
  total_positive := by simpa [highRowTotalMass,highUnionRowRestrict] using hpos
  activation_measurable := fun _ => G.activation_measurable i
  activation_bound := fun _ => G.activation_bound i
  activation_centered := fun _ => G.activation_centered i
  slope_measurable := fun j _ => G.slope_measurable j i
  slope_integrable := fun j x _ => G.slope_integrable j x i
  slope_centered := fun j x _ => G.slope_centered j x i
  intercept_measurable := fun _ => G.intercept_measurable i
  intercept_interval := fun _ => G.intercept_interval i
  row_reset_interval := fun j _ => G.row_reset_interval j i
  vector_measurable := fun _ => G.vector_measurable i
  time_measurable := fun _ => G.time_measurable i
  vector_ball := fun _ => G.vector_ball i
  time_interval := fun _ => G.time_interval i

/-- The complete actual source family satisfies every primitive source
condition from numerical guards alone. In particular the final prior is
not restricted to the pair rows or a single higher-target packet. -/
theorem completeSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    HighUnionSourceGuards C (M : ℝ) Cfr R ∧ ∀ i, 0 < R.rowMass i := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hCf : 0 < Cfr := by linarith
  have hcomp (i : SourceRowIndex d D M q a b Cfr lam ℓ N μ) :
      HighUnionSourceGuards C (M : ℝ) Cfr (sourceRowComponent d k D M q a b Cfr lam ℓ N μ i) := by
    cases i with
    | inl p =>
      exact (finePairSourceRows_guards C k D M q hD hq hM Cfr hCfr ℓ N hℓ hℓN).restrict p
        (finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf ℓ N hℓ hℓN p)
    | inr i =>
      cases i with
      | inl _ => exact singletonRowSource_guards C k D M q hq hM Cfr hCfr
      | inr i =>
        exact higherBandSourceRow_guards C k (higherBandFamilyTarget i.val)
          (higherBandFamilyGuardDegree M i.val) D q
          (by have hh := (higherBandFamily_target_bounds d D M q a b Cfr lam ℓ N μ i).1; omega)
          (M : ℝ) Cfr lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 hM hCfr
          i.property.1 i.property.2.2.2
  dsimp only
  have hpos (i : SourceRowIndex d D M q a b Cfr lam ℓ N μ) :
      0 < (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass i := by
    change 0 < (sourceRowComponent d k D M q a b Cfr lam ℓ N μ i).rowMass ()
    simpa only [highRowTotalMass, Fintype.sum_unique] using (hcomp i).total_positive
  refine ⟨?_, hpos⟩
  exact {
    resolution := hM
    frame := hCfr
    row_probability := fun i => (hcomp i).row_probability ()
    mass_nonneg := fun i => (hpos i).le
    total_positive := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
    activation_measurable := fun i => (hcomp i).activation_measurable ()
    activation_bound := fun i => (hcomp i).activation_bound ()
    activation_centered := fun i => (hcomp i).activation_centered ()
    slope_measurable := fun j i => (hcomp i).slope_measurable j ()
    slope_integrable := fun j x i => (hcomp i).slope_integrable j x ()
    slope_centered := fun j x i => (hcomp i).slope_centered j x ()
    intercept_measurable := fun i => (hcomp i).intercept_measurable ()
    intercept_interval := fun i => (hcomp i).intercept_interval ()
    row_reset_interval := fun j i => (hcomp i).row_reset_interval j ()
    vector_measurable := fun i => (hcomp i).vector_measurable ()
    time_measurable := fun i => (hcomp i).time_measurable ()
    vector_ball := fun i => (hcomp i).vector_ball ()
    time_interval := fun i => (hcomp i).time_interval () }

end NearlyMinimax
