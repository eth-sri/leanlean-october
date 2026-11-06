/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusFourierTestL2

/-!
# DOZZ.GFF.TorusFourierEvalIdentification

The measurable local Fourier limit agrees almost everywhere with the accepted G4 evaluation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by
  infer_instance
section
variable (r : ℕ) (f : TestFn)

/-- The scalar Fourier partial sums converge pointwise on the common square-summability event. -/
theorem ae_tendsto_equatorLocalFourierPartialEval :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      Tendsto (fun s : Finset (Fin 2 → ℤ) =>
        equatorLocalFourierPartialEval r f s ω) atTop
        (𝓝 (equatorLocalFourierEval r f ω)) := by
  filter_upwards [ae_equatorHaarCommonGood] with ω hω
  have hcos := equatorHaarCommonCosEval_summable_of_good r ω hω
  have hsin := equatorHaarCommonSinEval_summable_of_good r ω hω
  have hsum := hasSum_equatorLocalFourierPartialEval r f ω hcos hsin
  have hEval := equatorLocalFourierEval_eq_distributionCLM_apply r f ω hcos hsin
  aesop

/-- On tests supported in the inner part of a local chart, the local Fourier distribution
evaluation is almost everywhere the G4 isonormal evaluation. -/
theorem ae_equatorLocalFourierEval_eq_equatorFieldL2 (hsupp : Function.support f ⊆
      ball (0 : ℂ) (gffLocalModeRadius r - 1)) :
    (fun ω => equatorLocalFourierEval r f ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => equatorFieldL2 f ω) := by
  let R := gffLocalModeRadius r
  let L := gffLocalModeBoxSide r
  have hR := gffLocalModeRadius_pos r
  have hL : 0 < L := by
    dsimp [L, gffLocalModeBoxSide, gffLocalModeRadius]
    positivity
  have hbox : L / 2 = R + 2 := by
    dsimp [L, R, gffLocalModeBoxSide, gffLocalModeRadius]
    ring
  let partialTest : Finset (Fin 2 → ℤ) → TestFn := fun s =>
    equatorLocalFourierPartialTest R L hR f s
  have hLp : Tendsto (fun s =>
      equatorFieldL2 (partialTest s)) atTop (𝓝 (equatorFieldL2 f)) := by
    simpa [partialTest, R, L] using
      tendsto_equatorFieldL2_localFourierPartialTest R L hR hL hbox f hsupp
  have hFieldInMeasure :=
    tendstoInMeasure_of_tendsto_Lp hLp
  have hScalarInMeasure : TendstoInMeasure
      (GaussianFields.scaleSpaceWhiteNoiseMeasure 2)
      (fun (s : Finset (Fin 2 → ℤ)) ω => equatorLocalFourierPartialEval r f s ω)
      atTop (equatorFieldL2 f) := by
    apply hFieldInMeasure.congr_left
    intro s
    simpa [partialTest, R, L] using
      (ae_equatorLocalFourierPartialEval_eq_equatorFieldL2 r f s hsupp).symm
  have hScalarAestrong : ∀ s : Finset (Fin 2 → ℤ),
      AEStronglyMeasurable (equatorLocalFourierPartialEval r f s)
        (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) := by
    intro s
    exact (measurable_equatorLocalFourierPartialEval r f s).aestronglyMeasurable
  obtain ⟨ns, hns, hScalarSeqInMeasure⟩ :=
    hScalarInMeasure.exists_seq_tendstoInMeasure_atTop
  have hPointwiseSeq : ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      Tendsto (fun n => equatorLocalFourierPartialEval r f (ns n) ω) atTop
        (𝓝 (equatorLocalFourierEval r f ω)) := by
    filter_upwards [(ae_tendsto_equatorLocalFourierPartialEval r f)] with ω hω
    exact hω.comp hns
  have hScalarSeqAestrong : ∀ n : ℕ,
      AEStronglyMeasurable
        (equatorLocalFourierPartialEval r f (ns n))
        (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) := by
    intro n
    exact hScalarAestrong (ns n)
  have hScalarSeqToEval :=
    tendstoInMeasure_of_tendsto_ae hScalarSeqAestrong hPointwiseSeq
  have hEq := tendstoInMeasure_ae_unique
   
   
   
    hScalarSeqInMeasure hScalarSeqToEval
  exact hEq.symm

end

end DOZZ

end
