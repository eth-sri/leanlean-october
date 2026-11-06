/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCUniqueConcrete
public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Uniqueness transfer once mixed cutoff test integrals are Cauchy in measure. -/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped CompactlySupported

namespace DOZZ.Proofs

/-- Subtraction preserves convergence in measure for real-valued families. -/
theorem tendstoInMeasure_sub
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {l : Filter ι}
    (F G : ι → Ω → ℝ) (Flim Glim : Ω → ℝ)
    (hF : TendstoInMeasure P F l Flim)
    (hG : TendstoInMeasure P G l Glim) :
    TendstoInMeasure P (fun i ω => F i ω - G i ω) l
      (fun ω => Flim ω - Glim ω) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by positivity
  have hFzero := ((tendstoInMeasure_iff_norm).mp hF) δ hδ
  have hsum : Tendsto
      (fun i => P {ω | δ ≤ ‖F i ω - Flim ω‖} +
        P {ω | δ ≤ ‖G i ω - Glim ω‖}) l (𝓝 0) := by
    simpa using hFzero.add (((tendstoInMeasure_iff_norm).mp hG) δ hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
  · positivity
  · intro i
    let A := {ω | δ ≤ ‖F i ω - Flim ω‖}
    let B := {ω | δ ≤ ‖G i ω - Glim ω‖}
    let E := {ω | ε ≤ ‖(F i ω - G i ω) - (Flim ω - Glim ω)‖}
    have hsubset : E ⊆ A ∪ B := by
      intro ω hω
      change ε ≤ ‖(F i ω - G i ω) - (Flim ω - Glim ω)‖ at hω
      have htriangle :
          ‖(F i ω - G i ω) - (Flim ω - Glim ω)‖ ≤
            ‖F i ω - Flim ω‖ + ‖G i ω - Glim ω‖ := by
        calc
          _ = ‖(F i ω - Flim ω) - (G i ω - Glim ω)‖ := by ring
          _ ≤ _ := norm_sub_le ..
      by_contra hnot
      have hFlt : ‖F i ω - Flim ω‖ < δ := by aesop
      have hGlt : ‖G i ω - Glim ω‖ < δ := by aesop
      have hFltNorm : ‖F i ω - Flim ω‖ < δ := by
        simpa using hFlt
      have hGltNorm : ‖G i ω - Glim ω‖ < δ := by
        simpa using hGlt
      have hsumlt : ‖F i ω - Flim ω‖ + ‖G i ω - Glim ω‖ < ε := by
        calc
          _ < δ + δ := add_lt_add hFltNorm hGltNorm
          _ = ε := by ring
      exact (not_le_of_gt (lt_of_le_of_lt htriangle hsumlt)) hω
    change P E ≤ P A + P B
    calc
      P E ≤ P _ := measure_mono hsubset
      _ ≤ P A + P B := measure_union_le A B

end DOZZ.Proofs
