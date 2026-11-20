/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Fatou's lemma transfers uniform nonnegative expectation bounds through convergence in measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- If real random variables converge in measure and their positive-part expectations are uniformly
bounded, the limiting positive-part expectation has the same bound. -/
theorem lintegral_ofReal_limit_le_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℝ → Ω → ℝ) (G : Ω → ℝ) (C : ℝ≥0∞)
    (hFmeas : ∀ r, Measurable (F r))
    (hT : TendstoInMeasure P F atTop G)
    (hbound : ∀ r, ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤ C := by
  obtain ⟨ns, hns, hae⟩ := hT.exists_seq_tendsto_ae'
  have hQmeas := fun n =>
  ENNReal.measurable_ofReal.comp (hFmeas (ns n))
  exact Trans.trans
    (Trans.trans
      (lintegral_congr_ae
        (EventuallyEq.symm
          (mp_mem (mp_mem hae (univ_mem' (id fun ω hω => ENNReal.tendsto_ofReal hω)))
            (univ_mem' (id fun ω hω => Tendsto.liminf_eq hω)))))
      (lintegral_liminf_le hQmeas))
    (liminf_le_of_frequently_le' (Frequently.of_forall fun n => id (hbound (ns n))))

end DOZZ.Proofs
