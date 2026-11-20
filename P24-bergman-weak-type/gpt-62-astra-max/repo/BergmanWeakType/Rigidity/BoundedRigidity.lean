/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.DomainGap
public import BergmanWeakType.Rigidity.DiskSimilarity

@[expose] public section

noncomputable section

open Set MeasureTheory Metric

namespace BergmanWeakType

/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  constructor
  · intro hc; by_contra hnd
    exact (nondisk_gt_one hopen hbounded hconnected hK hnd).ne' hc
  · rintro ⟨c, R, hR, rfl⟩
    apply weakTypeConstant_domainPositiveProjection_ball_eq_one <;> assumption

end BergmanWeakType
