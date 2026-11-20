/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.CoreGap
public import BergmanWeakType.Rigidity.DiskSimilarity

public section


namespace BergmanWeakType

/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  constructor
  · intro hc
    by_contra hnd
    exact (weakTypeConstant_gt_one_of_nondisk hopen hconnected hbounded hK hnd).ne' hc
  · rintro ⟨c, R, hR, rfl⟩
    exact weakTypeConstant_domainPositiveProjection_ball_eq_one c hR hK

end BergmanWeakType
