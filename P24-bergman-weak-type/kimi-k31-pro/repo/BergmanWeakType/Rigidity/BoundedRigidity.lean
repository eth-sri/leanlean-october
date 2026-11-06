/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.DomainGap
public import BergmanWeakType.Rigidity.Perturbation
public import BergmanWeakType.Rigidity.DiskSimilarity

@[expose] public section

noncomputable section

open Set MeasureTheory Metric

namespace BergmanWeakType

-- Keep the public statement's topology, bornology, and metric instances identical to the
-- independently elaborated Challenge statement, which imports no C*-algebra instances.
attribute [-instance] instCommCStarAlgebraComplex in
/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  constructor
  · intro hc
    by_contra hnd
    have : IsFiniteMeasure (area.restrict Ω) :=
      isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
    obtain ⟨E, hE, hsub, hEpos, η, hη, hη1, hgap⟩ :=
      exists_domain_core_gap hopen hbounded hconnected hK hnd
    have hlt := Rigidity.weakTypeConstant_gt_one_of_core_gap hopen.measurableSet hK hE hsub
      hEpos hη hη1 hgap
    rw [hc] at hlt
    exact (lt_irrefl 1) hlt
  · rintro ⟨c, R, hR, rfl⟩
    exact weakTypeConstant_domainPositiveProjection_ball_eq_one c hR hK

end BergmanWeakType
