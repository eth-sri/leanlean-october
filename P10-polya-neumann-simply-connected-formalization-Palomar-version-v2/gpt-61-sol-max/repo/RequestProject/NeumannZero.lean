module

public import RequestProject.NeumannEigenspace
public import RequestProject.WeakConstancy

public section

open MeasureTheory



namespace PolyaNeumann

/-- The zero weak Neumann eigenspace consists exactly of the constants. -/
theorem mem_neumannEigenspace_zero_iff  (hΩ : IsDomain Ω)
    [IsFiniteMeasure (volume.restrict Ω)] u :
    u ∈ neumannEigenspace Ω 0 ↔ ∃ c : ℂ, u = Lp.const 2 (volume.restrict Ω) c := by
  constructor
  · rintro ⟨g, hg, hweak⟩
    have h := hweak u g hg
    simp   at h
    have hnorm : ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2 = 0 :=
      Complex.ofReal_injective (by push_cast; exact h)
    have hg0 : g = 0 := by
      have hzero0  := norm_eq_zero.mp (by
        nlinarith [sq_nonneg ‖g 1‖, norm_nonneg (g 0)])
      have hzero1  := norm_eq_zero.mp (by
        nlinarith [sq_nonneg ‖g 0‖, norm_nonneg (g 1)])
      funext i
      fin_cases i <;> simp [hzero0, hzero1]
    obtain ⟨c, hc⟩ := ae_const_of_weakGradient_zero hΩ u (by simpa [hg0] using hg)
    refine ⟨c, Lp.ext ?_⟩
    filter_upwards [hc, Lp.coeFn_const 2 (volume.restrict Ω) c] with w hw hconst
    exact hw.trans hconst.symm
  · rintro ⟨c, rfl⟩
    refine ⟨0, isWeakGradient_const Ω c, fun v h hv => ?_⟩
    simp

end PolyaNeumann
