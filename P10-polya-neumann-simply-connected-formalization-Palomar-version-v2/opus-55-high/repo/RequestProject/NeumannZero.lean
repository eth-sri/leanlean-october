module

public import RequestProject.NeumannEigenspace
public import RequestProject.WeakConstancy

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The zero weak Neumann eigenspace consists exactly of the constants. -/
theorem mem_neumannEigenspace_zero_iff {Ω : Set ℂ} (hΩ : IsDomain Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (u : L2 Ω) :
    u ∈ neumannEigenspace Ω 0 ↔ ∃ c : ℂ, u = Lp.const 2 (volume.restrict Ω) c := by
  constructor
  · rintro ⟨g, hg, hweak⟩
    have h := hweak u g hg
    have hnorm : ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2 = 0 :=
      Complex.ofReal_injective (by simp_all)
    have hg0 : g = 0 := by
      have hzero0 : g 0 = 0 := norm_eq_zero.mp (by
        nlinarith )
      funext i
      fin_cases i <;> simp [hzero0, norm_eq_zero.mp (by
        nlinarith )]
    obtain ⟨c, hc⟩ := ae_const_of_weakGradient_zero hΩ u (by simp_all)
    refine ⟨c, Lp.ext ?_⟩
    filter_upwards [hc, Lp.coeFn_const 2 (volume.restrict Ω) c] with w hw hconst
    simp_all
  · rintro ⟨c, rfl⟩
    refine ⟨0, isWeakGradient_const Ω c, fun v h hv => ?_⟩
    simp

end PolyaNeumann

end
