module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem entire_division_at_zero (q : ℂ → ℂ) (hq : Differentiable ℂ q) (hq0 : q 0 = 0) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s : ℂ, q s = s * u s := by
  refine ⟨dslope q 0, ?_, ?_⟩
  · rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      hq.differentiableOn
  · intro s
    simpa using (sub_smul_dslope_of_zero hq0 s).symm

end DedekindZetaZeroFree.AbelianQuotient
