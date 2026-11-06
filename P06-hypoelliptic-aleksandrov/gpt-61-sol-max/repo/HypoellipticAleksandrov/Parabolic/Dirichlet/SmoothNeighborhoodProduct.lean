module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Products with locally smooth coefficients

This module promotes smoothness near a prescribed set to global smoothness
after multiplication by a globally smooth function supported in that set.
-/

 public section

open Set



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {E : Type*}

private theorem contDiff_mul_of_contDiffOn_of_tsupport_subset
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {V : Set E}
    (hV : IsOpen V) (hf : ContDiffOn ℝ PDE.smoothOrder f V)
    (hg : ContDiff ℝ PDE.smoothOrder g) (hsub : tsupport g ⊆ V) :
    ContDiff ℝ PDE.smoothOrder (fun x => f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact (hf.contDiffAt (hV.mem_nhds hx)).mul hg.contDiffAt
  ·

    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsub h)))] with y hy
    rw [hy]
    simp

/-- Multiplying a function smooth near a set by a globally smooth function
supported in that set produces a globally smooth function. -/
theorem IsSmoothOnNeighborhood.contDiff_mul_of_tsupport_subset
     [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {K : Set E}
    (hf : IsSmoothOnNeighborhood f K) (hg : ContDiff ℝ PDE.smoothOrder g)
    (hsub : tsupport g ⊆ K) :
    ContDiff ℝ PDE.smoothOrder (fun x => f x * g x) := by
  rcases hf with ⟨V, hV, hKV, hfV⟩
  exact contDiff_mul_of_contDiffOn_of_tsupport_subset hV hfV hg
    (hsub.trans hKV)

end HypoellipticAleksandrov.Parabolic.Dirichlet
