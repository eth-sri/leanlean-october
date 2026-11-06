module

public import RequestProject.HardyAntiderivative
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The full closed nonpositive Fourier space

The original Hardy input space contains frequency zero. It is precisely
the kernel of the strict-positive Fourier projection; its actual Hilbert
orthogonal projection is therefore identity minus that projection.
These facts prepare the physical fixed-complement chart, without
asserting its still separately required reference-energy injectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open scoped InnerProductSpace

/-- The full nonpositive Fourier input space, including frequency zero. -/
def nonpositiveFourierSubspace : Submodule ℂ L2Z where
  carrier := {b | IsNonpositiveFourierSupport b}
  zero_mem' := by simp [IsNonpositiveFourierSupport]
  add_mem' := by
    intro b d hb hd n hn
    simp [hb n hn, hd n hn]
  smul_mem' := by
    intro c b hb n hn
    simp [hb n hn]

variable (b : L2Z)

theorem nonpositiveFourierSubspace_eq_ker_posProj :
    nonpositiveFourierSubspace = posProj.ker := by
  apply Submodule.ext
  intro b
  constructor
  · intro hb
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, hb n hn]
    simp [posProj, hn]
  · intro hb n hn
    simpa [posProj, hn] using congrArg (fun v  => v n) hb

theorem isClosed_nonpositiveFourierSubspace :
    IsClosed (nonpositiveFourierSubspace : Set L2Z) := by
  rw [nonpositiveFourierSubspace_eq_ker_posProj]
  exact posProj.isClosed_ker

instance nonpositiveFourierSubspaceCompleteSpace :
    CompleteSpace nonpositiveFourierSubspace :=
  isClosed_nonpositiveFourierSubspace.completeSpace_coe

instance nonpositiveFourierComplementCompleteSpace :
    CompleteSpace nonpositiveFourierSubspaceᗮ :=
  nonpositiveFourierSubspace.isClosed_orthogonal.completeSpace_coe

theorem one_sub_posProj_mem_nonpositive :
    (1 - posProj) b ∈ nonpositiveFourierSubspace := by
  intro n hn
  simp [posProj, hn]

theorem posProj_mem_nonpositive_orthogonal :
    posProj b ∈ nonpositiveFourierSubspaceᗮ := by
  intro a ha
  rw [lp.inner_eq_tsum]
  have hterms : (fun n => ⟪a n, posProj b n⟫_ℂ) = fun _ => 0 := by
    funext n
    by_cases hn : 0 < n
    · simp [ha n hn]
    simp [posProj, hn]
  simp_all

/-- The zero frequency belongs to the first summand of the actual
orthogonal decomposition used by the physical chart. -/
theorem nonpositiveFourierSubspace_starProjection :
    nonpositiveFourierSubspace.starProjection = 1 - posProj := by
  ext1 b
  apply nonpositiveFourierSubspace.eq_starProjection_of_mem_orthogonal
    (one_sub_posProj_mem_nonpositive b)
  have heq : b - (1 - posProj) b = posProj b := by
    norm_num
  rw [heq]
  exact posProj_mem_nonpositive_orthogonal b

end PolyaNeumann

end
