module

public import RequestProject.PositiveFourierBasis
public import RequestProject.ConormalNormalization
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sobolev preservation by the actual finite Fourier correction

Finite Fourier output vectors make the chart correction regularizing.
The actual orthogonal compatibility projection preserves each Sobolev
order for which its finite collection of defining vectors is regular.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

def fourierSobolevSubmodule (s : ℝ) : Submodule ℂ L2Z where
  carrier := {b | IsSobolevSeq s (b : ℤ → ℂ)}
  zero_mem' := by simp [IsSobolevSeq]
  add_mem' := by
    intro b d hb hd
    show IsSobolevSeq s ((b + d : L2Z) : ℤ → ℂ)
    simpa only [lp.coeFn_add] using isSobolevSeq_add hb hd
  smul_mem' := by
    intro a b hb
    show IsSobolevSeq s ((a • b : L2Z) : ℤ → ℂ)
    simpa using isSobolevSeq_smul a hb

theorem isSobolevSeq_posProj {s : ℝ} {b : L2Z}
    (hb : IsSobolevSeq s b) :
    IsSobolevSeq s (posProj b : ℤ → ℂ) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hb
  by_cases hn : 0 < n
  · simp [posProj, hn]
  · simpa [posProj, hn] using sq_nonneg (sobWeight n ^ s * ‖b n‖)

theorem nonpositive_orthogonal_starProjection :
    nonpositiveFourierSubspaceᗮ.starProjection = posProj := by
  ext1 b
  have h := nonpositiveFourierSubspace.starProjection_add_starProjection_orthogonal b
  rw [nonpositiveFourierSubspace_starProjection] at h
  simp at h
  calc
    _ = b - (b - posProj b) := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using h
    _ = _ := by abel


end PolyaNeumann

end
