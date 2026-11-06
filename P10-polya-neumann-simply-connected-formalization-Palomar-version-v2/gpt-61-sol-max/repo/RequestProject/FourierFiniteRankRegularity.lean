module

public import RequestProject.PlanarTypes

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

def fourierSobolevSubmodule (s : ℝ) : Submodule ℂ L2Z where
  carrier := {b | IsSobolevSeq s (b : FourierSeq)}
  zero_mem' := by simp [IsSobolevSeq]
  add_mem' := (fun {b d} hb hd => id (id (isSobolevSeq_add hb hd)))
  smul_mem' := by
    intro a b hb
    show IsSobolevSeq s ((a • b))
    simpa   using isSobolevSeq_smul a hb

theorem isSobolevSeq_posProj  {b : L2Z}
    (hb : IsSobolevSeq s (b : FourierSeq)) :
    IsSobolevSeq s (posProj b : FourierSeq) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hb
  by_cases hn : 0 < n
  · simp [posProj, hn]
  · simpa [posProj, hn] using sq_nonneg (sobWeight n ^ s * ‖b n‖)

theorem nonpositive_orthogonal_starProjection :
    nonpositiveFourierSubspaceᗮ.starProjection = posProj := by
  ext1 b
  have h := nonpositiveFourierSubspace.starProjection_add_starProjection_orthogonal b
  rw [nonpositiveFourierSubspace_starProjection] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h
  calc
    _ = b - (b - posProj b) := by
      rw [eq_sub_iff_add_eq]
      simpa only [add_comm] using h
    _ = _ := by abel

instance (priority := 1000) finiteFourierCompatibilityOrthogonalProjection {m : ℕ}
    (η : Fin m → nonpositiveFourierSubspaceᗮ) :
    ((Submodule.span ℂ (range η))ᗮ).HasOrthogonalProjection := by
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

end PolyaNeumann

end
