module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import HypoellipticAleksandrov.Parabolic.ScalarCalculus

/-! # Symmetry of the scalar spatial Hessian -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Spatial C² slices give the exact scalar Hessian symmetry, without time regularity. -/
theorem scalarSpatialHessian_isSymm_of_c12
    {d : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hu : IsScalarC12On u U) {z : TimeVelocity d} (hz : z ∈ U) :
    (scalarSpatialHessian u z).IsSymm := by
  have hs := hu.spatialSlice_contDiffAt hz
  ext i j
  change scalarSpatialHessian u z j i = scalarSpatialHessian u z i j
  rw [_root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_apply_eq_sndFDeriv hs, _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_apply_eq_sndFDeriv hs]
  exact hs.isSymmSndFDerivAt (by norm_num) _ _

end HypoellipticAleksandrov.Parabolic
