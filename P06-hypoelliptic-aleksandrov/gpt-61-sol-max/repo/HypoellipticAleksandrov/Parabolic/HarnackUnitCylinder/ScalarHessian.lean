module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift

section
open private HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv from HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
private alias _sharedProof_197_3 := HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv
end


/-! # Symmetry of the scalar spatial Hessian -/

 public section

namespace HypoellipticAleksandrov.Parabolic

/-- The scalar Hessian equals the second derivative of the fixed-time slice. -/
theorem scalarSpatialHessian_eq_secondFDeriv
    {d : ℕ} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 (fun y => u (z.1, y)) z.2) (i j : Fin d) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y => u (z.1, y))) z.2 (PDE.basisVec i)
        (PDE.basisVec j) := (_sharedProof_197_3 hu i j)


/-- Spatial C² slices give the exact scalar Hessian symmetry, without time regularity. -/
theorem scalarSpatialHessian_isSymm_of_c12
    {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : IsScalarC12On u U) {z : TimeVelocity d} (hz : z ∈ U) :
    (scalarSpatialHessian u z).IsSymm := by
  have hs := hu.spatialSlice_contDiffAt hz
  ext i j
  change scalarSpatialHessian u z j i = scalarSpatialHessian u z i j
  rw [scalarSpatialHessian_eq_secondFDeriv hs, scalarSpatialHessian_eq_secondFDeriv hs]
  exact hs.isSymmSndFDerivAt (by norm_num) _ _

end HypoellipticAleksandrov.Parabolic
