module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesTransport
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling

/-! # Exact velocity-Hessian prefactor in homogeneous coordinates -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The homogeneous cutoff ansatz has the literal source velocity-Hessian scaling. -/
theorem homogeneousAnsatz_velocity_hessian {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (x v w u : PDE.Vec d) (hx : x ≠ 0) :
    fderiv ℝ (fun z => fderiv ℝ
      (fun a => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x a) z w) v u =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) *
        fderiv ℝ (fun z => fderiv ℝ
          (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) z w)
          (normalizedVelocity x v) u := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hF : ContDiff ℝ _
      (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
      (contDiff_id.prodMk contDiff_const)
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3)) ^ 2 =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    ring
  have hh := hessian_scaledFunction _ hF
    (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3))
    (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3))) v w u
  rw [hp] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
