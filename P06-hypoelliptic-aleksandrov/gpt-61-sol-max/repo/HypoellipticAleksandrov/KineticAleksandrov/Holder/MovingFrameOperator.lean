module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrame
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # The complete source operator in moving skeleton coordinates -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

variable {d : ℕ}

variable {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} (hf : ContDiff ℝ PDE.smoothOrder f)

include hf in
/-- Velocity translation leaves the velocity Hessian unchanged in moving coordinates. -/
theorem movingLift_velocityHessian
     (tminus : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) :
    kineticVelocityHessian (movingLift f tminus x v) P =
      kineticVelocityHessian
        (fun Q  => f (P.time - tminus, (Q.position, Q.velocity)))
        ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩ := by
  let s := P.time - tminus
  let y := P.position - x s
  let g := fun V  => f (s, (y, V))
  have hg : ContDiff ℝ PDE.smoothOrder g := hf.comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hslice : (fun V  => movingLift f tminus x v ⟨P.time, P.position, V⟩) =
      (fun V => g (-v s + (1 : ℝ) • V)) := by
    funext V
    simp only [movingLift, movingCoordinates, s, y, g, one_smul]
    congr 2
    abel_nf
  rw [kineticVelocityHessian_eq_sliceHessian, hslice,
    kineticVelocityHessian_eq_sliceHessian]
  have h := sliceHessian_affine (y₀ := -v s) (c := (1 )) (Y := P.velocity)
    (hg.contDiffAt.of_le (by norm_cast))
  simpa only [one_smul, one_pow, neg_add_eq_sub] using h

section
variable (s : ℝ) (y V : PDE.Vec d)

include hf
/-- The source time slice is the raw time-direction derivative. -/
theorem deriv_raw_time_slice
      :
    deriv (fun r => f (r, (y, V))) s = fderiv ℝ f (s, (y, V)) (1, (0, 0)) := ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s (y, V)))).deriv

/-- The source position-line derivative is the raw transport-direction derivative. -/
theorem deriv_raw_position_line
      :
    deriv (fun r : ℝ => f (s, (y + r • V, V))) 0 =
      fderiv ℝ f (s, (y, V)) (0, (V, 0)) := by


  simpa only [Function.comp_def, zero_smul, add_zero] using
    ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 s).prodMk ((show HasDerivAt (fun r : ℝ => y + r • V) V 0 by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add y).prodMk (hasDerivAt_const 0 V)))).deriv
end


/-- The complete source chain rule, with precisely the acceleration correction. -/
theorem movingLift_backwardOperator  (A : FullKineticCoefficient d)
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} {x v : ℝ → PDE.Vec d}
    (hf : ContDiff ℝ PDE.smoothOrder f) (hx : ContDiff ℝ PDE.smoothOrder x)
    (hv : ContDiff ℝ PDE.smoothOrder v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (tminus : ℝ) (P : KineticPoint d) :
    backwardOperator A (movingLift f tminus x v) P =
      deriv (fun s => f (s, (P.position - x (P.time - tminus),
        P.velocity - v (P.time - tminus)))) (P.time - tminus) +
      deriv (fun r : ℝ => f (P.time - tminus,
        (P.position - x (P.time - tminus) + r • (P.velocity - v (P.time - tminus)),
          P.velocity - v (P.time - tminus)))) 0 -
      PDE.vecDot (deriv v (P.time - tminus))
        (kineticVelocityGradient (fun Q  =>
          f (P.time - tminus, (Q.position, Q.velocity)))
          ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩) -
      matrixContraction (fullKineticCoefficientAt A P)
        (kineticVelocityHessian (fun Q  =>
          f (P.time - tminus, (Q.position, Q.velocity)))
          ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩) := by
  let s := P.time - tminus
  let y := P.position - x s
  let V := P.velocity - v s

  rw [backwardOperator, movingLift_transport hf hx hv hkin,
    movingLift_velocityHessian hf, deriv_raw_time_slice hf, deriv_raw_position_line hf]
  rw [vecDot_kineticVelocityGradient (by
      exact (hf.comp (contDiff_const.prodMk contDiff_snd)).differentiable (by norm_num) _)]
  change _ = _
  have hvel : fderiv ℝ (rawLift (fun Q  => f (s, (Q.position, Q.velocity))))
      (rawPoint (⟨0, y, V⟩ )) (0, (0, deriv v s)) =
      fderiv ℝ f (s, (y, V)) (0, (0, deriv v s)) := by
    have hc := (hasFDerivAt_const s (rawPoint (⟨0, y, V⟩ ))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := rawPoint (⟨0, y, V⟩ )))
    change fderiv ℝ (f ∘ fun Q : ℝ × (PDE.Vec d × PDE.Vec d) => (s, Q.2))
      (rawPoint (⟨0, y, V⟩ )) (0, (0, deriv v s)) = _
    rw [((hf.differentiable (by norm_num) _).hasFDerivAt.comp _ hc).fderiv]
    simp [rawPoint]
  rw [hvel]
  rw [← map_add]
  simp only [movingCoordinates, s, y, V, Prod.mk_add_mk, zero_add, add_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
