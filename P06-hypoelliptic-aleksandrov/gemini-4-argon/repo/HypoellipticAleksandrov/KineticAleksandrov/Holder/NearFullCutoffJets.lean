module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffTransport
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffAffine
import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Exact transport and velocity-Hessian scaling of the interior cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/- Smoothness of a scaled cutoff in the existing raw product coordinates. -/
theorem hasDerivAt_kinetic_transport {d : ℕ} {u : KineticPoint d → ℝ}
    {P : KineticPoint d} (hu : DifferentiableAt ℝ (rawLift u) (rawPoint P)) :
    HasDerivAt (fun t : ℝ => u ⟨P.time + t, P.position + t • P.velocity, P.velocity⟩)
      (kineticTimeDerivative u P + PDE.vecDot P.velocity (kineticPositionGradient u P))
      0 := by
  have ht : HasDerivAt (fun t : ℝ => P.time + t) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add P.time
  have hx : HasDerivAt (fun t : ℝ => P.position + t • P.velocity) P.velocity 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const P.velocity).const_add P.position
  have hc := ht.prodMk (hx.prodMk (hasDerivAt_const (0 : ℝ) P.velocity))
  have heq : (P.time + (0 : ℝ), (P.position + (0 : ℝ) • P.velocity, P.velocity)) =
      rawPoint P := by simp [rawPoint]
  have hu' := hu
  rw [← heq] at hu'
  have _h_xinl_0 : kineticTimeDerivative u P + PDE.vecDot P.velocity (kineticPositionGradient u P) =
      fderiv ℝ (rawLift u) (rawPoint P) (1, (P.velocity, 0)) := by
    rw [kineticTimeDerivative_eq_fderiv hu, PDE.vecDot_comm]
    change _ + PDE.vecDot
      (PDE.classicalGradient (fun x => u ⟨P.time, x, P.velocity⟩) P.position) P.velocity = _
    rw [← PDE.fderiv_apply_eq_vecDot_classicalGradient, fderiv_positionSlice hu]
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [_h_xinl_0]
  simpa only [heq, rawLift, Function.comp_def] using
    hu'.hasFDerivAt.comp_hasDerivAt 0 hc

/- The time-plus-transport jet scales by the exact inverse-square radius. -/
theorem scaledUnitCutoff_transport {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (P₀ P : KineticPoint d) (R ell : ℝ) :
    kineticTimeDerivative (scaledUnitCutoff f P₀ R ell) P +
      PDE.vecDot P.velocity (kineticPositionGradient (scaledUnitCutoff f P₀ R ell) P) =
      ell * (R ^ 2)⁻¹ *
        fderiv ℝ f (KineticPoint.equivProd d (kineticAffineInverse P₀ R P))
          (1, ((kineticAffineInverse P₀ R P).velocity, 0)) := by
  let Q := kineticAffineInverse P₀ R P
  have hi : HasDerivAt (fun t : ℝ => KineticPoint.equivProd d
      (kineticAffineInverse P₀ R ⟨P.time + t, P.position + t • P.velocity, P.velocity⟩))
      ((R ^ 2)⁻¹, ((R ^ 3)⁻¹ • (P.velocity - P₀.velocity), 0)) 0 := by
    have ht : HasDerivAt (fun t : ℝ => P.time + t) 1 0 :=
      (hasDerivAt_id (0 : ℝ)).const_add P.time
    have hx : HasDerivAt (fun t : ℝ => P.position + t • P.velocity) P.velocity 0 := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).smul_const P.velocity).const_add P.position
    have ht' := (ht.sub_const P₀.time).div_const (R ^ 2)
    have hx' := ((hx.sub_const P₀.position).sub
      ((ht.sub_const P₀.time).smul_const P₀.velocity)).const_smul ((R ^ 3)⁻¹)
    have hv' := hasDerivAt_const (0 : ℝ) (R⁻¹ • (P.velocity - P₀.velocity))
    change HasDerivAt (fun t : ℝ =>
      ((P.time + t - P₀.time) / R ^ 2,
        ((R ^ 3)⁻¹ • (P.position + t • P.velocity - P₀.position -
          (P.time + t - P₀.time) • P₀.velocity), R⁻¹ • (P.velocity - P₀.velocity))))
      ((R ^ 2)⁻¹, ((R ^ 3)⁻¹ • (P.velocity - P₀.velocity), 0)) 0
    simpa only [one_div, Pi.sub_apply, Pi.smul_apply, one_smul] using
      ht'.prodMk (hx'.prodMk hv')
  have hq : KineticPoint.equivProd d
      (kineticAffineInverse P₀ R
        ⟨P.time + (0 : ℝ), P.position + (0 : ℝ) • P.velocity, P.velocity⟩) =
      KineticPoint.equivProd d Q := by simp only [add_zero, zero_smul, Q]
  have hd := (hf.differentiable (by simp)).differentiableAt
    (x := KineticPoint.equivProd d Q)
  rw [← hq] at hd
  have hc := (hd.hasFDerivAt.comp_hasDerivAt 0 hi).const_mul ell
  have _h_inl_19 : ContDiff ℝ (⊤ : ℕ∞) (rawLift (scaledUnitCutoff f P₀ R ell)) := by
      exact (
    contDiff_const.mul (hf.comp (contDiff_kineticAffineInverse_prod P₀ R))
    )
  have ht := hasDerivAt_kinetic_transport
    (_h_inl_19.differentiable (by simp)).differentiableAt
      (P := P)
  have hsame : kineticTimeDerivative (scaledUnitCutoff f P₀ R ell) P +
      PDE.vecDot P.velocity (kineticPositionGradient (scaledUnitCutoff f P₀ R ell) P) =
      ell * fderiv ℝ f (KineticPoint.equivProd d Q)
        ((R ^ 2)⁻¹, ((R ^ 3)⁻¹ • (P.velocity - P₀.velocity), 0)) := by
    apply ht.unique
    simpa only [scaledUnitCutoff, Function.comp_apply, hq] using hc
  have hv : ((R ^ 2)⁻¹, ((R ^ 3)⁻¹ • (P.velocity - P₀.velocity), 0)) =
      (R ^ 2)⁻¹ • ((1, (Q.velocity, 0)) : ℝ × (PDE.Vec d × PDE.Vec d)) := by
    ext i
    all_goals simp [Q, kineticAffineInverse, relativeVelocity]
    all_goals ring
  rw [hsame, hv, map_smul]
  simp only [smul_eq_mul]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
