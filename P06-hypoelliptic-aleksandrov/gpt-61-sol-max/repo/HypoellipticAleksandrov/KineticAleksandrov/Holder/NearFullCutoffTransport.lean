module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic

/-! # Directional transport derivative of the source kinetic cutoff -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

variable {d : ℕ}

section
variable {u : HypoellipticAleksandrov.KineticScalarField d} {P : KineticPoint d} (hu : DifferentiableAt ℝ (rawLift u) (rawPoint P))

include hu
/-- The position slice derivative is the corresponding raw coordinate direction. -/
theorem fderiv_positionSlice   (w : PDE.Vec d) :
    fderiv ℝ (fun x => u ⟨P.time, x, P.velocity⟩) P.position w =
      fderiv ℝ (rawLift u) (rawPoint P) (0, (w, 0)) := by
  let sharedTerm_f23c54322f := ((fun x : PDE.Vec d => (P.time, (x, P.velocity))))
  have hc : HasFDerivAt sharedTerm_f23c54322f
      ((0 : PDE.Vec d →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
          (0 : PDE.Vec d →L[ℝ] PDE.Vec d))) P.position :=
    (hasFDerivAt_const P.time P.position).prodMk
      ((hasFDerivAt_id P.position).prodMk (hasFDerivAt_const P.velocity P.position))
  change (fderiv ℝ (rawLift u ∘ sharedTerm_f23c54322f) P.position) w = _
  rw [(hu.hasFDerivAt.comp P.position hc).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- The source time-plus-transport operator is the literal raw directional derivative. -/
theorem kinetic_transport_eq_fderiv   :
    kineticTimeDerivative u P + PDE.vecDot P.velocity (kineticPositionGradient u P) =
      fderiv ℝ (rawLift u) (rawPoint P) (1, (P.velocity, 0)) := by
  rw [kineticTimeDerivative_eq_fderiv hu, PDE.vecDot_comm]
  change _ + PDE.vecDot
    (PDE.classicalGradient (fun x => u ⟨P.time, x, P.velocity⟩) P.position) P.velocity = _
  rw [← PDE.fderiv_apply_eq_vecDot_classicalGradient, fderiv_positionSlice hu]
  rw [← map_add]
  congr 1
  ext <;> simp
end


/-- The unit free-transport direction under the inverse physical affine coordinates. -/
theorem hasDerivAt_inverse_transport  (P₀ P : KineticPoint d)
    (R : ℝ) :
    HasDerivAt (fun t  => KineticPoint.equivProd d
      (kineticAffineInverse P₀ R ⟨P.time + t, P.position + t • P.velocity, P.velocity⟩))
      ((R ^ 2)⁻¹, ((R ^ 3)⁻¹ • (P.velocity - P₀.velocity), 0)) 0 := by
  have ht : HasDerivAt (fun t  => P.time + t) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add P.time
  have hx : HasDerivAt (fun t : ℝ => P.position + t • P.velocity) P.velocity 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const P.velocity).const_add P.position

  have hx' := ((hx.sub_const P₀.position).sub
    ((ht.sub_const P₀.time).smul_const P₀.velocity)).const_smul ((R ^ 3)⁻¹)

  change HasDerivAt (fun t : ℝ =>
    ((P.time + t - P₀.time) / R ^ 2,
      ((R ^ 3)⁻¹ • (P.position + t • P.velocity - P₀.position -
        (P.time + t - P₀.time) • P₀.velocity), R⁻¹ • (P.velocity - P₀.velocity))))
    ((R ^ 2)⁻¹, ((R ^ 3)⁻¹ • (P.velocity - P₀.velocity), 0)) 0
  simpa only [one_div, Pi.sub_apply, Pi.smul_apply, one_smul] using
    ((ht.sub_const P₀.time).div_const (R ^ 2)).prodMk (hx'.prodMk (hasDerivAt_const (0 : ℝ) (R⁻¹ • (P.velocity - P₀.velocity))))

end HypoellipticAleksandrov.KineticAleksandrov.Holder
