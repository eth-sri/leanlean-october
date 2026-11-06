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

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/- The position slice derivative is the corresponding raw coordinate direction. -/
theorem fderiv_positionSlice {d : ℕ} {u : KineticPoint d → ℝ} {P : KineticPoint d}
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint P)) (w : PDE.Vec d) :
    fderiv ℝ (fun x => u ⟨P.time, x, P.velocity⟩) P.position w =
      fderiv ℝ (rawLift u) (rawPoint P) (0, (w, 0)) := by
  have hc : HasFDerivAt (fun x : PDE.Vec d => (P.time, (x, P.velocity)))
      ((0 : PDE.Vec d →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
          (0 : PDE.Vec d →L[ℝ] PDE.Vec d))) P.position :=
    (hasFDerivAt_const P.time P.position).prodMk
      ((hasFDerivAt_id P.position).prodMk (hasFDerivAt_const P.velocity P.position))
  change (fderiv ℝ (rawLift u ∘ fun x => (P.time, (x, P.velocity))) P.position) w = _
  rw [(hu.hasFDerivAt.comp P.position hc).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/- The source time-plus-transport operator is the literal raw directional derivative. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
