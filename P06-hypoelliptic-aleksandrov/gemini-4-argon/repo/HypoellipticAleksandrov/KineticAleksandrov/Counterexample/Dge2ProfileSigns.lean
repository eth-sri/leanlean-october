module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsRescaled
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsSeedTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
import Mathlib.Tactic.FieldSimp
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
import PDEFoundation.Ambient.EuclideanNorm

/-! # Hessian and transport signs of the literal full kinetic profile -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped BigOperators

/- The full-product velocity quadratic second jet. -/
def fullVelocityQuadratic {d : ℕ} (H : XV d → ℝ) (q : XV d) (w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ H z (0, w)) q (0, w)

/- The profile's full velocity Hessian has the source cutoff prefactor at nonzero position. -/
theorem geometricProfile_quadratic_nonzero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : XV d) (hx : q.1 ≠ 0) (w : PDE.Vec d) :
    fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w =
      Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) *
        cutoffHessian alpha C₀ sigma R (normalizedVelocity q.1 q.2) (positionDirection q.1) w := by
  have hq : q ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have heq : (fun v => geometricProfile alpha C₀ sigma R (q.1, v)) =
      (fun v => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) q.1 v) := by
    funext v
    simp only [geometricProfile, ite_eq_right hx]
  unfold fullVelocityQuadratic
  rw [show q = (q.1, q.2) from rfl,
    full_velocity_hessian_eq_slice _ q.1 q.2 w w hH, heq]
  let x := q.1
  let v := q.2
  let u := w
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
      (contDiff_id.prodMk contDiff_const)
  have heq : (fun a => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x a) =
      (fun a => Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
        cutoffProfile alpha C₀ sigma R
          (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) • a) (positionDirection x)) := by
    funext a
    rfl
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) ^ 2 =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    congr 1
    norm_num
    ring
  rw [heq]
  have hh := hessian_scaledFunction _ hF
    (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3))
    (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ))) v w u
  rw [hp] at hh
  exact hh

/- The full profile transport has the same source prefactor at nonzero position. -/
theorem geometricProfile_quadratic_zero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (v w : PDE.Vec d) (hv : v ≠ 0) :
    fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) (0, v) w =
      radialHessianForm alpha v w w := by
  have hq : ((0, v) : XV d) ≠ 0 := fun h => hv (congrArg Prod.snd h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have heq : (fun a => geometricProfile alpha C₀ sigma R ((0 : PDE.Vec d), a)) =
      radialProfile alpha := by
    funext a
    simp only [geometricProfile, ite_true]
  unfold fullVelocityQuadratic
  rw [full_velocity_hessian_eq_slice _ 0 v w w hH, heq]
  exact radialProfile_hessian alpha v w w hv

/- All source Hessian and transport sign conditions hold for the actual full profile. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
