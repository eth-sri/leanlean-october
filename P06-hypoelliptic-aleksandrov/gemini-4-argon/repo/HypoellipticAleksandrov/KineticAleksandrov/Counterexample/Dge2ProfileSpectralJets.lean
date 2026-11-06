module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSigns
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffCompact
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsRescaled
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsSeedTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffJets
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
import PDEFoundation.Ambient.EuclideanNorm
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRadial
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Compactness.Compact
import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # Spectral sign and continuity interfaces discharged by the actual profile -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped BigOperators

/- Scalar directional evaluation of the local slice second derivative. -/
theorem secondDirectional_eq_at {d : ℕ} (F : PDE.Vec d → ℝ) (y w u : PDE.Vec d)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F y) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u = fderiv ℝ (fderiv ℝ F) y u w := by
  have hd := (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/- The native velocity matrix represents the literal full velocity quadratic jet. -/
theorem dvv_quadratic_eq {d : ℕ} (H : XV d → ℝ) (q : XV d) (w : PDE.Vec d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) :
    dotProduct w ((dvv H q).mulVec w) = fullVelocityQuadratic H q w := by
  let F := fun v => H (q.1, v)
  have hF :=
    hH.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  have heq : dvv H q = fun i k => fderiv ℝ (fderiv ℝ F) q.2
      (Pi.single i 1) (Pi.single k 1) := by
    ext i k
    change fderiv ℝ (fun z => fderiv ℝ H z (0, Pi.single k 1))
      (q.1, q.2) (0, Pi.single i 1) = _
    rw [full_velocity_hessian_eq_slice H q.1 q.2 _ _ hH]
    exact secondDirectional_eq_at F q.2 _ _ hF
  rw [heq, dotProduct_matrix_of_bilinear]
  unfold fullVelocityQuadratic
  rw [show q = (q.1, q.2) from rfl, full_velocity_hessian_eq_slice H q.1 q.2 w w hH]
  exact (secondDirectional_eq_at F q.2 w w hF).symm

/- The velocity Hessian matrix of a smooth punctured profile is continuous off the origin. -/
theorem continuousOn_dvv_off_origin {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) : ContinuousOn (dvv H) ({0}ᶜ) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hd := hH.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro k
  have hscalar := hd.clm_apply (contDiffOn_const (c := ((0, Pi.single k 1) : XV d)))
  exact (hscalar.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
    (continuousOn_const (c := ((0, Pi.single i 1) : XV d)))

/- The classical full transport scalar is continuous off the origin. -/
theorem continuousOn_transport_off_origin {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) :
    ContinuousOn (fun q => PDE.vecDot q.2 (dx H q)) ({0}ᶜ) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hc : Continuous (fun q : XV d => (q.2, (0 : PDE.Vec d))) := by fun_prop
  have hh := (hH.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply hc.continuousOn
  simpa only [transport_eq_direction] using hh

/- The actual full profile discharges the spectral solver's sign conditions off the origin. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
