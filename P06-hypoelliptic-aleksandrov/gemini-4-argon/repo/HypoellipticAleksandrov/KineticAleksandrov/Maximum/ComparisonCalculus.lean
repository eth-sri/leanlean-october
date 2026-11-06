module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Classical transport differentiation with anisotropic regularity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology

/- The position differential encoded by the existing classical gradient. -/
def comparisonPositionDifferential {d } (u : KineticPoint d → ℝ)
    (P : KineticPoint d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, kineticPositionGradient u P i • ContinuousLinearMap.proj i

/- The encoded differential agrees with the actual position-slice differential. -/
theorem comparisonPositionDifferential_eq_fderiv {d }
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    comparisonPositionDifferential u P =
      fderiv ℝ (fun x => u ⟨P.time,x,P.velocity⟩) P.position := by
  ext v
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
  simp only [comparisonPositionDifferential, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    kineticPositionGradient, PDE.vecDot]

/- Continuity of the existing position gradient implies continuity of its differential. -/
end HypoellipticAleksandrov.KineticAleksandrov
