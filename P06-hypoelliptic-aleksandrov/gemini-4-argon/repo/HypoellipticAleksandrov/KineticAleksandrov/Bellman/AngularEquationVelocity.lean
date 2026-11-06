module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSeparated
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic

/-! # The second velocity derivative of the literal angular separated test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/- Every positive-position point is the literal angular point of its inverse coordinates. -/
theorem bellmanAngularPoint_inverse (q : ℝ × ℝ) (hq : 0 < q.1) :
    (bellmanAngularPoint (bellmanAngularHomeomorph.symm ⟨q, hq⟩)).val = q :=  congrArg Subtype.val (bellmanAngularHomeomorph.apply_symm_apply ⟨q, hq⟩)

/- The first velocity formula holds throughout the open positive-position half-plane. -/
end HypoellipticAleksandrov.KineticAleksandrov
