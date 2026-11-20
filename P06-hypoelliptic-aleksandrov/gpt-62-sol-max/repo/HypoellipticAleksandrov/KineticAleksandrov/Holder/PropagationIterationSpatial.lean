module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockBoundary
import Mathlib.Tactic

/-! # Spatial inclusion of positive initial-strip points in the preceding block -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- An initial-strip positive point lies strictly inside the preceding block spatial faces. -/
theorem gaussianBarrier_initial_previous_spatial {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d)
    (ht : P.time - tminus - sblock ≤ 0)
    (hpos : 0 < gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P) :
    P.velocity ∈ PDE.euclideanBall (v sblock)
        (barrierW d lam Lam H T1 * Real.sqrt h) ∧
      relativePosition ⟨tminus + sblock, x sblock, v sblock⟩ P ∈
        PDE.euclideanBall (0 : PDE.Vec d) ((barrierW d lam Lam H T1 * Real.sqrt h) ^ 3) := by
  exact gaussianBarrier_positive_spatial hd hlam hLam hH hT0 hT1 hh hhstar hell
    tminus sblock hv hkin hLip P (le_add_of_nonneg_right hh.le) (by linarith) hpos

end HypoellipticAleksandrov.KineticAleksandrov.Holder
