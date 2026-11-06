module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockQuadraticBounds
import Mathlib.Tactic

/-! # Endpoint allowance and the source half-height quadratic estimate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/- Cancelling a positive spatial scale preserves the Euclidean endpoint allowance. -/
theorem endpoint_scaled_norm_le {d a C} (ha : 0 < a)
    (y : PDE.Vec d) (hy : PDE.vecEuclideanNorm y ≤ C * a) :
    PDE.vecEuclideanNorm (a⁻¹ • y) ≤ C := by
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr ha)]
  have he := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr ha.le)
  have heq : a⁻¹ * (C * a) = C := by field_simp
  exact he.trans_eq heq

/- The source one-eighth endpoint allowance gives q_h at most L squared over two. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
