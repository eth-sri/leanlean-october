module

public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Domain energies controlled by the `H¹` graph distance

The scalar value error and the Euclidean magnitude of the gradient error each
have squared integral at most the squared distance in the complete `H¹`
graph.  Both component comparisons have constant one.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

/-- The squared integral of a representative of a scalar `L²` class is its
squared `L²` norm. -/
theorem integral_sq_eq_sq_norm_of_ae_eq
    {d U} (F : ScalarLp U (2 : ℝ≥0∞))
    (f : Vec d → ℝ)
    (hF : ⇑F =ᵐ[volumeOn U] f) :
    (∫ x, f x ^ 2 ∂(volumeOn U)) = ‖F‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂(volumeOn U)) =
        ∫ x, F x ^ 2 ∂(volumeOn U) := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      rw [hx]
    _ = RCLike.re (inner ℝ F F) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner F F)]
      apply integral_congr_ae
      filter_upwards with x
      simp
    _ = ‖F‖ ^ 2 := inner_self_eq_norm_sq F

/-- The squared integral of the norm of a representative of a Hilbert-vector
`L²` class is its squared `L²` norm. -/
theorem integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert
    {d U}
    (F : HilbertVectorLp U (2 : ℝ≥0∞))
    (f : Vec d → ℝ)
    (hF : (fun x => ‖F x‖) =ᵐ[volumeOn U] f) :
    (∫ x, f x ^ 2 ∂(volumeOn U)) = ‖F‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂(volumeOn U)) =
        ∫ x, ‖F x‖ ^ 2 ∂(volumeOn U) := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      rw [hx]
    _ = RCLike.re (inner ℝ F F) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner F F)]
      apply integral_congr_ae
      filter_upwards with x
      simp
    _ = ‖F‖ ^ 2 := inner_self_eq_norm_sq F

namespace H1Function

end H1Function

end

end PDE
