module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm

/-! # Continuity of unshifted positive parts in spatial `H¹₀` -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The positive-part map contracts the full spatial graph norm. -/
theorem norm_h10PositivePart_le (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ‖h10PositivePart hΩ u‖ ≤ ‖u‖ := norm_h10ShiftedPositivePart_le hΩ u 0

/-- Continuity in the norm of spatial `H¹₀`. -/
theorem continuous_h10PositivePart (hΩ : IsOpen Ω) : Continuous (h10PositivePart hΩ) :=
  (continuous_h10ShiftedPositivePart hΩ).comp (continuous_id.prodMk continuous_const)

end HypoellipticAleksandrov.Parabolic.Dirichlet
