module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev

/-!
# Norm identity for the spatial `H¹₀` Hilbert graph

This module records the exact `ℓ²` product norm inherited by the spatial
Hilbert realization of the zero-boundary Sobolev graph.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The spatial `H¹₀` Hilbert-graph norm is the squared `ℓ²` sum of its value
and weak-gradient component norms. -/
theorem norm_sq_h10HilbertGraph
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ‖u‖ ^ 2 =
      ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 _

end HypoellipticAleksandrov.Parabolic.Dirichlet
