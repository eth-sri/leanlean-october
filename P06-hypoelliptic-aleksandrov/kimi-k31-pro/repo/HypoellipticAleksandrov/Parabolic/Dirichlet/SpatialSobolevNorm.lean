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
  change
    ‖(u : PDE.H1HilbertGraph Ω).1‖ ^ 2 =
      ‖(u : PDE.H1HilbertGraph Ω).1.fst‖ ^ 2 +
        ‖(u : PDE.H1HilbertGraph Ω).1.snd‖ ^ 2
  exact WithLp.prod_norm_sq_eq_of_L2 _

theorem norm_h10HilbertGraph_le_value_add_gradient
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ‖u‖ ≤ ‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖u‖ ^ 2 = ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 :=
      norm_sq_h10HilbertGraph hΩ u
    _ ≤ ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 +
        2 * (‖valueCLM hΩ u‖ * ‖gradientCLM hΩ u‖) := by
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖) ^ 2 := by ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
