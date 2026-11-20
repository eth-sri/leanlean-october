module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

namespace Finsupp

/-- Transporting coefficients and generators together commutes with the linear combination. -/
theorem linearCombination_semilinear {ι R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    {σ : R →+* S} (f : M →ₛₗ[σ] N) {v : ι → M} {w : ι → N}
    (h : ∀ i, f (v i) = w i) (x : ι →₀ R) :
    linearCombination S w (x.mapRange σ (map_zero σ)) = f (linearCombination R v x) := by
  rw [linearCombination_apply, sum_mapRange_index (h := fun i a => a • w i) (fun _ => zero_smul _ _),
    linearCombination_apply, map_finsuppSum]
  simp only [f.map_smulₛₗ, h]

end Finsupp
