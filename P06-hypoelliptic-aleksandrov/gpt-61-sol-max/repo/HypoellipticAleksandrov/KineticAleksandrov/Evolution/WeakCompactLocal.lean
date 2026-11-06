module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactness



/-!
# Weak subsequences in separable real Hilbert spaces

The sequential Banach--Alaoglu theorem and the Riesz isometry give a subsequence
converging against every Hilbert-space test vector.
-/

 public section

open Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A bounded sequence in a separable real Hilbert space has a weakly convergent
subsequence. -/
theorem exists_hilbert_weak_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (v : ℕ → H) (R : ℝ) (hv : ∀ j, ‖v j‖ ≤ R) :
    ∃ (u : H) (ν : ℕ → ℕ), StrictMono ν ∧
      ∀ w : H, Tendsto (fun j => inner ℝ (v (ν j)) w)
        atTop (nhds (inner ℝ u w)) := (Parabolic.Dirichlet.exists_strictMono_tendsto_inner_of_norm_le v R hv)


end HypoellipticAleksandrov.KineticAleksandrov
