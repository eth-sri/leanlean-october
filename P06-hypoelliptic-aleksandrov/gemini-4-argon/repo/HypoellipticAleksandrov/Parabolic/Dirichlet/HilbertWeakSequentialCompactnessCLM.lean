module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactness
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

/-! Sequential weak compactness against continuous linear functionals in separable real Hilbert
spaces. -/

@[expose] public section

open Filter Function Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence converging against every continuous linear functional. -/
theorem exists_strictMono_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell v)) := by
  obtain ⟨v, φ, hφ, hinner⟩ : ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ z : H,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ v z)) := by
    let f : ℕ → WeakDual ℝ H := fun n =>
      StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
    have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ H) R := by
      intro n
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      change ‖InnerProductSpace.toDual ℝ H (u n) - 0‖ ≤ R
      simpa using hu n
    obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ :=
      (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
    let v : H :=
      (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
    refine ⟨v, φ, hφ, fun z => ?_⟩
    simpa [f, v, Function.comp_def] using
      ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim
  refine ⟨v, φ, hφ, fun ell => ?_⟩
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  simp_rw [← InnerProductSpace.toDual_symm_apply]
  simpa only [z, real_inner_comm] using hinner z

end HypoellipticAleksandrov.Parabolic.Dirichlet
