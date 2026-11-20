module

public import PottsDiscontinuity.Bethe.Theorem23
public import PottsDiscontinuity.SixVertex.Cor34Final

@[expose] public section

namespace PottsDiscontinuity.SixVertex

open Bethe

/-- Theorem 2.3 supplies a density-controlled Bethe state at `d₀`, and its Bethe eigenvalue
is the Perron root of the transfer block. -/
theorem cor34_final_exists_family_at_endpoint (r : ℕ) {d₀ : ℝ} (hd₀ : d₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      let n := N / 2 - r
      ∃ hn : 0 < n, ∃ hs : 2 * n ≤ N, ∃ p : Fin n → ℝ,
        ∃ hp : p ∈ S_n n,
        DiscreteBetheEquation d₀ N n p ∧
        densityNorm d₀ (rootStepError d₀ N p hn) ≤ K / N ∧
        parityEigenvalue N (Real.sqrt (2 - 2 * d₀)) p =
          (Lambda (Real.sqrt (2 - 2 * d₀)) N r : ℂ) := by
  obtain ⟨K, hK, N₀, hN₀, d₁, hd₀₁, _, hf⟩ := theorem23 r hd₀
  refine ⟨K, hK, N₀, hN₀, fun N hN hEven => ?_⟩
  obtain ⟨hn, hs, p, hp, hb, ha, ⟨P, hP, hP₀, hform⟩, hnorm⟩ := hf N hN hEven
  exact ⟨hn, hs, p d₀, hp d₀ le_rfl, hb d₀ le_rfl, hnorm d₀ le_rfl,
    cor34_final_at_endpoint hd₀ hd₀₁ ha hp hb hform hP.continuousAt hP₀ hn hs⟩

end PottsDiscontinuity.SixVertex
