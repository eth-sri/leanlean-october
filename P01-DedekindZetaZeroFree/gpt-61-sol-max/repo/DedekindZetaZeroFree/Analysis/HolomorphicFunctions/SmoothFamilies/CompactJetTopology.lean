module

public import Mathlib

public import DedekindZetaZeroFree.Analysis.Sobolev.LocalEmbeddingAndSmoothRepresentatives

@[expose] public section


noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.Raw

open MeasureTheory KPContLocalNorm KPContLocalCubeEmbedding

def SmoothPowerSeriesOn {n : ℕ} (B : LocalBall n) (z₀ : ℂ) (ρ : ℝ)
    (coeff : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ)  :=
  (∀ q, ContDiffOn ℝ (⊤ : ℕ∞) (coeff q) B.carrier) ∧
  (∀ z ∈ Metric.ball z₀ ρ, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier) ∧
  ∀ (K : Set (Space n)), IsCompact K → K ⊆ B.carrier →
    ∀ m : ℕ, ∀ r : ℝ, 0 ≤ r → r < ρ → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
        ∀ α : MultiIndex n m, ∀ x : K,
          ‖coordinateDerivative α
              (fun y => (∑ q ∈ Finset.range M, (z - z₀) ^ q * coeff q y) - f z y) x‖ < ε

section
variable {n : ℕ} (B : LocalBall n)
    (f : ℂ → Space n → ℂ) (O : Set ℂ)
include n B f O
def SmoothCompactOpenHolomorphicOn    :=
  ∀ z₀ ∈ O, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z₀ ρ ⊆ O ∧
    ∃ coeff : ℕ → Space n → ℂ, SmoothPowerSeriesOn B z₀ ρ coeff f

def JetContinuousOn    :=
  ∀ z₀ ∈ O, ∀ K : Set (Space n), IsCompact K → K ⊆ B.carrier →
    ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ O, dist z z₀ < δ → ∀ α : MultiIndex n m, ∀ x : K,
        ‖coordinateDerivative α (fun y => f z y - f z₀ y) x‖ < ε
end


end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.Raw

end
