module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaInverseJetBounds

@[expose] public section

/-!
# Uniform all-order model errors for the actual Legendre phase

For each fixed derivative order, one explicit finite expression yields a
bound depending only on sigma and that order. The phase and slope point
are arbitrary within the original model assumptions and common slope domain.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def inverseJetMagnitudeBudget (σ : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), inverseJetMagnitude σ j

theorem inverseJetMagnitudeBudget_nonneg {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    0 ≤ inverseJetMagnitudeBudget σ K :=
  Finset.sum_nonneg fun j _ => inverseJetMagnitude_nonneg hσ j

theorem inverseJetMagnitude_le_budget {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    inverseJetMagnitude σ j ≤ inverseJetMagnitudeBudget σ K :=
  Finset.single_le_sum (fun k _ => inverseJetMagnitude_nonneg hσ k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

theorem approximateModelPhase_tolerance_nonneg
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    0 ≤ δ :=
  (norm_nonneg _).trans (hF.2 0 (Nat.zero_le P) ⟨1, by norm_num [phaseInterval]⟩)

end TaoTrudgianYang2025
