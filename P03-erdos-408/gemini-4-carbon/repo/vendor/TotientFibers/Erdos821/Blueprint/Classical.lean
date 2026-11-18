module

public import Erdos821.Blueprint.Analytic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Package P1. Each proposition spells out the needed uniformity. -/

@[expose] public section

noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint
open Analytic




def HarmonicCharacters : Prop :=
  ∀ c C B A : ℝ, 0 < c → 0 < C → 0 < B → 0 < A →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (lo hi t : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
        Real.exp (L x ^ c) ≤ lo → lo ≤ hi → hi ≤ x ^ C →
        1 ≤ r → (r : ℝ) ≤ L x ^ B → χ ≠ 1 → |t| ≤ L x ^ B →
        ‖∑ p ∈ ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime),
          χ (p : ZMod r) * mellin p t / (p : ℂ)‖ ≤ K * L x ^ (-A)


def MeanSquares : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ) (a : ℕ → ℂ) (lo hi : ℝ), lo ≤ hi →
    (∫ t : ℝ in lo..hi, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      K * (hi - lo + Y * Real.log (2 * Y)) * sqNorm (Finset.Icc 1 Y) a ∧
    ∀ E : Finset ℝ, (∀ t ∈ E, lo ≤ t ∧ t ≤ hi) →
      (∀ t ∈ E, ∀ u ∈ E, t ≠ u → 1 ≤ |t - u|) →
      (∑ t ∈ E, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
        K * (hi - lo + 1 + Y * Real.log (2 * Y)) * Real.log (2 * Y) ^ 2 *
          sqNorm (Finset.Icc 1 Y) a



/-- A Fourier coefficient measure is an explicit factorization, not an abstract oracle.
The derivatives can grow by a fixed power per order; the frequency cutoff is fixed
before the requested saving A. -/
def FourierSeparation : Prop :=
  ∀ b : ℕ, ∀ C R : ℝ, 0 < C → 0 < R → ∀ bounds : ℕ → ℝ,
    (∀ j, 0 ≤ bounds j) → ∃ C' K : ℝ, C < C' ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧
      ∀ᶠ x : ℝ in atTop, ∀ F : (Fin b → ℝ) → ℂ,
        ContDiff ℝ ∞ F → Function.support F ⊆ Metric.closedBall 0 R →
        (∀ j y, ‖iteratedFDeriv ℝ j F y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
        ∃ a : (Fin b → ℝ) → ℂ,
          Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
          (∀ y, F y = ∫ ξ, a ξ * e (∑ i, ξ i * y i)) ∧
          (∫ ξ in {ξ : Fin b → ℝ | L x ^ C' < ‖ξ‖}, ‖a ξ‖) ≤ KA * L x ^ (-A)


-- `classical_inputs` is proved in `Erdos821/P1/ClassicalInputs.lean`.

end Erdos821.Blueprint
