module
public import DensityEnergyGM.SecondMomentSharp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem coefficient_one_difference_eq_ratio_second (M : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) =
      gmDiscreteRatioMoment 2 M W := by
  rw [gmDiscreteRatioMoment_eq_iterated,
    ← sourceCoefficientOne_differenceMoment_eq_gmR_ratioMoment]
  have hone : conjugateCoeffs (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) := by
    funext n
    exact star_one ℂ
  simp_rw [norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs, hone]

/-- Literal all-pairs ratio second moment, obtained from the proved sharp
difference estimate by the exact finite Gram identity. -/
theorem ratio_second_moment_sharp_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        gmDiscreteRatioMoment 2 M W ≤ C * T ^ ε *
          ((M : ℝ) ^ 2 * (discreteAdditiveEnergy W : ℝ) ^ (1 / 2 : ℝ) +
            (W.card : ℝ) * (discreteAdditiveEnergy W : ℝ) ^ (1 / 4 : ℝ) *
              ((M : ℝ) ^ (9 / 5 : ℝ) +
                T ^ (1 / 4 : ℝ) * (M : ℝ) ^ (6 / 5 : ℝ))) := by
  obtain ⟨C, T₀, hC, hT₀, h⟩ := actual_second_moment_sharp_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W hM hT hMT hSep hBase
  rw [← coefficient_one_difference_eq_ratio_second]
  exact h M T (fun _ => 1) W hM hT hMT (by simp) hSep hBase

end Montgomery.RationalMoment
