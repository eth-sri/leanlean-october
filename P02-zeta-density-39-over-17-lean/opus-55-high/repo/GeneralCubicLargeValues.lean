module
public import FiniteCenteredCubic
public import GeneralCenteredMixedTrace
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The full cubic large-value inequality with the actual finite signed
amplifier, discrete cubic and improved mixed trace all proved. E is the
literal closed-boundary quadruple count, not an assumed energy bound. -/
theorem finite_cubic_large_value_general (w : MathCollab.Density.ComparisonCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → T^((4:ℝ)/5) ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^3*V^6 ≤ C*T^η*((N*L)^3+
        (N^4*T^2/L)*(W.card:ℝ)*Real.sqrt (W.card:ℝ)+
        N^4*T*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ)+
        N^4*adjacentCenteredBudget K T L W.card) := by
  have hδ : 0 < η/2 := by positivity
  pm_69 A hA hamp finite_signed_amplified_moment w hδ
  pm_69 B hB hcubic centered_matrix_cubic_bound w.toReflectionCutoff hδ
  pm_114 D hD hmix centered_mixed_trace_general w.toReflectionCutoff hK hδ
  refine ⟨A*(1+B+D),by positivity,?_⟩
  intro T t₀ N L hT hN hNL hLl hLu a ha W V hV hW hlarge hsep
  pm_4572
  pm_4498
  pm_432
  have hm := hmix T t₀ L (by linarith) hL1 W hW hsep
  have hm' : ‖Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
      cutoffCenteredMatrix w.toReflectionCutoff L W^2)‖ ≤ D*T^(η/2)*L*adjacentCenteredBudget K T L W.card := by
    simpa only [pow_two,mul_assoc] using hm
  pm_2721
  let X := (N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
    N^4*T*Real.sqrt R*Real.sqrt E+N^4*adjacentCenteredBudget K T L R
  pm_2722 hR0 hE0
  have hbudget : 0 ≤ adjacentCenteredBudget K T L R :=
    adjacentCenteredBudget_nonneg K hTp.le hLp.le hR0
  pm_4556
  pm_966 hTe hT1
  pm_199 hp T η hTp
  have hsum : (N*L)^3+(N^4/L)*
      ((Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
        (Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
          cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re) ≤
      (1+B+D)*T^(η/2)*X := by
    calc
      _ ≤ (N*L)^3+(N^4/L)*(B*T^(η/2)*(T^2*R*Real.sqrt R+T*L*Real.sqrt R*Real.sqrt E)+
          D*T^(η/2)*L*adjacentCenteredBudget K T L R) := by
        pm_789
      _ ≤ T^(η/2)*(N*L)^3+(N^4/L)*(B*T^(η/2)*(T^2*R*Real.sqrt R+T*L*Real.sqrt R*Real.sqrt E)+
          D*T^(η/2)*L*adjacentCenteredBudget K T L R) := by
        pm_790
      _ = T^(η/2)*((N*L)^3+B*((N^4*T^2/L)*R*Real.sqrt R+
          N^4*T*Real.sqrt R*Real.sqrt E)+D*(N^4*adjacentCenteredBudget K T L R)) := by field_simp; ring
      _ ≤ (1+B+D)*T^(η/2)*X := by
        pm_350
        have h₃ : 0 ≤ N^4*adjacentCenteredBudget K T L R := by positivity
        pm_192
  pm_227


end Montgomery.RationalMoment
