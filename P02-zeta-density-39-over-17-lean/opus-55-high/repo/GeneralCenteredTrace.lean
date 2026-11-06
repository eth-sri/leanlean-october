module
public import GeneralCenteredReflection
import WeylPort.Analytic.RealLaplace

public section

open Finset MeasureTheory
namespace Montgomery.RationalMoment

section
variable (w : MathCollab.Density.ReflectionCutoff) {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η)
include w K hK η hη
/-- The full discrete centered energy; near-diagonal terms and shell-count
losses have been discharged. Fixed reflected-length factors are absorbed
in the constant; the exact undilated length T/L governs the hypothesis. -/
theorem centered_energy_general :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        C*T^η*adjacentCenteredBudget K T L W.card := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨C,B,hC,hB,hshell⟩ := centered_shell_general w hK (A := 2) (by norm_num) hδ
  pm_4245
  pm_4497
  refine ⟨1+B₀^2+D*(C+B),by positivity,?_⟩
  intro T t₀ L hT hL W hW hsep
  pm_4240
  have hX : 0 ≤ adjacentCenteredBudget K T L W.card :=
    adjacentCenteredBudget_nonneg K (by linarith) (by linarith) (Nat.cast_nonneg _)
  have hfirst := adjacentCenteredBudget_first K (R:=(W.card:ℝ)) (by linarith : 0 ≤ T) (by linarith : 0 ≤ L) (Nat.cast_nonneg _)
  have hbase : B₀^2*(W.card:ℝ)^2 ≤ B₀^2*T^η*adjacentCenteredBudget K T L W.card := by
    have hLR : (W.card:ℝ)^2 ≤ L*(W.card:ℝ)^2 := by nlinarith [sq_nonneg (W.card:ℝ)]
    have hh : (W.card:ℝ)^2 ≤ adjacentCenteredBudget K T L W.card := hLR.trans hfirst
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg B₀)
    have hh'' := mul_le_mul_of_nonneg_left hη1 (mul_nonneg (sq_nonneg B₀) hX)
    nlinarith
  by_cases hYT : Y ≤ T
  · obtain ⟨J,hcover,hmin,hJ⟩ := reflection_shell_count hT hL hYT
    pm_4243
    have hs (j : ℕ) (hj : j ∈ range J) :
        (∑ p ∈ (W ×ˢ W).filter
          (fun p => (2:ℝ)^j*Y ≤ |p.1-p.2| ∧ |p.1-p.2| < (2:ℝ)^(j+1)*Y),
          ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) ≤
        (C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card := by
      pm_4246
      have hh := hshell T t₀ L H hT hL hHp hHT.le W hW hsep
      pm_4241
      calc
        _ ≤ C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*(W.card:ℝ)^2*L^(2-2*(2:ℝ)) := hh
        _ ≤ C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*(W.card:ℝ)^2*L := by gcongr
        _ = C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*(L*(W.card:ℝ)^2) := by ring
        _ ≤ C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*adjacentCenteredBudget K T L W.card := by gcongr
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd1 (mul_nonneg hB hX)]
    pm_4244
    calc
      _ = ∑ p ∈ W ×ˢ W, ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2 := (sum_product _ _ _).symm
      _ = _ := he
      _ ≤ B₀^2*(W.card:ℝ)^2+∑ _j ∈ range J, (C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card :=
        add_le_add hnearSum (sum_le_sum hs)
      _ = B₀^2*(W.card:ℝ)^2+(J:ℝ)*((C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card) := by simp
      _ ≤ B₀^2*T^η*adjacentCenteredBudget K T L W.card+(D*T^(η/2))*((C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card) := by gcongr
      _ = (B₀^2+D*(C+B))*T^η*adjacentCenteredBudget K T L W.card := by rw [← hpow]; ring
      _ ≤ _ := by gcongr; linarith
  pm_4242

/-- The actual squared-cutoff centered matrix satisfies the improved
quadratic trace bound, with no analytic estimate among the premises. -/
theorem centered_trace_general :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W)‖ ≤
        C*T^η*adjacentCenteredBudget K T L W.card := by
  obtain ⟨C,hC,hbound⟩ := centered_energy_general (reflectionSquare w) hK hη
  pm_417 hL
end

end Montgomery.RationalMoment
