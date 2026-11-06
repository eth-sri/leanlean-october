module
public import RightSolidTailBudgets
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem dashed_first_quadratic_window {σ : ℝ}
    (hl : 4/5 ≤ σ) (hr : σ ≤ 289/358) :
    QuadraticWindow σ (2168/(6846*σ-1893)) := by
  pm_7484
  pm_2856

theorem dashed_second_quadratic_window {σ : ℝ}
    (hl : 289/358 ≤ σ) (hr : σ ≤ 163/198) :
    QuadraticWindow σ (566/(1818*σ-519)) := by
  pm_7485
  pm_2856

theorem fraction_detector_threshold {σ n d : ℝ} (hd : 0 < d)
    (hm : d/2 < 3*n*(σ-1/2)) :
    1/8 < (3*(n/d)/4)*(σ-1/2) := by
  have he : (3*(n/d)/4)*(σ-1/2)=3*n*(σ-1/2)/(4*d) := by field_simp
  rw [he]
  pm_5929 lt_div_iff₀ d
  linarith

theorem dashed_first_tail_budgets {σ : ℝ}
    (hl : 4/5 ≤ σ) (_hr : σ ≤ 289/358) :
    let a : ℝ := 2168/(6846*σ-1893)
    1/8 < (3*a/4)*(σ-1/2) ∧
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(41/81:ℝ)/(85/189)-(4+(2+4*(41/81))/(85/189))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  pm_7484
  refine ⟨fraction_detector_threshold hd (by linarith),?_⟩
  pm_2719
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

theorem dashed_second_tail_budgets {σ : ℝ}
    (hl : 289/358 ≤ σ) (_hr : σ ≤ 163/198) :
    let a : ℝ := 566/(1818*σ-519)
    1/8 < (3*a/4)*(σ-1/2) ∧
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(51/100:ℝ)/(13/30)-(4+(2+4*(51/100))/(13/30))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  pm_7485
  refine ⟨fraction_detector_threshold hd (by linarith),?_⟩
  rw [show (1:ℝ)+(51/100)/(13/30)=283/130 by norm_num,
    show (4:ℝ)+(2+4*(51/100))/(13/30)=866/65 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith
end Montgomery.RationalMoment
