module
public import DashedInitialParameters

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Exact original TTY4 target tail budgets on its full requested interval. -/
theorem tty4_full_target_tail_budgets {σ : ℝ}
    (hl : 163/198 ≤ σ) (_hr : σ ≤ 7873/9370) :
    let a : ℝ := 31544/(107010*σ-33609)
    1/8 < (3*a/4)*(σ-1/2) ∧
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(914/1739:ℝ)/(3316/8695)-(4+(2+4*(914/1739))/(3316/8695))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 107010*σ-33609 := by linarith
  refine ⟨fraction_detector_threshold hd (by linarith),?_⟩
  rw [show (1:ℝ)+(914/1739)/(3316/8695)=3943/1658 by norm_num,
    show (4:ℝ)+(2+4*(914/1739))/(3316/8695)=24467/1658 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

end Montgomery.RationalMoment
