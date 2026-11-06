module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.OriginalTimePlateau

/-!
# Reverse-time scalar plateau cutoffs

This module specializes the common smooth time plateau to a reverse-time test.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Function Set

private theorem timePlateau_outer_subset_reverseTime
    {T a d : ℝ} (ha0 : 0 ≤ a) (hdT : d ≤ T) :
    Ioo a d ⊆ reverseTimeOpenInterval T := by
  intro tau htau
  exact ⟨lt_of_le_of_lt ha0 htau.1, lt_of_lt_of_le htau.2 hdT⟩

/-- A smooth reverse-time test with values in `[0, 1]`, a closed inner
plateau, and topological support strictly inside the prescribed outer interval. -/
theorem exists_reverseTimeScalarTest_plateau
    (T a b c d : ℝ)
    (ha0 : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (hdT : d ≤ T) :
    ∃ eta : ReverseTimeScalarTest T,
      (∀ tau : ℝ, 0 ≤ eta tau) ∧
      (∀ tau : ℝ, eta tau ≤ 1) ∧
      (∀ tau ∈ Set.Icc b c, eta tau = 1) ∧
      tsupport (eta : ℝ → ℝ) ⊆ Set.Ioo a d := by
  let eta : ReverseTimeScalarTest T :=
    { toFun := timePlateau a b c d
      contDiff' := timePlateau_contDiff a b c d
      hasCompactSupport' := timePlateau_hasCompactSupport hab hcd
      tsupport_subset' := (timePlateau_tsupport_subset_outer hab hcd).trans
        (timePlateau_outer_subset_reverseTime ha0 hdT) }
  refine ⟨eta, timePlateau_nonneg a b c d, timePlateau_le_one a b c d, ?_, ?_⟩
  · intro tau htau
    exact timePlateau_eq_one_on hab hbc hcd htau
  · exact timePlateau_tsupport_subset_outer hab hcd

end HypoellipticAleksandrov.Parabolic.Dirichlet
