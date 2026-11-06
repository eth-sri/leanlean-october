module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import MathCollab.Density.Stronger.DyadicMoment
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025

theorem exists_dyadic_cutoff {X : ℝ} (hX : 1 ≤ X) :
    ∃ M : ℕ, X ≤ (2:ℝ)^M ∧ (2:ℝ)^M ≤ 2*X :=
  MathCollab.Density.Stronger.exists_dyadic_cutoff hX

theorem exists_dyadic_count_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, ((M:ℝ)+1)^2 ≤ D*((2:ℝ)^M)^ε :=
  MathCollab.Density.Stronger.exists_dyadic_count_sq_le_rpow hε

end TaoTrudgianYang2025
