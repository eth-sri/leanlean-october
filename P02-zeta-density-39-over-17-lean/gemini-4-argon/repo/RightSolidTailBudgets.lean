module
public import DetectorPowerRange

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem tail_budgets_of_fraction {σ n d φ b : ℝ} (hd : 0 < d)
    (hfirst : 4*d ≤ n*(6*σ+3))
    (hsecond : φ*d ≤ n*(3*(1-σ)+(3*b/4)*(σ-1/2))) :
    1-6*((3*(n/d)/4)*(σ-1/2)) ≤ 3*(n/d)*(1-σ) ∧
    φ-b*((3*(n/d)/4)*(σ-1/2)) ≤ 3*(n/d)*(1-σ) := by
  have h1 : 4 ≤ (n/d)*(6*σ+3) := by rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hd).mpr hfirst
  have h2 : φ ≤ (n/d)*(3*(1-σ)+(3*b/4)*(σ-1/2)) := by rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hd).mpr hsecond
  exact ⟨by nlinarith, by nlinarith⟩

