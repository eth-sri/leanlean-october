module
public import GuthMaynard.Improvement.UpperTypeICount
public import GuthMaynard.Improvement.UpperCurveLargeValues

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

theorem upper_curve_typeI_separated_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ t₀ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(((9/4)*(1-σ))+ε) :=
  typeI_separated_count_of_large_values (9/4) upper_curve_large_values hε

theorem upper_curve_typeI_zero_slab_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(((9/4)*(1-σ))+ε) := by
  obtain ⟨C,hC,hcount⟩ := upper_curve_typeI_separated_count hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with H hh
  intro σ R hσ hσ' hR hcard hsep hlarge
  apply hh σ H R hσ hσ' hcard hsep
  intro ρ hρ
  obtain ⟨hz,hβ,hγ,hγ'⟩ := mem_zetaZeroFinset.mp (hR hρ)
  exact ⟨hβ,hz.2.2.le,⟨hγ,by linarith⟩,hlarge ρ hρ⟩

end GuthMaynard.Improvement
