module
public import DensityStrip.Low
public import GuthMaynard.Improvement.ShortWindowLargeValues
public import TwoTermWindowParameters
public import TwoTermLargeValues
public import AdjacentWindowParameters
public import AdjacentLargeValues
public import ThirdWindowParameters
public import ThirdLargeValues

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter MathCollab.Density GuthMaynard.Improvement Montgomery.RationalMoment
namespace DensityStrip

private theorem uniform_window {s a p k e : ℝ} (h :
  ∃ C : ℝ, 0<C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
    2 ≤ T → 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+e) →
    (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) → oneSeparated W →
    (∀ t ∈ W, N^s*T^(-2*e) ≤ ‖boundedPolynomial N b t‖) → (W.card:ℝ) ≤ C*T^(p+k*e)) : WindowCount s a p k e := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
  exact fun N b W => h T N T b W hT

theorem short_density {σ ε : ℝ} (hl : 9/13 ≤ σ) (hr : σ ≤ 5/7) (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → (zetaDensityCount σ T:ℝ) ≤ C*T^(shortDensityExponent σ+ε) := by
  obtain ⟨ha,ha',_⟩ := short_density_scale_bounds hl hr
  apply low_density (a:=shortDensityA σ) (by linarith) (by linarith) (by linarith) (by linarith) ?_ (by norm_num : (5:ℝ) ≤ 10) ?_ he
  · unfold shortDensityExponent
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith only [mul_nonneg (show 0≤1-σ by linarith) (show 0≤6-7*σ by linarith)]
  · intro e he he'
    obtain ⟨C,hC,h⟩ := short_window_large_values he he'
    exact uniform_window ⟨C,hC,fun T N t b W => h σ T N t b W hl hr⟩

theorem two_term_density_first {σ ε : ℝ}
    (hσ : 12/17 ≤ σ) (hσ' : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6*(1-σ)/(8*σ-3)+ε) := by
  have hw := two_term_window_first σ hσ hσ'
  refine low_density (k:=18) ?_ ?_ ?_ ?_ ?_ (by norm_num) (fun _ he he' => uniform_window (two_term_full_window_large_values hw he he')) hε
  all_goals linarith only [hw.sigma_low,hw.sigma_high,hw.a_low,hw.a_high,hw.typeII]

theorem adjacent_density_second {σ ε : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 113/153) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(12*(1-σ)/(9*σ-1)+ε) := by
  have hw := adjacent_window_second σ hσ hσ'
  refine low_density (k:=18) ?_ ?_ ?_ ?_ ?_ (by norm_num) (fun _ he he' => uniform_window (adjacent_full_window_large_values hw he he')) hε
  all_goals linarith only [hw.sigma_low,hw.sigma_high,hw.a_low,hw.a_high,hw.typeII]

theorem third_density_segment {σ ε : ℝ}
    (hσ : 113/153 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(255*(1-σ)/(153*σ+7)+ε) := by
  have hw := third_window_parameters σ hσ hσ'
  refine low_density (k:=18) ?_ ?_ ?_ ?_ ?_ (by norm_num) (fun _ he he' => uniform_window (third_full_window_large_values hw he he')) hε
  all_goals linarith only [hw.sigma_low,hw.sigma_high,hw.a_low,hw.a_high,hw.typeII]

end DensityStrip
