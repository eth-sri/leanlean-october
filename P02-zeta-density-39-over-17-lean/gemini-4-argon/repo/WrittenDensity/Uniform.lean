module
public import WrittenDensity.UniformModulus

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density

theorem uniform_source_oct2_mixed_4 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22) ≤ σ → σ ≤ (23/26) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((24+-24*σ)/(-11+30*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(19/22)) (b:=(23/26)) (K:=457)
    (f:=fun σ : ℝ => ((24+-24*σ)/(-11+30*σ))) (by norm_num) (by norm_num)
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=24) (b:=-24) (c:=-11) (d:=30)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    exact source_oct2_mixed_4 hlo hhi hε
  · exact hε

theorem uniform_source_oct2_mixed_5 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26) ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((6+-6*σ)/(3+1*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(23/26)) (b:=1) (K:=25)
    (f:=fun σ : ℝ => ((6+-6*σ)/(3+1*σ))) (by norm_num) (by norm_num)
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=6) (b:=-6) (c:=3) (d:=1)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo _hhi ε _hε
    exact density_of_actual_zero (by linarith)
  · exact hε

