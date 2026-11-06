module
public import WrittenDensity.UniformModulus

@[expose] public section


namespace Montgomery.WrittenDensity
open MathCollab.Density
section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε



/- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_oct2_mixed_4  :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22) ≤ σ → σ ≤ (23/26) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((24+-24*σ)/(-11+30*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(19/22)) (b:=(23/26)) (K:=457)
    (f:=fun σ : ℝ => ((24+-24*σ)/(-11+30*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=24) (b:=-24) (c:=-11) (d:=30)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((24+-24*σ)/(-11+30*σ)) ε
    simpa using source_oct2_mixed_4 hlo hhi hε
  · exact hε


end



