module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

@[expose] public section

namespace Light.Sec4.RatParams

/-- Change only the threshold, not the two ratios used to set the parameters. -/
def withThreshold (G : RatParams) (m : ℕ) (hm : 1 ≤ m) : RatParams :=
  { G with m₀ := m, hm₀ := hm }

noncomputable abbrev realC (G : RatParams) : ℝ := (G.a : ℝ) / G.b
noncomputable abbrev realTheta (G : RatParams) : ℝ := (G.p : ℝ) / G.q

theorem ten_lt_realC (G : RatParams) : 10 < G.realC :=
  (lt_div_iff₀ (by exact_mod_cast G.hb)).2 (by exact_mod_cast G.hc)

theorem realTheta_bounds (G : RatParams) : 0 < G.realTheta ∧ G.realTheta < 0.9 := by
  have hq : (0 : ℝ) < G.q := by exact_mod_cast G.hq
  have h : (10 : ℝ) * G.p < 9 * G.q := by exact_mod_cast G.hθ
  exact ⟨div_pos (by exact_mod_cast G.hp) hq, (div_lt_iff₀ hq).2 (by linarith)⟩

end Light.Sec4.RatParams
