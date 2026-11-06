module
public import NativeBHBPeakTails
public import PairActualDensity
public import RightSolidTailBudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

theorem density_of_pair_fraction {k l σ P D ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε)
    (hk : 0 < k := by norm_num) (hlog : 2+4*l/k ≤ 7 := by norm_num)
    (hs1 : 7/9 ≤ σ := by linarith) (hs2 : σ < 1 := by linarith) (hD : 0 < 3*D := by linarith)
    (hal : 3*D ≤ 2*P := by linarith) (hah : 3*P < 2*(3*D) := by linarith)
    (hf1 : 6*D ≤ P*(3*σ+1) := by linarith) (hf2 : 3*D ≤ P*(11*σ-7) := by linarith)
    (hth : 3*D/2 < 3*P*(σ-1/2) := by linarith)
    (hfirst : 4*(3*D) ≤ P*(6*σ+3) := by linarith)
    (hsecond : (1+l/k)*(3*D) ≤ P*(3*(1-σ)+(3*(4+(2+4*l)/k)/4)*(σ-1/2)) := by nlinarith) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(P*(1-σ)/D+ε) := by
  have hw : QuadraticWindow σ (P/(3*D)) := ⟨by linarith, hs2,
    (le_div_iff₀ hD).mpr (by linarith), (div_lt_iff₀ hD).mpr (by linarith),
    by rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hD).mpr (by linarith),
    by rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hD).mpr (by linarith)⟩
  have hth' : 1/8 < (3*(P/(3*D))/4)*(σ-1/2) := by
    rw [show (3*(P/(3*D))/4)*(σ-1/2) = 3*P*(σ-1/2)/(4*(3*D)) by field_simp]
    exact (lt_div_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨hb1, hb2⟩ := tail_budgets_of_fraction hD hfirst hsecond
  have hh := density_of_pair_tail_window hpair hk hlog hw hs1 hth' hb1 hb2 hε
  have he : 3*(P/(3*D))*(1-σ) = P*(1-σ)/D := by
    have : D ≠ 0 := by linarith
    field_simp
  simpa only [he] using hh

theorem density_right_solid_first {σ ε : ℝ}
    (hl : 7/9 ≤ σ) (hr : σ ≤ 29359/37574) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(11*σ-7)+ε) :=
  density_of_pair_fraction exponentPair_BHB10 hε

theorem density_right_solid_second {σ ε : ℝ}
    (hl : 29359/37574 ≤ σ) (hr : σ ≤ 1015/1294) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(4744*(1-σ)/(4870*σ-1283)+ε) :=
  density_of_pair_fraction exponentPair_BHB10 hε

theorem density_right_solid_third {σ ε : ℝ}
    (hl : 1015/1294 ≤ σ) (hr : σ ≤ 353/447) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6154*(1-σ)/(6354*σ-1693)+ε) :=
  density_of_pair_fraction exponentPair_BHB9 hε

theorem density_right_solid_fourth {σ ε : ℝ}
    (hl : 353/447 ≤ σ) (hr : σ ≤ 467/586) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3782*(1-σ)/(3936*σ-1065)+ε) :=
  density_of_pair_fraction exponentPair_BHB8 hε

theorem density_dashed_first {σ ε : ℝ}
    (hl : 467/586 ≤ σ) (hr : σ ≤ 289/358) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(2168*(1-σ)/(2282*σ-631)+ε) :=
  density_of_pair_fraction exponentPair_BHB7 hε

theorem density_dashed_second {σ ε : ℝ}
    (hl : 289/358 ≤ σ) (hr : σ ≤ 163/198) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(566*(1-σ)/(606*σ-173)+ε) :=
  density_of_pair_fraction exponentPair_BHB6 hε

