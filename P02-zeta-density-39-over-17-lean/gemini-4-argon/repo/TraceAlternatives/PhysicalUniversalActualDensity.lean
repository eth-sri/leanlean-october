module
public import LaterPairs.PhysicalPairLongZeroCount
public import TraceAlternatives.PhysicalUniversalShortZeroCount
public import PairActualDensity
public import RightSolidTailBudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025 GuthMaynard.Improvement

theorem density_of_pair_universal_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a)
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) :=
  density_of_pair_of_short hpair hk hw hfirst hsecond hε (by norm_num)
    fun η δ hη hηsmall _ _ => smoothShortZeroCount_universal_bound hw hc hη
      (by linarith) (by linarith [hw.a_high]) δ

theorem density_of_pair_universal_fraction {k l σ P D ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε)
    (hk : 0 < k := by norm_num)
    (hσ : 4/5 ≤ σ := by linarith) (hσ1 : σ < 1 := by linarith) (hd : 0 < 3*D := by linarith)
    (hal : 3*D ≤ 2*P := by linarith) (hah : 3*P < 2*(3*D) := by linarith)
    (hth : 3*D/2 < 3*P*(σ-1/2) := by linarith)
    (hlow : 51*(3*D) ≤ 100*P*(7*σ/2-2) := by linarith)
    (hm : ∀ j : Fin 3, ∀ i : Fin 5,
      0 ≤ (2-universalTraceB j-universalTraceG j-universalTraceD j*gmEnergyR i)*3*P*(1-σ)-
        (universalTraceA j+universalTraceD j*gmEnergyV i)*(3*D)+
        ((4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
          universalTraceD j*gmEnergyU i)*P := by
      intro j i; fin_cases j <;> fin_cases i <;>
        norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,
          gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
        linarith)
    (hfirst : 4*(3*D) ≤ P*(6*σ+3) := by linarith)
    (hsecond : (1+l/k)*(3*D) ≤ P*(3*(1-σ)+(3*(4+(2+4*l)/k)/4)*(σ-1/2)) := by norm_num; nlinarith) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(P*(1-σ)/D+ε) := by
  have hw : PhysicalDetectorWindow σ (P/(3*D)) := ⟨by linarith, hσ1,
    (le_div_iff₀ hd).mpr (by linarith), (div_lt_iff₀ hd).mpr (by linarith), by
      rw [show (3*(P/(3*D))/4)*(σ-1/2) = 3*P*(σ-1/2)/(4*(3*D)) by field_simp]
      exact (lt_div_iff₀ (by positivity)).mpr (by linarith)⟩
  have hc := universalCountWindow_of_fraction hσ hσ1 hd hal hah hlow hm
  obtain ⟨hb1, hb2⟩ := tail_budgets_of_fraction hd hfirst hsecond
  have hh := density_of_pair_universal_window hpair hk hw hc hb1 hb2 hε
  have he : 3*(P/(3*D))*(1-σ) = P*(1-σ)/D := by
    have : D ≠ 0 := by linarith
    field_simp
  simpa only [he] using hh
