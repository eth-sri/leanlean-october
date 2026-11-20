module
public import TraceAlternatives.PhysicalUniversalActualDensity
public import RightSolidTailBudgets
public import LaterPairs.NativeSharpRows78
public import LaterPairs.NativeSharpRow5Suffix
public import LaterPairs.NativeTTY3

/-! All the later windows can use the same universal second-moment trace.
Only the critical-tail exponent pair and the affine length vary. -/
@[expose] public section
noncomputable section
open MathCollab.Density TaoTrudgianYang2025 Montgomery.RationalMoment
open Montgomery.RationalMoment.RightDetector Montgomery.RationalMoment.RightDetector.Physical
namespace DensityStrip

private theorem row {s e k l P d : ℝ} (pair : ExponentPair k l) (hk : 0 < k)
    (hl : 4/5 ≤ s) (hr : s < 1) (he : 0 < e) (hd : 0 < d) (ha : d ≤ 2*P) (ha' : 3*P < 2*d)
    (hθ : d < 6*P*(s-1/2)) (hf : 4*d ≤ P*(6*s+3))
    (hs : (1+l/k)*d ≤ P*(3*(1-s)+(3*(4+(2+4*l)/k)/4)*(s-1/2)))
    (hLow : 51/100*d ≤ P*(7*s/2-2))
    (hm : ∀ j : Fin 3, ∀ i : Fin 5, 0  ≤ 
      (2-universalTraceB j-universalTraceG j-universalTraceD j*gmEnergyR i)*3*P*(1-s)-
        (universalTraceA j+universalTraceD j*gmEnergyV i)*d+
        ((4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*s-3+
          universalTraceB j-universalTraceD j*gmEnergyU i)*P) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount s T:ℝ) ≤ C*T^((3*P/d)*(1-s)+e) := by
  have hal : 1/2 ≤ P/d := (le_div_iff₀ hd).mpr (by linarith)
  have hah : P/d < 2/3 := (div_lt_iff₀ hd).mpr (by linarith)
  obtain ⟨ht₁,ht₂⟩ := tail_budgets_of_fraction hd hf hs
  rw [mul_div_assoc]
  apply density_of_pair_universal_window pair hk _ _ ht₁ ht₂ he
  · refine ⟨by linarith,hr,hal,hah,?_⟩
    field_simp; linarith only [hθ]
  refine ⟨hl,hr,hal,hah,?_,?_⟩
  · intro x hx j i
    let m := (4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*s-3+
      universalTraceB j-universalTraceD j*gmEnergyU i
    have hn : 0 ≤ m := by
      fin_cases j  <;> fin_cases i  <;> norm_num [m,universalTraceB,universalTraceD,gmEnergyU,gmEnergyW]  <;> linarith
    have hbase : 0 ≤ universalTraceEnergyMargin s (P/d) (P/d) j i := by
      unfold universalTraceEnergyMargin
      field_simp
      linarith only [hm j i]
    unfold universalTraceEnergyMargin at hbase ⊢
    linarith only [hbase,mul_le_mul_of_nonneg_left hx hn]
  · intro x hx
    have hbase : 1/100 ≤ universalLowMargin s (P/d) (P/d) := by
      unfold universalLowMargin; field_simp; linarith only [hLow]
    unfold universalLowMargin at hbase ⊢
    linarith only [hbase,mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 5*s-7/2)]

macro "check_row " s:term ", " pair:term ", " n:term ", " d:term ", " he:term : tactic => `(tactic|
  (convert row (s:=$s) (P:=$n/3) (d:=$d) $pair (by norm_num) (by linarith) (by linarith) $he ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1
   all_goals first | (ring_nf; done) | (norm_num  <;> linarith) |
     (intro j i; fin_cases j  <;> fin_cases i  <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR]  <;> linarith)))

theorem later₃ {σ ε : ℝ} (hl : 163/198 ≤ σ) (hr : σ ≤ 7873/9370) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((31544/(35670*σ-11203))*(1-σ)+ε) := by
  check_row σ, exponentPair_BTTY4, 31544, 35670*σ-11203, he

theorem later₄ {σ ε : ℝ} (hl : 7873/9370 ≤ σ) (hr : σ ≤ 2018/2375) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((1261710/(1447460*σ-465509))*(1-σ)+ε) := by
  check_row σ, exponentPair_BTTY3, 1261710, 1447460*σ-465509, he

theorem later₅ {σ ε : ℝ} (hl : 2018/2375 ≤ σ) (hr : σ ≤ 1959705/2298302) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((3066/(3616*σ-1215))*(1-σ)+ε) := by
  check_row σ, exponentPair_BATY2, 3066, 3616*σ-1215, he

theorem later₆ {σ ε : ℝ} (hl : 1959705/2298302 ≤ σ) (hr : σ ≤ 6482825/7570038) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((597962/(729216*σ-257415))*(1-σ)+ε) := by
  check_row σ, exponentPair_BATYnew2, 597962, 729216*σ-257415, he

theorem later₇ {σ ε : ℝ} (hl : 6482825/7570038 ≤ σ) (hr : σ ≤ 2905/3354) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((16504356/(20732766*σ-7623595))*(1-σ)+ε) := by
  check_row σ, exponentPair_BTTY2, 16504356, 20732766*σ-7623595, he

theorem later₈ {σ ε : ℝ} (hl : 2905/3354 ≤ σ) (hr : σ ≤ 7/8) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((2172/(2742*σ-1015))*(1-σ)+ε) := by
  check_row σ, exponentPair_BTTY1, 2172, 2742*σ-1015, he

theorem middle_left {σ ε : ℝ} (hl : 7/8 ≤ σ) (hr : σ ≤ 23/26) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((24/(30*σ-11))*(1-σ)+ε) := by
  check_row σ, exponentPair_BTTY1, 24, 30*σ-11, he

theorem middle_right {σ ε : ℝ} (hl : 23/26 ≤ σ) (hr : σ ≤ 17/19) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^((6/(σ+3))*(1-σ)+ε) := by
  check_row σ, exponentPair_BTTY1, 6, σ+3, he

end DensityStrip
