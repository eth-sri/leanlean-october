module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter
namespace GuthMaynard.Improvement

def cubicSmoothingWidth (q T η L K : ℝ) : ℝ := q*T^η/(L*K)

theorem cubic_smoothing_width_bounds {T η L K R q : ℝ}
    (hT : 1 ≤ T) (_hη : 0 ≤ η) (hLlow : T^((4:ℝ)/5) ≤ L)
    (_hLhigh : L ≤ T) (hK : 1 ≤ K) (hKR : K ≤ R)
    (hRU : R ≤ T^(1+η)/L) (hq : 1 ≤ q) :
    0 < cubicSmoothingWidth q T η L K ∧
    (cubicSmoothingWidth q T η L K)⁻¹ ≤ T ∧
    cubicSmoothingWidth q T η L K ≤ q*T^(η-(4:ℝ)/5) := by
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLlow
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have hH : 0 < T^η := Real.rpow_pos_of_pos hTp _
  have hLK : L*K ≤ T^(1+η) := by
    have hh := (le_div_iff₀ hLp).mp (hKR.trans hRU)
    nlinarith
  have hid : T^(1+η) = T*T^η := by rw [Real.rpow_add hTp,Real.rpow_one]
  have hbase : T^((4:ℝ)/5) ≤ L*K := by nlinarith
  refine ⟨by unfold cubicSmoothingWidth; positivity,?_,?_⟩
  · unfold cubicSmoothingWidth
    rw [inv_div]
    apply (div_le_iff₀ (mul_pos hqp hH)).mpr
    rw [hid] at hLK
    exact hLK.trans (mul_le_mul_of_nonneg_left (by nlinarith : T^η ≤ q*T^η) hTp.le)
  · unfold cubicSmoothingWidth
    calc
      _ ≤ q*T^η/T^((4:ℝ)/5) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hTp _) hbase
      _ = _ := by rw [Real.rpow_sub hTp]; ring

/-- One threshold works for every admissible L,K,R. The bounded-height
range is deliberately not removed from any global theorem. -/
theorem cubic_smoothing_width_eventually {η q δ : ℝ}
    (hη : 0 ≤ η) (hη1 : η < (4:ℝ)/5) (hq : 1 ≤ q) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T L K R : ℝ, T₀ ≤ T →
      T^((4:ℝ)/5) ≤ L → L ≤ T → 1 ≤ K → K ≤ R → R ≤ T^(1+η)/L →
      cubicSmoothingWidth q T η L K ≤ δ := by
  have ht : Tendsto (fun T : ℝ => q*T^(η-(4:ℝ)/5)) atTop (nhds 0) := by
    have hh := tendsto_rpow_neg_atTop (show 0 < (4:ℝ)/5-η by linarith)
    have hm : Tendsto (fun T : ℝ => q*T^(-((4:ℝ)/5-η))) atTop (nhds (q*0)) :=
      tendsto_const_nhds.mul hh
    simpa only [neg_sub,mul_zero] using hm
  have he : ∀ᶠ T : ℝ in atTop, q*T^(η-(4:ℝ)/5) < δ :=
    (tendsto_order.mp ht).2 δ hδ
  obtain ⟨T₀,h⟩ := eventually_atTop.mp he
  refine ⟨max 1 T₀,le_max_left _ _,?_⟩
  intro T L K R hT hLl hLu hK hKR hRU
  exact (cubic_smoothing_width_bounds ((le_max_left _ _).trans hT) hη hLl hLu hK hKR hRU hq).2.2.trans
    (h T ((le_max_right _ _).trans hT)).le

theorem cubic_box_sqrt_polynomial {R K M E : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hM : 0 ≤ M) (hE : 0 ≤ E) :
    Real.sqrt (R^2*K^4*M^2+R*K^3*E) ≤
      K*(R*K*M+Real.sqrt (R*K)*Real.sqrt E) := by
  have hs : (K*Real.sqrt (R*K)*Real.sqrt E)^2 = R*K^3*E := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hR hK),Real.sq_sqrt hE]
    ring
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hp : 0 ≤ (R*K^2*M)*(K*Real.sqrt (R*K)*Real.sqrt E) := by positivity
    nlinarith [sq_nonneg (R*K^2*M)]

/-- Common shell numerator, uniform over every K<=U. -/
theorem cubic_shell_sqrt_normalization {U K M E : ℝ}
    (hK : 1 ≤ K) (hKU : K ≤ U) (hM : 0 ≤ M) (hE : 0 ≤ E) :
    Real.sqrt (U^2*K^4*M^2+U*K^3*E) ≤ K*(U^2*M+U*Real.sqrt E) := by
  have hK0 : 0 ≤ K := by linarith
  have hU0 : 0 ≤ U := hK0.trans hKU
  have hUK : U*K ≤ U^2 := by nlinarith
  have hroot : Real.sqrt (U*K) ≤ U := (Real.sqrt_le_iff).mpr ⟨hU0,hUK⟩
  exact (cubic_box_sqrt_polynomial hU0 hK0 hM hE).trans (by gcongr)

/-- Exact affine half-exponent and dyadic exponent absorption, preserving
an independent restricted first-factor mass A. -/
theorem cubic_box_epsilon_absorption {T η α δ ε M E A L : ℝ}
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hbudget : δ+α/2+3*η ≤ ε) :
    T^δ*T^(α/2)*Real.sqrt A*(T^(3*η)*T^2*M+T^(2*η)*T*L*Real.sqrt E) ≤
      T^ε*Real.sqrt A*(T^2*M+T*L*Real.sqrt E) := by
  have hTp : 0 < T := by linarith
  have h₁ : T^δ*T^(α/2)*T^(3*η) ≤ T^ε := by
    rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
    exact Real.rpow_le_rpow_of_exponent_le hT hbudget
  have h₂ : T^δ*T^(α/2)*T^(2*η) ≤ T^ε := by
    rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  calc
    _ = (T^δ*T^(α/2)*T^(3*η))*(Real.sqrt A*T^2*M)+
        (T^δ*T^(α/2)*T^(2*η))*(Real.sqrt A*T*L*Real.sqrt E) := by ring
    _ ≤ T^ε*(Real.sqrt A*T^2*M)+T^ε*(Real.sqrt A*T*L*Real.sqrt E) := by gcongr
    _ = _ := by ring

theorem cubic_scale_choose_exponents {ε : ℝ} (hε : 0 < ε) :
    ∃ η α δ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < α ∧ 0 < δ ∧ δ+α/2+3*η ≤ ε := by
  refine ⟨min (ε/12) (1/10),ε/4,ε/4,?_,?_,by positivity,by positivity,?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · have hh := min_le_left (ε/12) (1/10)
    linarith

/-- The truncated mode height is at most T, so any positive dyadic-count
power U^delta is bounded by T^delta in this range. -/
theorem cubic_truncation_height_le {T η L : ℝ} (hT : 1 ≤ T)
    (hη : η ≤ (4:ℝ)/5) (hL : T^((4:ℝ)/5) ≤ L) :
    T^(1+η)/L ≤ T := by
  have hTp : 0 < T := by linarith
  have hLp : 0 < T^((4:ℝ)/5) := Real.rpow_pos_of_pos hTp _
  calc
    _ ≤ T^(1+η)/T^((4:ℝ)/5) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hTp.le _) hLp hL
    _ = T^(1+η-(4:ℝ)/5) := (Real.rpow_sub hTp _ _).symm
    _ ≤ T^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = T := Real.rpow_one _

theorem cubic_affine_sqrt_exponent {T : ℝ} (hT : 1 ≤ T) (α : ℝ) :
    Real.sqrt (T^α) = T^(α/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by linarith : 0 ≤ T)]
  congr 1
  ring

