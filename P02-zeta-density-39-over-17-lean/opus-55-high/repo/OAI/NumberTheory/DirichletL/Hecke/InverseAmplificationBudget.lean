module
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPrimePool
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

def amplificationPower (c r : ℝ) : ℝ := max 0 (((1+c)*r-1)/6)
def sourceExponent (r : ℝ) : ℝ := max 1 ((1+5*r)/6)

theorem amplificationPower_nonneg (c r : ℝ) : 0≤amplificationPower c r := le_max_left _ _

theorem amplificationPower_upper (c r R : ℝ) (hc : c≤1) (hr : 0≤ r)
    (hrR : r≤R) : amplificationPower c r≤R/3 := by
  apply max_le (by linarith)
  have hh := mul_le_mul_of_nonneg_right hc hr
  nlinarith

theorem amplified_exponent (c r : ℝ) :
    1+5*amplificationPower c r=max 1 ((1+5*(1+c)*r)/6) := by
  unfold amplificationPower
  by_cases h : 0≤((1+c)*r-1)/6
  grind
  grind

theorem amplified_exponent_le (c r R : ℝ) (hc : 0≤ c) (hrR : r≤R)
    (hR : 0≤R) : 1+5*amplificationPower c r≤ sourceExponent r+5*c*R/6 := by
  rw [amplified_exponent]
  apply max_le
  · have hh := le_max_left 1 ((1+5*r)/6)
    unfold sourceExponent
    nlinarith [mul_nonneg hc hR]
  · have hh := le_max_right 1 ((1+5*r)/6)
    have hh' := mul_le_mul_of_nonneg_left hrR hc
    unfold sourceExponent
    nlinarith

theorem exists_amplification_budget (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ : ℝ, 0< c ∧ c≤1 ∧ 0<κ ∧
      ∀ r : ℝ, 0≤ r → r≤R →
      1+5*amplificationPower c r+κ*(1+6*amplificationPower c r+r)≤
        sourceExponent r+ε/2 := by
  pm_8198 c R
  let κ := ε/(4*(1+3*R))
  have hc : 0< c := lt_min zero_lt_one (div_pos hε (by positivity))
  pm_3587 hκ κ hε
  have hc1 : c≤1 := min_le_left _ _
  have hcb : c*(4*(R+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hκb : κ*(4*(1+3*R))=ε := by dsimp [κ]; field_simp
  pm_164 c κ hc hc1 hκ
  intro r hr hrR
  have hp := amplificationPower_upper c r R hc1 hr hrR
  have he := amplified_exponent_le c r R hc.le hrR hR
  have hraw : κ*(1+6*amplificationPower c r+r)≤κ*(1+3*R) := by
    apply mul_le_mul_of_nonneg_left _ hκ.le
    linarith
  nlinarith

theorem logarithmic_cost_eventually (A b P η : ℝ) (hA : 1≤A)
    (hbA : 1≤b*A) (hP : 0≤P) (hη : 0<η) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ U : ℝ in atTop, ∀ p : ℝ, 0≤p → p≤P →
      (1+2*Real.log (b*(A*U^p)))*Real.log (A*U^p)≤K*U^η := by
  let K := (1+2*Real.log (b*A)+2*P)*(Real.log A+P)
  have hLA : 0≤Real.log A := Real.log_nonneg hA
  have hLB : 0≤Real.log (b*A) := Real.log_nonneg hbA
  have hK : 0≤K := mul_nonneg (by positivity) (by positivity)
  pm_3138
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with U hlog hLU hU
  intro p hp hpP
  have hUp : 0<U := zero_lt_one.trans_le hU
  pm_3773 hpow U p hUp
  have hx : 1≤A*U^p := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hU hp)
  have hlogx : Real.log (A*U^p)=Real.log A+p*Real.log U := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hA)) hpow.ne',Real.log_rpow hUp]
  have hlogbx : Real.log (b*(A*U^p))=Real.log (b*A)+p*Real.log U := by
    rw [show b*(A*U^p)=b*A*U^p by ring,
      Real.log_mul (ne_of_gt (zero_lt_one.trans_le hbA)) hpow.ne',Real.log_rpow hUp]
  have hfirst : 1+2*Real.log (b*(A*U^p))≤(1+2*Real.log (b*A)+2*P)*Real.log U := by
    pm_7073 hlogbx hLB
  have hsecond : Real.log (A*U^p)≤(Real.log A+P)*Real.log U := by
    pm_7073 hlogx hLA
  pm_3139 hsq
  calc
    _ ≤ ((1+2*Real.log (b*A)+2*P)*Real.log U)*((Real.log A+P)*Real.log U) :=
      mul_le_mul hfirst hsecond (Real.log_nonneg hx) (by positivity)
    _ = K*(Real.log U)^2 := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK

end SevenEighths.HeckeInverseAmplification

end

end OAI
