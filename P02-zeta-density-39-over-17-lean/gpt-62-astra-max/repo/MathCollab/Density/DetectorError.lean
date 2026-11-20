module
public import MathCollab.Density.DetectorIdentity
public import MathCollab.Density.MollifierBound
public import MathCollab.Density.DetectorParameters

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Normalized detector integral after shifting zeta to the vertical line at `u`. -/
abbrev detectorIntegralOn (u : ℝ) (ρ : ℂ) (X Y : ℝ) : ℂ :=
  (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    detectorKernel ρ X Y (((u-ρ.re : ℝ) : ℂ)+(t : ℂ)*I))

abbrev detectorIntegral := detectorIntegralOn (1/2)

/-- The dependence on the shifted ordinate costs a fixed factor, uniformly in q. -/
theorem detector_shifted_rpow_le {T γ v q : ℝ} (hT : 1 ≤ T)
    (hγ : |γ| ≤ 2*T) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    (1+|γ+v|)^q ≤ 3*T^q*(1+|v|) := by
  have hbase : 1+|γ+v| ≤ 3*T*(1+|v|) := by
    have hab := abs_add_le γ v
    nlinarith [abs_nonneg v, mul_nonneg (show 0 ≤ T-1 by linarith) (abs_nonneg v),
      mul_nonneg (show 0 ≤ T by linarith) (abs_nonneg v)]
  calc
    _ ≤ (3*T*(1+|v|))^q := Real.rpow_le_rpow (by positivity) hbase hq
    _ = 3^q*T^q*(1+|v|)^q := by rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ 3*T^q*(1+|v|) := by
      have h3 : (3 : ℝ)^q ≤ 3 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hq'
      have hv : (1+|v|)^q ≤ 1+|v| := by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v] : 1 ≤ 1+|v|) hq'
      gcongr

/-- A pointwise bound on the shifted line gives a uniform bound on the detector integral. -/
theorem uniform_integral_on {u s : ℝ} (hu : 1/2 ≤ u) (hs : u < s) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q C T X Y : ℝ) (ρ : ℂ),
      0 ≤ q → q ≤ 1 → 0 ≤ C → 1 ≤ T → 0 ≤ X → 0 < Y →
      s ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ 2*T →
      (∀ t : ℝ, ‖riemannZeta ((u : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^q) →
      ‖detectorIntegralOn u ρ X Y‖ ≤ A*C*Real.sqrt X*Y^(u-ρ.re)*T^q := by
  obtain ⟨G, hG, hmass⟩ := uniform_detector_gamma_mass hs hu
  refine ⟨6*G, by positivity, ?_⟩
  intro q C T X Y ρ hq hq' hC hT hX hY hβ hβ' hγ hW
  let a : ℝ := u-ρ.re
  let g := fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*I)
  let F := fun t : ℝ => detectorKernel ρ X Y ((a : ℂ)+(t : ℂ)*I)
  let B : ℝ := 6*C*Real.sqrt X*Y^a*T^q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he : ∀ t : ℝ, ρ+((a : ℂ)+(t : ℂ)*I) = (u : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
    intro t
    apply Complex.ext <;> simp [a]
  have hb : ∀ t : ℝ, ‖F t‖ ≤ B*((1+|t|)*‖g t‖) := by
    intro t
    have hm := norm_zetaMollifier_le_two_sqrt (s := ρ+((a : ℂ)+(t : ℂ)*I)) hX (by rw [he]; simp; linarith)
    have hz := (hW (ρ.im+t)).trans (mul_le_mul_of_nonneg_left
      (detector_shifted_rpow_le hT hγ hq hq') hC)
    rw [← he] at hz
    dsimp [F, detectorKernel]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
    have hre : (((a : ℂ)+(t : ℂ)*I)).re = a := by simp
    rw [hre]
    calc
      _ ≤ (Y^a*‖g t‖)*(2*Real.sqrt X)*(C*(3*T^q*(1+|t|))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hz (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hint := integrable_detectorKernel_left (X := X) hY (hs.trans_le hβ) hβ' hu
  have hw := (hmass ρ.re hβ hβ').2.1
  have hm := (hmass ρ.re hβ hβ').2.2
  have hnorm : ‖∫ t : ℝ, F t‖ ≤ B*G := by
    calc
      _ ≤ ∫ t : ℝ, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, B*((1+|t|)*‖g t‖) := integral_mono hint.norm (hw.const_mul B) hb
      _ = B*(∫ t : ℝ, (1+|t|)*‖g t‖) := integral_const_mul _ _
      _ ≤ B*G := mul_le_mul_of_nonneg_left hm hB
  have hc : ‖((1/(2*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).2
    linarith [Real.pi_gt_three]
  change ‖((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ 1*(B*G) := mul_le_mul hc hnorm (norm_nonneg _) (by norm_num)
    _ = _ := by dsimp [B, a]; ring


/-- The pole term estimate requires no growth bound for zeta. -/
theorem norm_detectorResidue_le {ρ : ℂ} {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 < Y) (hβ : 1/2 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : 1 ≤ |ρ.im|) :
    ‖detectorResidue ρ X Y‖ ≤
      24*Real.sqrt X*Y^(1-ρ.re)*(1+|ρ.im|)*Real.exp (-|ρ.im|) := by
  have hm := norm_zetaMollifier_le_two_sqrt (s := 1) hX (by norm_num)
  have hg := norm_Gamma_one_sub_zero_le (by linarith) hβ' hγ
  dsimp [detectorResidue]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ Y^(1-ρ.re)*(12*(1+|ρ.im|)*Real.exp (-|ρ.im|))*(2*Real.sqrt X) := by gcongr
    _ = _ := by ring




end MathCollab.Density
