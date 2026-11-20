module
public import MathCollab.Density.DetectorMellin
public import MathCollab.Density.DetectorGamma
public import MathCollab.Density.AbelZetaGrowth
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- A coarse bound uniform in the imaginary part, adequate for contour limits. -/
theorem norm_zetaMollifier_le_cutoff (X : ℝ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaMollifier X s‖ ≤ (⌊X⌋₊ : ℝ) := by
  unfold zetaMollifier
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
        ‖(ArithmeticFunction.moebius d : ℂ)*(d : ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 ⌊X⌋₊, (1 : ℝ) := Finset.sum_le_sum fun d hd => by
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
      have hm : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hdpos, Complex.neg_re]
      have hp : (d : ℝ)^(-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hdreal (by linarith)
      exact (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _)).trans (by simpa using hp)
    _ = _ := by simp

/-- Actual zeta has a global linear majorant on the critical line. This is
coarse growth for contour convergence, not a Weyl estimate. -/
theorem norm_zeta_line {u : ℝ} (hu : 1/2 ≤ u) (hu' : u < 1) (t : ℝ) :
    ‖riemannZeta ((u:ℂ)+(t:ℂ)*I)‖ ≤ (1/(1-u)+2)*(1+|t|) := by
  let s := (u:ℂ)+(t:ℂ)*I
  have hr : s.re=u := by simp [s]
  have hs1 : s≠1 := by intro h; rw [h] at hr; simp at hr; linarith
  have hd : 1-u ≤ ‖s-1‖ := by simpa [hr,abs_of_nonpos (sub_nonpos.mpr hu'.le)] using abs_re_le_norm (s-1)
  have ha := ZetaGrowth.norm_abelZetaRemainder_le (s:=s) (by linarith)
  have hsn : ‖s‖ ≤ 1+|t| := (norm_le_abs_re_add_abs_im s).trans (by simp [s,abs_of_nonneg (by linarith : 0≤u)]; linarith)
  change ‖riemannZeta s‖ ≤ _
  rw [ZetaGrowth.riemannZeta_eq_abel (by linarith) hs1]
  apply (norm_sub_le ..).trans
  rw [norm_div,norm_mul,div_eq_mul_one_div]
  have hd' := one_div_le_one_div_of_le (by linarith : 0<1-u) hd
  have ha' : ‖ZetaGrowth.abelZetaRemainder s‖ ≤ 2 := ha.trans ((div_le_iff₀ (by linarith)).mpr (by linarith))
  calc
    _ ≤ (1+|t|)*(1/(1-u))+(1+|t|)*2 := by gcongr
    _ = _ := by ring

theorem norm_riemannZeta_critical_le_linear (t : ℝ) :
    ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ 4*(1+|t|) := by
  convert norm_zeta_line (u:=1/2) le_rfl (by norm_num) t using 1 <;> norm_num

/-- The right contour is absolutely integrable for independent X and Y. -/
theorem integrable_detectorKernel_right {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 1/2 < ρ.re) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) := by
  let line := fun t : ℝ => ((1/2 : ℝ) : ℂ)+(t : ℂ)*I
  have hg : Integrable (fun t : ℝ => Complex.Gamma (line t) *
      LSeries (mollifierDirichletCoeff X) (ρ+line t)) := by
    have h := verticalIntegrable_mellin_smoothedDetector (X := X) hρ
    apply h.congr
    filter_upwards with t
    exact mellin_smoothedDetector_eq (by linarith : 0 ≤ ρ.re)
      (by simp) (by simp; linarith)
  have hp : Continuous (fun t : ℝ => (Y : ℂ)^(line t)) := by
    apply Continuous.cpow continuous_const (by dsimp [line]; fun_prop)
    intro t
    left; simpa using hY
  have hb : ∀ t : ℝ, ‖(Y : ℂ)^(line t)‖ ≤ Y^(1/2 : ℝ) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp [line]
  have hi := hg.bdd_mul hp.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  apply hi.congr
  filter_upwards with t
  dsimp [detectorKernel]
  rw [← riemannZeta_mul_zetaMollifier_eq_LSeries X (by simp [line]; linarith)]
  dsimp [line]
  ring

/-- The shifted contour is absolutely integrable using only linear zeta growth. -/
theorem integrable_detectorKernel_left {ρ : ℂ} {X Y u : ℝ}
    (hY : 0 < Y) (hβ : u < ρ.re) (hβ' : ρ.re ≤ 1) (hu : 1/2 ≤ u := by norm_num) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((u-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  let a : ℝ := u-ρ.re
  let line := fun t : ℝ => (a : ℂ)+(t : ℂ)*I
  have he : ∀ t : ℝ, ρ+line t = (u : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
    intro t
    apply Complex.ext <;> simp [line, a]
  have hg := ((uniform_detector_gamma_mass hβ hu).choose_spec.2 ρ.re le_rfl hβ').2.1
  have hc : Continuous (fun t : ℝ => detectorKernel ρ X Y (line t)) := by
    unfold detectorKernel
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.mul
        · apply Continuous.cpow continuous_const (by dsimp [line]; fun_prop)
          intro t
          left; simpa using hY
        · exact continuous_Gamma_detector_strip (by dsimp [a]; linarith) (by dsimp [a]; linarith)
      · apply continuous_iff_continuousAt.mpr
        intro t
        exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ+line t)).continuousAt
          (by dsimp [line]; fun_prop)
    · apply continuous_iff_continuousAt.mpr
      intro t
      apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt
        (by dsimp [line]; fun_prop)
      rw [he]
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith
  let K := 1/(1-u)+2
  have hd : 0 < 1-u := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C : ℝ := Y^a*(⌊X⌋₊ : ℝ)*K*(1+|ρ.im|)
  have hbound : ∀ t : ℝ, ‖detectorKernel ρ X Y (line t)‖ ≤
      C*((1+|t|)*‖Complex.Gamma (line t)‖) := by
    intro t
    have hm := norm_zetaMollifier_le_cutoff X (s := ρ+line t) (by rw [he]; simp; linarith)
    have hz := norm_zeta_line hu (by linarith) (ρ.im+t)
    rw [← he] at hz
    have hab := abs_add_le ρ.im t
    have hzt : ‖riemannZeta (ρ+line t)‖ ≤ K*(1+|ρ.im|)*(1+|t|) := by
      rw [mul_assoc]
      exact hz.trans (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]) hK)
    dsimp [detectorKernel]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
    have hre : (line t).re = a := by simp [line]
    rw [hre]
    calc
      _ ≤ (Y^a*‖Complex.Gamma (line t)‖)*(⌊X⌋₊ : ℝ)*(K*(1+|ρ.im|)*(1+|t|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hzt (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C]; ring
  exact (hg.const_mul C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- One ordinate-independent horizontal majorant for arbitrary fixed X,Y,rho. -/
theorem norm_detectorKernel_horizontal {ρ : ℂ} {X Y u t : ℝ}
    (hY : 1 ≤ Y) (hβ' : ρ.re ≤ 1)
    (hu : 1/2-ρ.re ≤ u) (hu' : u ≤ 1/2) (ht : |ρ.im|+1 ≤ |t|) :
    ‖detectorKernel ρ X Y ((u : ℂ)+(t : ℂ)*I)‖ ≤
      (60*Y^(1/2 : ℝ)*(⌊X⌋₊ : ℝ)*(2+|ρ.im|)) * (1+|t|)^3*Real.exp (-|t|) := by
  let s : ℂ := (u : ℂ)+(t : ℂ)*I
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hure : (ρ+s).re = ρ.re+u := by simp [s]
  have huim : (ρ+s).im = ρ.im+t := by simp [s]
  have him : 1 ≤ |(ρ+s).im| := by
    rw [huim]
    have h := abs_add_le (ρ.im+t) (-ρ.im)
    have he : ρ.im+t+-ρ.im = t := by ring
    rw [he, abs_neg] at h
    linarith
  have hz := ZetaGrowth.norm_riemannZeta_le_five_mul_norm
    (s := ρ+s) (by rw [hure]; linarith) him
  have hnorm : ‖ρ+s‖ ≤ 2+|ρ.im|+|t| := by
    have h := Complex.norm_le_abs_re_add_abs_im (ρ+s)
    rw [hure, huim, abs_of_nonneg (show 0 ≤ ρ.re+u by linarith)] at h
    have hh := abs_add_le ρ.im t
    linarith
  have hz' : ‖riemannZeta (ρ+s)‖ ≤ 5*(2+|ρ.im|)*(1+|t|) := by
    nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t), abs_nonneg t]
  have hm := norm_zetaMollifier_le_cutoff X (s := ρ+s) (by rw [hure]; linarith)
  have hg := norm_Gamma_contour_strip (a := u) (t := t)
    (by linarith) (by linarith) (by linarith [abs_nonneg ρ.im])
  have hp : ‖(Y : ℂ)^s‖ ≤ Y^(1/2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    exact Real.rpow_le_rpow_of_exponent_le hY (by simpa [s] using hu')
  change ‖(Y : ℂ)^s * Complex.Gamma s * zetaMollifier X (ρ+s) * riemannZeta (ρ+s)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ Y^(1/2 : ℝ)*(12*(1+|t|)^2*Real.exp (-|t|))*(⌊X⌋₊ : ℝ)*
        (5*(2+|ρ.im|)*(1+|t|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul hp hg (norm_nonneg _) (by positivity)) (norm_nonneg _)) hz'
        (norm_nonneg _) (by positivity) |>.trans (by gcongr)
    _ = _ := by ring

theorem tendsto_detector_horizontal_majorant (C : ℝ) :
    Tendsto (fun R : ℝ => C*(1+R)^3*Real.exp (-R)) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h3 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
  have h := (((h0.add (h1.const_mul 3)).add (h2.const_mul 3)).add h3).const_mul C
  convert h using 1
  · funext R
    ring
  · simp

/-- Both horizontal integrals vanish as the independent rectangle height grows. -/
theorem tendsto_detector_horizontal_integral {ρ : ℂ} {X Y ε u : ℝ}
    (hY : 1 ≤ Y) (hβ : u < ρ.re) (hβ' : ρ.re ≤ 1) (hε : |ε| = 1) (hu : 1/2 ≤ u := by norm_num) :
    Tendsto (fun R : ℝ => ∫ u in (u-ρ.re)..(1/2 : ℝ),
      detectorKernel ρ X Y ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)) atTop (𝓝 0) := by
  let C : ℝ := 60*Y^(1/2 : ℝ)*(⌊X⌋₊ : ℝ)*(2+|ρ.im|)
  apply squeeze_zero_norm' _ (tendsto_detector_horizontal_majorant C)
  filter_upwards [eventually_ge_atTop (|ρ.im|+1)] with R hR
  have hRpos : 0 < R := by linarith [abs_nonneg ρ.im]
  have he : |ε*R| = R := by rw [abs_mul, hε, one_mul, abs_of_pos hRpos]
  have hlength : |(1/2 : ℝ)-(u-ρ.re)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hpoint : ∀ v ∈ Set.uIoc (u-ρ.re) (1/2 : ℝ),
      ‖detectorKernel ρ X Y ((v : ℂ)+((ε*R : ℝ) : ℂ)*I)‖ ≤
        C*(1+R)^3*Real.exp (-R) := by
    intro v hv
    rw [Set.uIoc_of_le (by linarith : u-ρ.re ≤ (1/2 : ℝ))] at hv
    have h := norm_detectorKernel_horizontal (ρ := ρ) (X := X) (Y := Y)
      (u := v) (t := ε*R) hY hβ' (by linarith [hv.1]) hv.2 (by rw [he]; exact hR)
    rw [he] at h
    exact h
  have hnonneg : 0 ≤ C*(1+R)^3*Real.exp (-R) := by dsimp [C]; positivity
  have hmul := mul_le_mul_of_nonneg_left hlength hnonneg
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans (by simpa using hmul)

end MathCollab.Density
