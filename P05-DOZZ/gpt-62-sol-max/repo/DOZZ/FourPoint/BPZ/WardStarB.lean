/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardStar

/-! # The rooted moment of the cutoff Ward data

For the cutoff Ward data, the rooted moment `Ψ(x) = E[J_x^{-q}]` has a line derivative at every
point of the support of the test function, given by `E[-q J_x^{-q-1} S_x]` with the scalar root
derivative `S_x`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q r δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

/-- The cutoff part of the data is almost surely integrable against the cutoff chaos. -/
theorem bpzWard_cut_integrable (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) :
    ∀ᵐ ω ∂P, Integrable (fun y => ρ y * bpzWardCutWeight γ q r kt y *
      Real.exp (γ ^ 2 * bpzPin r y)) (regularizedGMC P Xc γ r ω) := by
  obtain ⟨B, hB0, hB⟩ := bpzWardCutWeight_bdd hd
  filter_upwards [regularizedGMC_finite_ae P X hp.hX Xc hp.hXc γ r] with ω hfin
  refine Integrable.of_bound ?_ B (Eventually.of_forall fun y => ?_)
  · exact ((hd.ρ_meas.mul (measurable_bpzWardCutWeight hd)).mul
      (Real.measurable_exp.comp ((continuous_bpzPin r).measurable.const_mul _))).aestronglyMeasurable
  · have hk := bpzWardCutWeight_nonneg hd y
    have hρ0 := hd.ρ_nonneg y
    have hρ1 := hd.ρ_le_one y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hy : ρ y = 0
    · rw [hy]; simp [hB0]
    · have h := hB y hy
      calc ρ y * bpzWardCutWeight γ q r kt y * Real.exp (γ ^ 2 * bpzPin r y)
          = ρ y * (bpzWardCutWeight γ q r kt y * Real.exp (γ ^ 2 * bpzPin r y)) := by ring
        _ ≤ 1 * B := mul_le_mul hρ1 h (by positivity) zero_le_one
        _ = B := one_mul B

/-- The cutoff chaos has no atoms. -/
theorem regularizedGMC_singleton (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω)
    (x : ℂ) : regularizedGMC P Xc γ r ω {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (measure_singleton x)

/-- The rooted moment has a line derivative on the support of the test function. -/
theorem bpzWard_hasLineDerivAt_Psi (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) {x₀ : ℂ} (hx₀ : x₀ ∈ tsupport φ) (v : ℂ) :
    HasLineDerivAt ℝ (fun x => ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
        (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P)
      (∫ ω, -q * bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x₀
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
        bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x₀ v
          (regularizedGMC P Xc γ r ω) (M ω) ∂P) x₀ v := by
  set k₁ := bpzWardCutWeight γ q r kt with hk₁def
  have hk₁m  := measurable_bpzWardCutWeight hd
  have hk₁0  := bpzWardCutWeight_nonneg hd
  have hsep := hd.sep x₀ hx₀
  have hq0  := le_trans zero_le_one hd.q_ge
  have hI₁ := bpzWard_cut_integrable hd hp
  have hI₂ := hp.k₂_int
  have hJm := measurable_bpzWard_J (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas
  have hSm := measurable_bpzWard_S (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas v
  obtain ⟨c, hc, hlow⟩ := bpzWard_J_lower (r := r) hd k₁ hk₁0 ‖x₀‖
  have hlowω : ∀ᵐ ω ∂P, c * (M ω D).toReal ≤
      bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hI₂] with ω hω
    exact hlow _ _ x₀ le_rfl (integrable_bpz_lim_part hd.ρ_meas hd.k₂_meas hd.ρ_le_one
      hd.k₂_nonneg hω hd.δ_pos hd.δ_r hsep (Metric.mem_ball_self hd.δ_pos))
  have hpos : ∀ᵐ ω ∂P, 0 < bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hlowω, bpzWard_far_mass_pos hp hd.D_meas] with ω h1 h2
    exact lt_of_lt_of_le (mul_pos hc h2) h1
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable (fun ω => bpzRootedMixedReal γ r ρ k₁ k₂
      (x₀ + t • v) (regularizedGMC P Xc γ r ω) (M ω)) P :=
    fun t => (hJm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hDeq : (fun ω => bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v)
      =ᵐ[P] fun ω => bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v (regularizedGMC P Xc γ r ω)
        (M ω) := by
    filter_upwards [hI₁, hI₂] with ω h1 h2
    exact bpzRootedMixedDeriv_apply hd.ρ_meas hk₁m hd.k₂_meas hd.ρ_nonneg hd.ρ_le_one hk₁0
      hd.k₂_nonneg h1 h2 hd.δ_pos hd.δ_r hsep v
  have hmeasD := ((hSm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).congr hDeq.symm
  have hint := bpzWard_integrable_rpow_neg hp hd.D_meas (hmeas 0 |>.congr (by simp)) hc
    hlowω hq0
  have hderiv := hasDerivAt_bpz_rooted_moment (P := P) (γ := γ) (r := r) (δ := δ) (q := q)
    (m₁ := fun ω => regularizedGMC P Xc γ r ω) (m₂ := M) (x₀ := x₀) (v := v)
    hd.ρ_meas hk₁m hd.k₂_meas hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg hq0 hd.δ_pos hd.δ_r
    hsep hI₁ hI₂ (Eventually.of_forall fun ω => regularizedGMC_singleton P Xc γ r ω x₀)
    hpos hmeas hmeasD hint
  have hcongr : (fun ω => -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω)
      (M ω) ^ (-q - 1) * bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v)
      =ᵐ[P] fun ω => -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω)
        (M ω) ^ (-q - 1) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v
          (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hDeq] with ω hω
    rw [hω]
  rw [integral_congr_ae hcongr] at hderiv
  exact hderiv

/-- A pointwise bound by a multiple of an integrable nonnegative weight bounds the lintegral. -/
theorem bpz_lintegral_ofReal_abs_le {m : Measure ℂ} {F w : ℂ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hw : Integrable w m) (hw0 : ∀ y, 0 ≤ w y) (hF : ∀ y, |F y| ≤ C * w y) :
    ∫⁻ y, ENNReal.ofReal |F y| ∂m ≤ ENNReal.ofReal (C * ∫ y, w y ∂m) := by
  calc ∫⁻ y, ENNReal.ofReal |F y| ∂m ≤ ∫⁻ y, ENNReal.ofReal (C * w y) ∂m :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hF y)
    _ = ENNReal.ofReal (∫ y, C * w y ∂m) :=
        (ofReal_integral_eq_lintegral_ofReal (hw.const_mul C)
          (Eventually.of_forall fun y => mul_nonneg hC (hw0 y))).symm
    _ = ENNReal.ofReal (C * ∫ y, w y ∂m) := by rw [integral_const_mul]

theorem bpzPin_nonneg (r : ℝ) (x : ℂ) : 0 ≤ bpzPin r x :=
  integral_nonneg fun a => Real.log_nonneg (bpz_one_le_normPlus a)

/-- The cutoff weight alone is almost surely integrable against the cutoff chaos. -/
theorem bpzWard_cut_integrable' (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) :
    ∀ᵐ ω ∂P, Integrable (fun y => ρ y * bpzWardCutWeight γ q r kt y)
      (regularizedGMC P Xc γ r ω) := by
  filter_upwards [bpzWard_cut_integrable hd hp] with ω hω
  refine hω.mono' (hd.ρ_meas.mul (measurable_bpzWardCutWeight hd)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h0 := mul_nonneg (hd.ρ_nonneg y) (bpzWardCutWeight_nonneg hd y)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact le_mul_of_one_le_right h0
    (Real.one_le_exp (mul_nonneg (sq_nonneg γ) (bpzPin_nonneg r y)))

theorem bpzMixedReal_nonneg {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1)
    (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) (m₁ m₂ : Measure ℂ) :
    0 ≤ bpzMixedReal ρ k₁ k₂ m₁ m₂ :=
  add_nonneg (integral_nonneg fun y => mul_nonneg (hρ0 y) (hk₁0 y))
    (integral_nonneg fun y => mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))

theorem bpzRootedMixedReal_nonneg {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) (x : ℂ)
    (m₁ m₂ : Measure ℂ) : 0 ≤ bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ :=
  add_nonneg (integral_nonneg fun y => mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y))
      (bpzCutRootKernel_pos γ r x y).le)
    (integral_nonneg fun y => mul_nonneg (mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))
      (bpzLimRootKernel_pos γ r x y).le)

theorem bpz_exp_mul_rpow_neg {a J q : ℝ} (hJ : 0 ≤ J) :
    (Real.exp a * J) ^ (-q) = Real.exp (-(q * a)) * J ^ (-q) := by
  rw [Real.mul_rpow (Real.exp_pos _).le hJ, ← Real.exp_mul]
  congr 2
  ring

private theorem abs_integral_weighted_deriv_le {m : Measure ℂ} {f : ℂ → ℝ}
    {D : ℂ → ℂ →L[ℝ] ℝ} {γ r : ℝ} (hf : Integrable f m) (hf₀ : ∀ y, 0 ≤ f y)
    (hD : ∀ y, ‖D y‖ ≤ Real.exp r) (v : ℂ) :
    |∫ y, f y * (γ ^ 2 * D y v) ∂m| ≤ γ ^ 2 * Real.exp r * ‖v‖ * ∫ y, f y ∂m := by
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) (hf.const_mul _)
    (Eventually.of_forall fun y => ?_))
  have h := ((D y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hD y) (norm_nonneg v))
  dsimp only
  rw [abs_mul, abs_mul, abs_of_nonneg (hf₀ y), abs_of_nonneg (sq_nonneg γ), ← Real.norm_eq_abs]
  calc
    f y * (γ ^ 2 * ‖D y v‖) ≤ f y * (γ ^ 2 * (Real.exp r * ‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (sq_nonneg γ)) (hf₀ y)
    _ = _ := by ring

section
variable {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y)
  (hk₂0 : ∀ y, 0 ≤ k₂ y) {m₁ m₂ : Measure ℂ}
include hρ0 hρ1 hk₁0 hk₂0

/-- The untilted root-derivative functional is bounded by the mixed mass. -/
theorem abs_bpzMixedDerivReal_le
    (h₁ : Integrable (fun y => ρ y * k₁ y) m₁) (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (x v : ℂ) :
    |bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂| ≤
      γ ^ 2 * Real.exp r * ‖v‖ * bpzMixedReal ρ k₁ k₂ m₁ m₂ := by
  unfold bpzMixedDerivReal bpzMixedReal
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_integral_weighted_deriv_le h₁ (fun y => mul_nonneg (hρ0 y) (hk₁0 y))
      (fun y => norm_bpzLamDeriv_le_exp r (x - y)) v
  · exact abs_integral_weighted_deriv_le h₂ (fun y => mul_nonneg (sub_nonneg.mpr (hρ1 y)) (hk₂0 y))
      (fun y => (norm_bpzTruncLogDeriv_le r (x - y)).1) v

/-- The rooted root-derivative functional is bounded by the rooted mixed mass. -/
theorem abs_bpzRootedMixedDerivApply_le
    {x : ℂ} (h₁ : Integrable (fun y => ρ y * k₁ y * bpzCutRootKernel γ r x y) m₁)
    (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) m₂) (v : ℂ) :
    |bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v m₁ m₂| ≤
      γ ^ 2 * Real.exp r * ‖v‖ * bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ := by
  unfold bpzRootedMixedDerivApply bpzRootedMixedReal
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [← mul_assoc] using abs_integral_weighted_deriv_le h₁
      (fun y => mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y)) (bpzCutRootKernel_pos γ r x y).le)
      (fun y => norm_bpzLamDeriv_le_exp r (x - y)) v
  · simpa only [← mul_assoc] using abs_integral_weighted_deriv_le h₂
      (fun y => mul_nonneg (mul_nonneg (sub_nonneg.mpr (hρ1 y)) (hk₂0 y))
        (bpzLimRootKernel_pos γ r x y).le)
      (fun y => (norm_bpzTruncLogDeriv_le r (x - y)).1) v

end

theorem bpzMixedReal_cut_le {ρ k₁ k₂ : ℂ → ℝ} (hρ1 : ∀ y, ρ y ≤ 1) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (m₁ m₂ : Measure ℂ) : ∫ y, ρ y * k₁ y ∂m₁ ≤ bpzMixedReal ρ k₁ k₂ m₁ m₂ := by
  have h2 := integral_nonneg (μ := m₂) (f := fun y => (1 - ρ y) * k₂ y)
    fun y => mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)
  show ∫ y, ρ y * k₁ y ∂m₁ ≤ ∫ y, ρ y * k₁ y ∂m₁ + ∫ y, (1 - ρ y) * k₂ y ∂m₂
  exact le_add_of_nonneg_right h2

theorem bpz_mul_rpow_neg_mul_le {C I A q : ℝ} (hC : 0 ≤ C) (hI : 0 < I) (hA : A ≤ I) :
    C * I ^ (-q) * A ≤ C * I ^ (-(q - 1)) := by
  calc C * I ^ (-q) * A ≤ C * I ^ (-q) * I :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hC (Real.rpow_nonneg hI.le _))
    _ = C * I ^ (-(q - 1)) := by
        rw [mul_assoc, ← Real.rpow_add_one hI.ne']
        congr 2
        ring

/-- A bounded function vanishing off the support of the test function, times the pinned `|x|₊⁴`
factor, is dominated by the cutoff weight. -/
theorem bpzWard_weight_bound_of (hd : BPZWardData γ q r δ ρ kt k₂ φ D) {g : ℂ → ℝ} {B : ℝ}
    (hgB : ∀ x, |g x| ≤ B) (hg0 : ∀ x, x ∉ tsupport φ → g x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)| ≤
      C * (ρ x * bpzWardCutWeight γ q r kt x) := by
  obtain ⟨c, hc, hck⟩ := hd.kt_pos
  refine ⟨max B 0 / c, by positivity, fun x => ?_⟩
  have hn : 0 ≤ normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) :=
    mul_nonneg (Real.rpow_nonneg (bpz_normPlus_pos x).le _) (Real.exp_pos _).le
  by_cases hx : x ∈ tsupport φ
  · have hρx : ρ x = 1 := by
      by_contra hne
      have h := hd.sep x hx x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
      rw [sub_self, norm_zero] at h
      linarith [hd.δ_pos]
    have hkx := hck x hx
    unfold bpzWardCutWeight
    rw [hρx, one_mul, mul_assoc, abs_mul, abs_of_nonneg hn]
    calc |g x| * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x))
        ≤ max B 0 * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) :=
          mul_le_mul_of_nonneg_right ((hgB x).trans (le_max_left _ _)) hn
      _ ≤ max B 0 / c * kt x * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) := by
          apply mul_le_mul_of_nonneg_right _ hn
          rw [div_mul_eq_mul_div, le_div_iff₀ hc]
          exact mul_le_mul_of_nonneg_left hkx (le_max_right _ _)
      _ = max B 0 / c * (kt x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) := by
          ring
  · rw [hg0 x hx, zero_mul, zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hd.ρ_nonneg x) (bpzWardCutWeight_nonneg hd x))

section
variable (hd : BPZWardData γ q r δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
include hd hp

/-- Rooting a signed Ward integrand: the mixed mass bound gives integrability, and
homogeneity cancels the pinning exponential and the reference density. -/
private theorem bpzWard_deroot_scaled (w : ℂ → ℝ) (hw : Continuous w)
    (B K : ℝ) (hB : ∀ x, |w x| ≤ B) (hw₀ : ∀ x ∉ tsupport φ, w x = 0) (hK : 0 ≤ K)
    (J : ℂ → Measure ℂ → Measure ℂ → ℝ) (G : ℂ → Ω → ℝ) :
    let k₁ := bpzWardCutWeight γ q r kt
    let Mr := regularizedGMC P Xc γ r
    let I := fun ω => bpzMixedReal ρ k₁ k₂ (Mr ω) (M ω)
    let pin := fun x => γ ^ 2 * bpzPin r x
    Measurable (fun p : Ω × ℂ => J p.2 (Mr p.1) (M p.1)) →
    (∀ x, Measurable (fun p : Measure ℂ × Measure ℂ => J x p.1 p.2)) →
    (∀ᵐ ω ∂P, 0 < I ω → ∀ x, |J x (Mr ω) (M ω)| ≤ K * I ω ^ (-q)) →
    (∀ x ω, J x ((Mr ω).withDensity (bpzCutRootDensity γ r x))
        ((M ω).withDensity (bpzLimRootDensity γ r x)) = Real.exp (-(q * pin x)) * G x ω) →
    (∫ ω, ∫ x, w x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) *
      J x (Mr ω) (M ω) ∂Mr ω ∂P) = ∫ x, w x * ∫ ω, G x ω ∂P := by
  intro k₁ Mr I pin hJm hJx hJ hroot
  let W := fun x => w x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)
  let F := fun x m₁ m₂ => W x * J x m₁ m₂
  have hW : Continuous W := (hw.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
    (bpz_normPlus_pos x).ne')).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_bpzPin r)))
  have hk₁ := bpzWardCutWeight_nonneg hd
  obtain ⟨C, hC, hb⟩ := bpzWard_weight_bound_of hd hB hw₀
  have hIm : Measurable I := (measurable_bpzMixedReal hd.ρ_meas (measurable_bpzWardCutWeight hd)
    hd.k₂_meas).comp ((regularizedGMC_measurable P X hp.hX Xc hp.hXc γ r).prodMk hp.hMm)
  obtain ⟨c, hc, hl⟩ := bpzWard_mixed_lower hd hp k₁ hk₁ (P := P) (Xc := Xc) (r := r)
  have hint := bpzWard_integrable_rpow_neg hp hd.D_meas hIm.aestronglyMeasurable hc hl
    (p := q - 1) (by linarith [hd.q_ge])
  have hCK := mul_nonneg hC hK
  have hfin : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal |F x (Mr ω) (M ω)| ∂Mr ω ∂P) < ⊤ := by
    have hm : ∀ᵐ ω ∂P, (∫⁻ x, ENNReal.ofReal |F x (Mr ω) (M ω)| ∂Mr ω) ≤
        ENNReal.ofReal (C * K * I ω ^ (-(q - 1))) := by
      filter_upwards [hJ, bpzWard_cut_integrable' hd hp, hl, bpzWard_far_mass_pos hp hd.D_meas]
        with ω hJω hρk hlω hpos
      have hI : 0 < I ω := (mul_pos hc hpos).trans_le hlω
      have hq : 0 ≤ I ω ^ (-q) := Real.rpow_nonneg hI.le _
      refine (bpz_lintegral_ofReal_abs_le (mul_nonneg hCK hq) hρk
        (fun x => mul_nonneg (hd.ρ_nonneg x) (hk₁ x)) (fun x => ?_)).trans ?_
      · rw [show |F x (Mr ω) (M ω)| = |W x| * |J x (Mr ω) (M ω)| from abs_mul ..]
        exact (mul_le_mul (hb x) (hJω hI x) (abs_nonneg _)
          (mul_nonneg hC (mul_nonneg (hd.ρ_nonneg x) (hk₁ x)))).trans_eq (by ring)
      · exact ENNReal.ofReal_le_ofReal (bpz_mul_rpow_neg_mul_le hCK hI
          (bpzMixedReal_cut_le hd.ρ_le_one hd.k₂_nonneg ..))
    refine (lintegral_mono_ae hm).trans_lt ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul (C * K))
      (Eventually.of_forall fun ω => mul_nonneg hCK (Real.rpow_nonneg
        (bpzMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁ hd.k₂_nonneg ..) _))]
    exact ENNReal.ofReal_lt_top
  rw [bpz_cutoff_deroot_real P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc r F
    ((hW.measurable.comp measurable_snd).mul hJm) (fun x => measurable_const.mul (hJx x)) hfin]
  apply integral_congr_ae
  filter_upwards with x
  have he : Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * pin x)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    congr 1
    dsimp [pin]
    ring
  have hn : normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add (bpz_normPlus_pos x)]
    norm_num
  simp only [Mr] at hroot
  simp only [F, hroot, ← mul_assoc, integral_const_mul, W]
  linear_combination (w x * ∫ ω, G x ω ∂P) * ((normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ)) * he + hn)

/-- The left side of the cutoff Ward identity, rooted at the integration point. -/
theorem bpzWard_left_deroot (v : ℂ) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) *
        ∫ x, bpzWardLeftWeight γ q r kt φ v x ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, fderiv ℝ (fun x => φ x * kt x) x v *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P := by
  let w := fun x => fderiv ℝ (fun y => φ y * kt y) x v
  have hw : Continuous w := (hd.f_C1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ (fun y => φ y * kt y) x) :=
    (hd.φ_compact.mul_right).fderiv (𝕜 := ℝ)
  obtain ⟨B, hB⟩ := hw.bounded_above_of_compact_support (hs.comp_left
    (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp))
  have hw₀ x (hx : x ∉ tsupport φ) : w x = 0 := by
    have h := image_eq_zero_of_notMem_tsupport
      (f := fderiv ℝ (fun y => φ y * kt y))
      (fun hx' => hx ((tsupport_fderiv_subset ℝ).trans
        (tsupport_mul_subset_left (f := φ) (g := kt)) hx'))
    simp [w, h]
  let k₁ := bpzWardCutWeight γ q r kt
  have hm := measurable_bpzMixedReal hd.ρ_meas (measurable_bpzWardCutWeight hd) hd.k₂_meas
  have hMr := regularizedGMC_measurable P X hp.hX Xc hp.hXc γ r
  have he := bpzWard_deroot_scaled hd hp w hw B 1 (fun x => by simpa only [Real.norm_eq_abs] using hB x)
      hw₀ zero_le_one (fun _ m₁ m₂ => bpzMixedReal ρ k₁ k₂ m₁ m₂ ^ (-q))
      (fun x ω => bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q))
      (((hm.comp (hMr.prodMk hp.hMm)).comp measurable_fst).pow_const _)
      (fun _ => hm.pow_const _)
      (Eventually.of_forall fun ω _ _ => by rw [one_mul, abs_of_nonneg (Real.rpow_nonneg
        (bpzMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one (bpzWardCutWeight_nonneg hd) hd.k₂_nonneg ..) _)])
      (fun x ω => by
        rw [bpzMixedReal_tilt]
        exact bpz_exp_mul_rpow_neg (bpzRootedMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one
          (bpzWardCutWeight_nonneg hd) hd.k₂_nonneg x ..))
  refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans he
  rw [mul_comm, ← integral_mul_const]
  rfl

/-- The right side of the cutoff Ward identity, rooted at the integration point. -/
theorem bpzWard_right_deroot (v : ℂ) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^
        (-q - 1) * ∫ x, φ x * bpzWardCutWeight γ q r kt x * bpzMixedDerivReal γ r ρ
          (bpzWardCutWeight γ q r kt) k₂ x v (regularizedGMC P Xc γ r ω) (M ω)
          ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, φ x * kt x *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
            (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
          bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x v
            (regularizedGMC P Xc γ r ω) (M ω) ∂P := by
  let k₁ := bpzWardCutWeight γ q r kt
  let Mr := regularizedGMC P Xc γ r
  let K := γ ^ 2 * Real.exp r * ‖v‖
  let I := fun m₁ m₂ => bpzMixedReal ρ k₁ k₂ m₁ m₂
  let J := fun x m₁ m₂ => I m₁ m₂ ^ (-q - 1) * bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂
  have hk₁m := measurable_bpzWardCutWeight hd
  have hk₁ := bpzWardCutWeight_nonneg hd
  have hm := measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas
  have hMr := regularizedGMC_measurable P X hp.hX Xc hp.hXc γ r
  have hYm := measurable_bpzWard_Yhat (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas v
  have hw : Continuous (fun x => φ x * kt x) := hd.f_C1.continuous
  obtain ⟨B, hB⟩ := hw.bounded_above_of_compact_support hd.φ_compact.mul_right
  have he := bpzWard_deroot_scaled hd hp _ hw B K (fun x => by
    simpa only [Real.norm_eq_abs] using hB x) (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]) (by dsimp [K]; positivity) J
    (fun x ω => bpzRootedMixedReal γ r ρ k₁ k₂ x (Mr ω) (M ω) ^ (-q - 1) *
      bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (Mr ω) (M ω))
    ((((hm.comp (hMr.prodMk hp.hMm)).comp measurable_fst).pow_const _).mul hYm)
    (fun x => (hm.pow_const _).mul (measurable_bpzMixedDerivReal hd.ρ_meas hk₁m hd.k₂_meas x v)) ?_ ?_
  · refine Eq.trans (integral_congr_ae (ae_of_all _ fun ω => ?_)) he
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [J, I, k₁, bpzWardCutWeight, Mr]
    ring
  · filter_upwards [bpzWard_cut_integrable' hd hp, hp.k₂_int] with ω h₁ h₂ hI x
    dsimp only [J]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hI.le _)]
    refine (mul_le_mul_of_nonneg_left (abs_bpzMixedDerivReal_le hd.ρ_nonneg hd.ρ_le_one
      hk₁ hd.k₂_nonneg h₁ h₂ x v) (Real.rpow_nonneg hI.le _)).trans_eq ?_
    dsimp only [K]
    -- Combine only the two powers of the mixed mass.
    have hpow : I (Mr ω) (M ω) ^ (-q - 1) * I (Mr ω) (M ω) = I (Mr ω) (M ω) ^ (-q) := by
      rw [← Real.rpow_add_one hI.ne', show -q - 1 + 1 = -q by ring]
    linear_combination (γ ^ 2 * Real.exp r * ‖v‖) * hpow
  · intro x ω
    dsimp only [J, I]
    rw [bpzMixedReal_tilt, bpzMixedDerivReal_tilt, show -q - 1 = -(q + 1) by ring,
      bpz_exp_mul_rpow_neg (bpzRootedMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁ hd.k₂_nonneg x ..)]
    have hE : Real.exp (-((q + 1) * (γ ^ 2 * bpzPin r x))) * Real.exp (γ ^ 2 * bpzPin r x) =
        Real.exp (-(q * (γ ^ 2 * bpzPin r x))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hE]
    ring

end

end DOZZ.Proofs
