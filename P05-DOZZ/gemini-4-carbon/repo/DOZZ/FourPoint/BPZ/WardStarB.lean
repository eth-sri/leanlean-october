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

variable {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q r δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

private lemma abs_integral_deriv_bound {m : Measure ℂ} {w D : ℂ → ℝ} {K : ℝ}
    (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w m) (hD : ∀ y, |D y| ≤ K) :
    |∫ y, w y * D y ∂m| ≤ K * ∫ y, w y ∂m := by
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) (hwi.const_mul K) (Eventually.of_forall fun y => ?_))
  dsimp only
  rw [abs_mul, abs_of_nonneg (hw0 y)]
  exact (mul_le_mul_of_nonneg_left (hD y) (hw0 y)).trans_eq (mul_comm _ _)

private lemma abs_bpzMixedDerivReal_le (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1)
    (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) {m₁ m₂ : Measure ℂ}
    (h₁ : Integrable (fun y => ρ y * k₁ y) m₁) (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (x v : ℂ) :
    |bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂| ≤
      γ ^ 2 * Real.exp r * ‖v‖ * bpzMixedReal ρ k₁ k₂ m₁ m₂ := by
  unfold bpzMixedDerivReal bpzMixedReal; rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine abs_integral_deriv_bound (fun y => mul_nonneg (hρ0 y) (hk₁0 y)) h₁ fun y => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg γ), mul_assoc, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (((bpzLamDeriv r (x - y)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_bpzLamDeriv_le_exp r _) (norm_nonneg v))) (sq_nonneg γ)
  · refine abs_integral_deriv_bound (fun y => mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)) h₂ fun y => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg γ), mul_assoc, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (((bpzTruncLogDeriv r (x - y)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_bpzTruncLogDeriv_le r _).1 (norm_nonneg v))) (sq_nonneg γ)

/-- The rooted root-derivative functional is bounded by the rooted mixed mass. -/
theorem abs_bpzRootedMixedDerivApply_le (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) {m₁ m₂ : Measure ℂ}
    {x : ℂ} (h₁ : Integrable (fun y => ρ y * k₁ y * bpzCutRootKernel γ r x y) m₁)
    (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) m₂) (v : ℂ) :
    |bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v m₁ m₂| ≤
      γ ^ 2 * Real.exp r * ‖v‖ * bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ := by
  unfold bpzRootedMixedDerivApply bpzRootedMixedReal; rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · simp_rw [show ∀ y, ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) * bpzLamDeriv r (x - y) v =
      (ρ y * k₁ y * bpzCutRootKernel γ r x y) * (γ ^ 2 * bpzLamDeriv r (x - y) v) by intro; ring]
    refine abs_integral_deriv_bound
      (fun y => mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y)) (bpzCutRootKernel_pos γ r x y).le) h₁ fun y => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg γ), mul_assoc, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (((bpzLamDeriv r (x - y)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_bpzLamDeriv_le_exp r _) (norm_nonneg v))) (sq_nonneg γ)
  · simp_rw [show ∀ y, (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) * bpzTruncLogDeriv r (x - y) v =
      ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v) by intro; ring]
    refine abs_integral_deriv_bound
      (fun y => mul_nonneg (mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)) (bpzLimRootKernel_pos γ r x y).le) h₂ fun y => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg γ), mul_assoc, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (((bpzTruncLogDeriv r (x - y)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_bpzTruncLogDeriv_le r _).1 (norm_nonneg v))) (sq_nonneg γ)

theorem bpzRootedMixedReal_nonneg (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) (x : ℂ)
    (m₁ m₂ : Measure ℂ) : 0 ≤ bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ :=
  add_nonneg (integral_nonneg fun y => mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y))
      (bpzCutRootKernel_pos γ r x y).le)
    (integral_nonneg fun y => mul_nonneg (mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))
      (bpzLimRootKernel_pos γ r x y).le)

section
variable (hd : BPZWardData γ q r δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
include hd hp

/-- The cutoff part of the data is almost surely integrable against the cutoff chaos. -/
theorem bpzWard_cut_integrable :
    ∀ᵐ ω ∂P, Integrable (fun y => ρ y * bpzWardCutWeight γ q r kt y *
      Real.exp (γ ^ 2 * bpzPin r y)) (regularizedGMC P Xc γ r ω) := by
  obtain ⟨B, hB0, hB⟩ := bpzWardCutWeight_bdd hd
  filter_upwards [regularizedGMC_finite_ae P X hp.hX Xc hp.hXc γ r] with ω _
  refine Integrable.of_bound ((hd.ρ_meas.mul (measurable_bpzWardCutWeight hd)).mul
      (Real.measurable_exp.comp ((continuous_bpzPin r).measurable.const_mul _))).aestronglyMeasurable
    B (Eventually.of_forall fun y => ?_)
  have hk0 := mul_nonneg (bpzWardCutWeight_nonneg hd y) (Real.exp_pos (γ ^ 2 * bpzPin r y)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [mul_nonneg (hd.ρ_nonneg y) hk0])]
  by_cases hy : ρ y = 0
  · simp [hy, hB0]
  · exact (mul_assoc (ρ y) _ _).trans_le ((mul_le_mul (hd.ρ_le_one y) (hB y hy) hk0 zero_le_one).trans_eq (one_mul B))

/-- The rooted moment has a line derivative on the support of the test function. -/
theorem bpzWard_hasLineDerivAt_Psi {x₀ : ℂ} (hx₀ : x₀ ∈ tsupport φ) (v : ℂ) :
    HasLineDerivAt ℝ (fun x => ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
        (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P)
      (∫ ω, -q * bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x₀
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
        bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x₀ v
          (regularizedGMC P Xc γ r ω) (M ω) ∂P) x₀ v := by
  set k₁ := bpzWardCutWeight γ q r kt
  have hk₁m := measurable_bpzWardCutWeight hd
  have hk₁0 := bpzWardCutWeight_nonneg hd
  have hsep := hd.sep x₀ hx₀
  have hq0 := zero_le_one.trans hd.q_ge
  have hI₁ := bpzWard_cut_integrable hd hp
  have hJm := measurable_bpzWard_J (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas
  have hSm := measurable_bpzWard_S (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas v
  obtain ⟨c, hc, hlow⟩ := bpzWard_J_lower (r := r) hd k₁ hk₁0 ‖x₀‖
  have hlowω : ∀ᵐ ω ∂P, c * (M ω D).toReal ≤
      bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) :=
    hp.k₂_int.mono fun ω hω => hlow _ _ x₀ le_rfl (integrable_bpz_lim_part hd.ρ_meas hd.k₂_meas
      hd.ρ_le_one hd.k₂_nonneg hω hd.δ_pos hd.δ_r hsep (Metric.mem_ball_self hd.δ_pos))
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable (fun ω => bpzRootedMixedReal γ r ρ k₁ k₂
      (x₀ + t • v) (regularizedGMC P Xc γ r ω) (M ω)) P :=
    fun _ => (hJm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hDeq : (fun ω => bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v)
      =ᵐ[P] fun ω => bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hI₁, hp.k₂_int] with ω h1 h2
    exact bpzRootedMixedDeriv_apply hd.ρ_meas hk₁m hd.k₂_meas hd.ρ_nonneg hd.ρ_le_one hk₁0
      hd.k₂_nonneg h1 h2 hd.δ_pos hd.δ_r hsep v
  have hderiv := hasDerivAt_bpz_rooted_moment (P := P) (γ := γ) (r := r) (δ := δ) (q := q)
    (m₁ := fun ω => regularizedGMC P Xc γ r ω) (m₂ := M) (x₀ := x₀) (v := v)
    hd.ρ_meas hk₁m hd.k₂_meas hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg hq0 hd.δ_pos hd.δ_r
    hsep hI₁ hp.k₂_int
    (Eventually.of_forall fun ω => withDensity_absolutelyContinuous _ _ (measure_singleton x₀))
    (by filter_upwards [hlowω, bpzWard_far_mass_pos hp hd.D_meas] with ω h1 h2; exact (mul_pos hc h2).trans_le h1)
    hmeas (((hSm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).congr hDeq.symm)
    (bpzWard_integrable_rpow_neg hp hd.D_meas ((hmeas 0).congr (by simp)) hc hlowω hq0)
  have hcongr : (fun ω => -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω)
      (M ω) ^ (-q - 1) * bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v)
      =ᵐ[P] fun ω => -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω)
        (M ω) ^ (-q - 1) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v
          (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hDeq] with ω hω; rw [hω]
  rw [integral_congr_ae hcongr] at hderiv
  exact hderiv

omit hd hp in
private lemma bpzWard_deroot_master (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) (g : ℂ → ℝ) (hgc : Continuous g)
    (hg0 : ∀ x, x ∉ tsupport φ → g x = 0) {B : ℝ} (hgB : ∀ x, |g x| ≤ B)
    (s K : ℝ) (hK0 : 0 ≤ K) (G G₀ : ℂ → Measure ℂ → Measure ℂ → ℝ)
    (hGm : Measurable fun p : Ω × ℂ => G p.2 (regularizedGMC P Xc γ r p.1) (M p.1))
    (hGx : ∀ x, Measurable fun q' : Measure ℂ × Measure ℂ => G x q'.1 q'.2)
    (hGbd : ∀ m₁ m₂ x, Integrable (fun y => ρ y * bpzWardCutWeight γ q r kt y) m₁ →
      Integrable (fun y => (1 - ρ y) * k₂ y) m₂ →
      |G x m₁ m₂| ≤ K * bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ m₁ m₂ ^ s)
    (hGtilt : ∀ x m₁ m₂,
      G x (m₁.withDensity (bpzCutRootDensity γ r x)) (m₂.withDensity (bpzLimRootDensity γ r x)) =
        Real.exp (s * (γ ^ 2 * bpzPin r x)) * G₀ x m₁ m₂) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
        ∫ x, g x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) *
          G x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, g x * ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
        G₀ x (regularizedGMC P Xc γ r ω) (M ω) ∂P := by
  set k₁ := bpzWardCutWeight γ q r kt
  have hk₁m := measurable_bpzWardCutWeight hd
  have hk₁0 := bpzWardCutWeight_nonneg hd
  set w : ℂ → ℝ := fun x => g x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)
  have hwc : Continuous w := (hgc.mul (bpz_continuous_normPlus.rpow_const fun x =>
    Or.inl (bpz_normPlus_pos x).ne')).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_bpzPin r)))
  obtain ⟨c, hc, hck⟩ := hd.kt_pos
  set C := max B 0 / c
  have hC0 : 0 ≤ C := by positivity
  have hCw (x : ℂ) : |w x| ≤ C * (ρ x * k₁ x) := by
    have hn : 0 ≤ normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) :=
      mul_nonneg (Real.rpow_nonneg (bpz_normPlus_pos x).le _) (Real.exp_pos _).le
    by_cases hx : x ∈ tsupport φ
    · have hρx : ρ x = 1 := by
        by_contra hne
        have h := hd.sep x hx x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
        rw [sub_self, norm_zero] at h; linarith [hd.δ_pos]
      dsimp only [w, k₁, bpzWardCutWeight]
      rw [hρx, one_mul, mul_assoc, abs_mul, abs_of_nonneg hn]
      refine (mul_le_mul_of_nonneg_right ((hgB x).trans (le_max_left B 0)) hn).trans ?_
      rw [show C * (kt x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) =
        (C * kt x) * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) by ring]
      refine mul_le_mul_of_nonneg_right ?_ hn
      dsimp only [C]
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left (hck x hx) (le_max_right _ _)
    · dsimp only [w]; rw [hg0 x hx, zero_mul, zero_mul, abs_zero]
      exact mul_nonneg hC0 (mul_nonneg (hd.ρ_nonneg x) (hk₁0 x))
  set F : ℂ → Measure ℂ → Measure ℂ → ℝ := fun x m₁ m₂ =>
    w x * (bpzMixedReal ρ k₁ k₂ m₁ m₂ ^ (-q - s) * G x m₁ m₂)
  simp_rw [show ∀ ω, bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
      ∫ x, g x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) *
        G x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω =
      ∫ x, F x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω from fun ω => by
    rw [← integral_const_mul]; congr 1; ext x; dsimp [F, w]; ring]
  have hImeas : Measurable fun ω => bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) :=
    (measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas).comp
      ((regularizedGMC_measurable P X hp.hX Xc hp.hXc γ r).prodMk hp.hMm)
  have hFm : Measurable fun p : Ω × ℂ => F p.2 (regularizedGMC P Xc γ r p.1) (M p.1) :=
    (hwc.measurable.comp measurable_snd).mul (((hImeas.comp measurable_fst).pow_const _).mul hGm)
  have hFx (x : ℂ) : Measurable fun q' : Measure ℂ × Measure ℂ => F x q'.1 q'.2 :=
    measurable_const.mul (((measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas).pow_const _).mul (hGx x))
  obtain ⟨cI, hcI, hlowI⟩ := bpzWard_mixed_lower hd hp k₁ hk₁0 (P := P) (Xc := Xc) (r := r)
  have hInt1 := bpzWard_integrable_rpow_neg hp hd.D_meas hImeas.aestronglyMeasurable hcI hlowI
    (p := q - 1) (by linarith [hd.q_ge])
  have hcut' : ∀ᵐ ω ∂P, Integrable (fun y => ρ y * k₁ y) (regularizedGMC P Xc γ r ω) := by
    filter_upwards [bpzWard_cut_integrable hd hp] with ω hω
    refine hω.mono' (hd.ρ_meas.mul hk₁m).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have h0 := mul_nonneg (hd.ρ_nonneg y) (hk₁0 y)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact le_mul_of_one_le_right h0 (Real.one_le_exp (mul_nonneg (sq_nonneg γ)
      (integral_nonneg fun a => Real.log_nonneg (bpz_one_le_normPlus a))))
  have hint : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |F x (regularizedGMC P Xc γ r ω) (M ω)|
      ∂regularizedGMC P Xc γ r ω ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun ω => ENNReal.ofReal (C * K *
        bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-(q - 1)))) ?_) ?_
    · filter_upwards [hcut', hlowI, bpzWard_far_mass_pos hp hd.D_meas, hp.k₂_int] with
        ω hρk hlow hpos hk₂i
      set I := bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω)
      have hIpos : 0 < I := (mul_pos hcI hpos).trans_le hlow
      have hIq : 0 ≤ I ^ (-q) := Real.rpow_nonneg hIpos.le _
      have hpt (x : ℂ) : |F x (regularizedGMC P Xc γ r ω) (M ω)| ≤
          (C * K * I ^ (-q)) * (ρ x * k₁ x) := by
        show |w x * (I ^ (-q - s) * G x (regularizedGMC P Xc γ r ω) (M ω))| ≤ _
        rw [abs_mul (w x), abs_mul (I ^ (-q - s)), abs_of_nonneg (Real.rpow_nonneg hIpos.le _)]
        have hGI : I ^ (-q - s) * |G x (regularizedGMC P Xc γ r ω) (M ω)| ≤ K * I ^ (-q) :=
          (mul_le_mul_of_nonneg_left (hGbd _ _ x hρk hk₂i) (Real.rpow_nonneg hIpos.le _)).trans_eq
            (by rw [mul_left_comm, ← Real.rpow_add hIpos]; ring_nf)
        exact (mul_le_mul (hCw x) hGI (mul_nonneg (Real.rpow_nonneg hIpos.le _) (abs_nonneg _))
          (mul_nonneg hC0 (mul_nonneg (hd.ρ_nonneg x) (hk₁0 x)))).trans_eq (by ring)
      refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)).trans ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hρk.const_mul _) (Eventually.of_forall fun y =>
          mul_nonneg (mul_nonneg (mul_nonneg hC0 hK0) hIq) (mul_nonneg (hd.ρ_nonneg y) (hk₁0 y))),
        integral_const_mul]
      refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (c := I) ?_
        (mul_nonneg (mul_nonneg hC0 hK0) hIq)).trans_eq ?_)
      · show ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω ≤
          ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω + ∫ y, (1 - ρ y) * k₂ y ∂M ω
        exact le_add_of_nonneg_right (integral_nonneg fun y =>
          mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y))
      · rw [mul_assoc, ← Real.rpow_add_one hIpos.ne']; congr 2; ring
    · rw [← ofReal_integral_eq_lintegral_ofReal (hInt1.const_mul (C * K)) (Eventually.of_forall fun ω =>
        mul_nonneg (mul_nonneg hC0 hK0) (Real.rpow_nonneg (add_nonneg
          (integral_nonneg fun y => mul_nonneg (hd.ρ_nonneg y) (hk₁0 y))
          (integral_nonneg fun y => mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y))) _))]
      exact ENNReal.ofReal_lt_top
  rw [bpz_cutoff_deroot_real P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc r F hFm hFx hint]
  congr 1; ext x
  have hstep (ω : Ω) : F x ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
      ((M ω).withDensity (bpzLimRootDensity γ r x)) =
        w x * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) *
          (bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
            G₀ x (regularizedGMC P Xc γ r ω) (M ω)) := by
    dsimp only [F]
    rw [bpzMixedReal_tilt, hGtilt, Real.mul_rpow (Real.exp_pos _).le
      (bpzRootedMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg x _ _), ← Real.exp_mul]
    have hexp : Real.exp ((γ ^ 2 * bpzPin r x) * (-q - s)) * Real.exp (s * (γ ^ 2 * bpzPin r x)) =
        Real.exp (-(q * (γ ^ 2 * bpzPin r x))) := by rw [← Real.exp_add]; congr 1; ring
    calc w x * (Real.exp ((γ ^ 2 * bpzPin r x) * (-q - s)) *
          bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
          (Real.exp (s * (γ ^ 2 * bpzPin r x)) * G₀ x (regularizedGMC P Xc γ r ω) (M ω)))
        = w x * (Real.exp ((γ ^ 2 * bpzPin r x) * (-q - s)) * Real.exp (s * (γ ^ 2 * bpzPin r x))) *
          (bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
            G₀ x (regularizedGMC P Xc γ r ω) (M ω)) := by ring
      _ = _ := by rw [hexp]
  simp_rw [hstep, integral_const_mul]
  have hn : normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add (bpz_normPlus_pos x)]; norm_num
  have he : Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  dsimp only [w]
  linear_combination (norm := ring)
    (g x * (Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x)))) *
      ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
        G₀ x (regularizedGMC P Xc γ r ω) (M ω) ∂P) * hn +
    (g x * ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - s) *
      G₀ x (regularizedGMC P Xc γ r ω) (M ω) ∂P) * he

/-- The left side of the cutoff Ward identity, rooted at the integration point. -/
theorem bpzWard_left_deroot (v : ℂ) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) *
        ∫ x, bpzWardLeftWeight γ q r kt φ v x ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, fderiv ℝ (fun x => φ x * kt x) x v *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P := by
  have hgc : Continuous fun x => fderiv ℝ (fun x => φ x * kt x) x v :=
    (hd.f_C1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨Cf, hCf⟩ := hgc.bounded_above_of_compact_support
    ((hd.φ_compact.mul_right.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp))
  have h := bpzWard_deroot_master hd hp (fun x => fderiv ℝ (fun x => φ x * kt x) x v) hgc
    (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx ((tsupport_fderiv_subset ℝ).trans
        (tsupport_mul_subset_left (f := φ) (g := kt)) h)]; rfl)
    (fun x => by rw [← Real.norm_eq_abs]; exact hCf x)
    0 1 zero_le_one (fun _ _ _ => 1) (fun _ _ _ => 1) measurable_const (fun _ => measurable_const)
    (fun _ _ _ _ _ => by simp) (fun _ _ _ => by simp)
  simpa [bpzWardLeftWeight] using h

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
  obtain ⟨B, hB⟩ := hd.f_C1.continuous.bounded_above_of_compact_support hd.φ_compact.mul_right
  have h := bpzWard_deroot_master hd hp (fun x => φ x * kt x) hd.f_C1.continuous
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
    (fun x => by rw [← Real.norm_eq_abs]; exact hB x)
    1 (γ ^ 2 * Real.exp r * ‖v‖) (by positivity)
    (fun x m₁ m₂ => bpzMixedDerivReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x v m₁ m₂)
    (fun x m₁ m₂ => bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x v m₁ m₂)
    (measurable_bpzWard_Yhat (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
      hd.ρ_meas (measurable_bpzWardCutWeight hd) hd.k₂_meas v)
    (fun x => measurable_bpzMixedDerivReal hd.ρ_meas (measurable_bpzWardCutWeight hd) hd.k₂_meas x v)
    (fun m₁ m₂ x h₁ h₂ => by
      rw [Real.rpow_one]
      exact abs_bpzMixedDerivReal_le hd.ρ_nonneg hd.ρ_le_one (bpzWardCutWeight_nonneg hd)
        hd.k₂_nonneg h₁ h₂ x v)
    (fun x m₁ m₂ => by rw [one_mul]; exact bpzMixedDerivReal_tilt _ _ _ _ _ _ _ _ _)
  convert h using 1; congr 1; ext ω; congr 1; refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [bpzWardCutWeight]; ring

end

end DOZZ.Proofs
