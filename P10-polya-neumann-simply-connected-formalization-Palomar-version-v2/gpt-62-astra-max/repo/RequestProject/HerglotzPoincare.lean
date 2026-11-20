module

public import RequestProject.L2Identities

public import RequestProject.Finite

public import RequestProject.Poincare
public import RequestProject.Herglotz
public import RequestProject.PlanarNotation

/-!
# Poincaré inequalities for Herglotz coefficients

* `poincare_C1`: on a bounded Lipschitz domain, a `C¹` function `f` on `ℂ` with bounded value
  and bounded derivative and `∫_Ω f = 0` satisfies `∫_Ω |f|² ≤ C ∫_Ω (|∂ₓf|² + |∂ᵧf|²)`.
* `poincare_C1_ball`: the same with the normalization `∫_B f = 0` on a ball `B ⊆ Ω`.
* For the Herglotz coefficients, `|∂ₓF_m|² + |∂ᵧF_m|² = (k²/2)(|F_{m+1}|² + |F_{m-1}|²)`
  (`sum_sq_fderiv_herglotzCoeff`), which gives `poincare_herglotzCoeff` and
  `poincare_herglotzCoeff_ball`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

/-- The squared gradient `|∂ₓf|² + |∂ᵧf|²`. -/
def gradSq (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2

lemma memLp_of_continuous_bounded (hb : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    MemLp f 2 (volume.restrict Ω) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact MemLp.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)

/-- The C¹ Poincaré estimate on `Ω` with the normalization imposed on `s`. -/
def C1PoincareOn (Ω s : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → (∃ B, ∀ z, ‖f z‖ ≤ B) →
      (∃ B, ∀ z, ‖fderiv ℝ f z‖ ≤ B) → ∫ z in s, f z = 0 →
        ∫ z in Ω, ‖f z‖ ^ 2 ≤ C * ∫ z in Ω, gradSq f z

section

variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
include hL hb

/-- **Poincaré–Wirtinger for `C¹` functions.** -/
theorem poincare_C1 :
    C1PoincareOn Ω Ω := by
  obtain ⟨C, hC, hP⟩ := poincare_wirtinger hb hL
  refine ⟨C, hC, fun f hf ⟨B, hB⟩ ⟨B', hB'⟩ h0 => ?_⟩
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hu  := memLp_of_continuous_bounded hb hf.continuous hB
  have hdc : ∀ v : ℂ, Continuous fun w => fderiv ℝ f w v := (by fun_prop)
  have hdB : ∀ v : ℂ, ∀ w, ‖fderiv ℝ f w v‖ ≤ B' * ‖v‖ := fun v w =>
    ((fderiv ℝ f w).le_opNorm v).trans (by gcongr; exact hB' w)
  have hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω) := fun i =>
    memLp_of_continuous_bounded hb (hdc _) (hdB _)
  have hW := isWeakGradient_of_contDiff_one hf hu hg
  have hmean : ∫ w in Ω, (hu.toLp f : L2 Ω) w = 0 := by
    rw [integral_congr_ae hu.coeFn_toLp]; exact h0
  have key := hP _ _ hW hmean
  rw [norm_sq_toLp_eq_integral, Fin.sum_univ_two, norm_sq_toLp_eq_integral, norm_sq_toLp_eq_integral] at key
  exact (integral_add (hg 0).norm.integrable_sq (hg 1).norm.integrable_sq).symm ▸ key

/-- **Poincaré inequality with a ball normalization.** If `B = ball z₁ r ⊆ Ω`, a `C¹` function
with bounded value and derivative and `∫_B f = 0` satisfies `∫_Ω |f|² ≤ C ∫_Ω |∇f|²`. -/
theorem poincare_C1_ball {z₁ : ℂ}
    {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    C1PoincareOn Ω (ball z₁ r) := by
  obtain ⟨CP, hCP, hP⟩ := poincare_C1 hb hL
  have hΩfin : volume Ω < ⊤ := hb.measure_lt_top
  have hBfin : volume (ball z₁ r) < ⊤ := measure_ball_lt_top
  set VΩ := (volume Ω).toReal with hVΩ
  set VB := (volume (ball z₁ r)).toReal with hVB
  have hVB  := ENNReal.toReal_pos (measure_ball_pos volume z₁ hr).ne' hBfin.ne
  have hVΩ0 : 0 < VΩ := ENNReal.toReal_pos (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hΩfin.ne
  refine ⟨(2 + 2 * VΩ / VB) * CP, by positivity, fun f hf ⟨B, hB⟩ hd h0 => ?_⟩
  
  haveI  := isFiniteMeasure_restrict.mpr hΩfin.ne
  haveI  := isFiniteMeasure_restrict.mpr hBfin.ne
  set μ : ℂ := (∫ z in Ω, f z) / (VΩ : ℂ) with hμ
  set g : ℂ → ℂ := fun z => f z - μ with hg
  have hgc : Continuous g := hf.continuous.sub continuous_const
  have hgB : ∀ z, ‖g z‖ ≤ B + ‖μ‖ := fun z => (norm_sub_le _ _).trans (by simp [*])
  have hfm := memLp_of_continuous_bounded hb hf.continuous hB
  have hgm := memLp_of_continuous_bounded hb hgc hgB
  have restrictBall := Measure.restrict_mono_set volume hball
  have hgd : ∀ z, fderiv ℝ g z = fderiv ℝ f z := fun z => by
    exact fderiv_sub_const _
  have hgrad : ∀ z, gradSq g z = gradSq f z := fun z => by simp [gradSq, hgd]
  have hint_const : ∀ s : Set ℂ, ∫ _ in s, μ = (volume s).toReal * μ := fun s => by
    simp [integral_const, Measure.real_def, univ_inter, Complex.real_smul]
  have hg0 : ∫ z in Ω, g z = 0 := by
    rw [hg, integral_sub (hfm.integrable (by norm_num)) (integrable_const _), hint_const]
    have hne : (VΩ : ℂ) ≠ 0 := by exact_mod_cast hVΩ0.ne'
    rw [← hVΩ, hμ, mul_div_cancel₀ _ hne, sub_self]
  have hS := hP g (hf.sub contDiff_const) ⟨_, hgB⟩ ⟨_, fun z => (hgd z).symm ▸ hd.choose_spec z⟩ hg0
  simp only [hgrad] at hS
  set S := ∫ z in Ω, ‖g z‖ ^ 2 with hSdef
  have hgB0 : ∫ z in ball z₁ r, g z = -(VB * μ) := by
    rw [hg, integral_sub ((hfm.mono_measure restrictBall).integrable (by norm_num)) (integrable_const _), hint_const, h0, zero_sub]
  have hmono : ∫ z in ball z₁ r, ‖g z‖ ^ 2 ≤ S :=
    integral_mono_measure restrictBall (.of_forall fun _ => sq_nonneg _) hgm.norm.integrable_sq
  have hμ2 : ‖μ‖ ^ 2 * VB ≤ S := by
    have hCS := norm_sq_integral_le (hgm.mono_measure restrictBall)
    rw [hgB0, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hVB.le,
      measureReal_restrict_apply_univ] at hCS
    change (VB * ‖μ‖) ^ 2 ≤ VB * _ at hCS
    nlinarith [hCS.trans (mul_le_mul_of_nonneg_left hmono hVB.le)]
  have hfg : ∫ z in Ω, ‖f z‖ ^ 2 ≤ 2 * S + 2 * ‖μ‖ ^ 2 * VΩ := by
    have hpt : ∀ z, ‖f z‖ ^ 2 ≤ 2 * ‖g z‖ ^ 2 + 2 * ‖μ‖ ^ 2 := fun z => by
      have : f z = g z + μ := by simp [hg]
      rw [this]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (g z) μ) 2
      nlinarith [sq_nonneg (‖g z‖ - ‖μ‖)]
    calc _ ≤ ∫ z in Ω, (2 * ‖g z‖ ^ 2 + 2 * ‖μ‖ ^ 2) :=
          integral_mono hfm.norm.integrable_sq
            ((hgm.norm.integrable_sq.const_mul 2).add
              (integrable_const _)) hpt
      _ = _ := by
          rw [integral_add (hgm.norm.integrable_sq.const_mul 2)
            (integrable_const _), integral_const_mul, integral_const, smul_eq_mul,
            Measure.real_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
          ring
  
  have hμ2' : ‖μ‖ ^ 2 ≤ S / VB := by rw [le_div_iff₀ hVB]; exact hμ2
  calc _ ≤ 2 * S + 2 * ‖μ‖ ^ 2 * VΩ := hfg
    _ ≤ 2 * S + 2 * (S / VB) * VΩ := by gcongr
    _ = (2 + 2 * VΩ / VB) * S := by ring
    _ ≤ (2 + 2 * VΩ / VB) * (CP * ∫ z in Ω, gradSq f z) := by gcongr
    _ = _ := by ring

end

section Herglotz

variable {a : ℝ → ℂ}

section

variable (ha : IntervalIntegrable a volume 0 anglePeriod) (k : ℝ) (m : ℤ)
include ha

lemma contDiff_herglotzCoeff :
    ContDiff ℝ 1 (herglotzCoeff k a m) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨differentiable_herglotzCoeff ha k m, ?_⟩
  have hfd : fderiv ℝ (herglotzCoeff k a m) = fun z =>
      (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) • ContinuousLinearMap.id ℝ ℂ +
      (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) •
        Complex.conjCLE.toContinuousLinearMap := by
    funext z
    ext1 w
    rw [fderiv_herglotzCoeff_apply ha]
    simp [smul_eq_mul] <;> ring
  rw [hfd]
  have h1 := continuous_herglotzCoeff ha k (m + 1)
  have h2 := continuous_herglotzCoeff ha k (m - 1)
  fun_prop

lemma gradSq_herglotzCoeff
    (z : ℂ) : gradSq (herglotzCoeff k a m) z =
      k ^ 2 / 2 * (‖herglotzCoeff k a (m + 1) z‖ ^ 2 + ‖herglotzCoeff k a (m - 1) z‖ ^ 2) := by
  unfold gradSq
  rw [fderiv_herglotzCoeff_apply ha, fderiv_herglotzCoeff_apply ha]
  set A := herglotzCoeff k a (m + 1) z
  set B := herglotzCoeff k a (m - 1) z
  have hc : ‖-(Complex.I * k / 2)‖ = |k| / 2 := by
    norm_num
  have e2 : Complex.I * A + conj Complex.I * B = Complex.I * (A - B) := by
    rw [Complex.conj_I]; ring
  simp only [one_mul, map_one, norm_mul, hc, e2, Complex.norm_I]
  have hpar : ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    have := parallelogram_law_with_norm ℝ A B
    nlinarith
  have hk  := sq_abs k
  nlinarith

end

/-- Poincaré for adjacent Herglotz modes, with a zero mode integral on `s`. -/
def HerglotzPoincareOn (Ω s : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℂ), IntervalIntegrable a volume 0 anglePeriod → ∀ (k : ℝ) (m : ℤ),
      ∫ z in s, herglotzCoeff k a m z = 0 →
        ∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2 ≤
          C * (k ^ 2 / 2 * ∫ z in Ω, (‖herglotzCoeff k a (m + 1) z‖ ^ 2 +
            ‖herglotzCoeff k a (m - 1) z‖ ^ 2))

lemma C1PoincareOn.herglotz {s : Set ℂ} (h : C1PoincareOn Ω s) : HerglotzPoincareOn Ω s := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨C, hC, fun a ha k m h0 => ?_⟩
  have := hP _ (contDiff_herglotzCoeff ha k m) ⟨_, norm_herglotzCoeff_le k m⟩
    ⟨_, norm_fderiv_herglotzCoeff_le ha k m⟩ h0
  simp only [gradSq_herglotzCoeff ha] at this
  rwa [integral_const_mul] at this

section

variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
include hL hb

/-- **Poincaré for Herglotz coefficients** (zero mean over `Ω`). -/
theorem poincare_herglotzCoeff :
    HerglotzPoincareOn Ω Ω := (poincare_C1 hb hL).herglotz

/-- **Poincaré for Herglotz coefficients** (zero mean over a ball `B ⊆ Ω`). -/
theorem poincare_herglotzCoeff_ball
    {z₁ : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    HerglotzPoincareOn Ω (ball z₁ r) := (poincare_C1_ball hb hL hr hball).herglotz

end

end Herglotz

end PolyaNeumann
