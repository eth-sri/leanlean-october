module

public import RequestProject.Poincare
public import RequestProject.Finite
public import RequestProject.Herglotz

/-! Poincaré estimates for Herglotz coefficients normalized on a subset of the domain. -/

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

private theorem poincare_C1 (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ Ω) (hpos : volume s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → (∃ B, ∀ z, ‖f z‖ ≤ B) →
      (∃ B, ∀ z, ‖fderiv ℝ f z‖ ≤ B) → ∫ z in s, f z = 0 →
        ∫ z in Ω, ‖f z‖ ^ 2 ≤ C * ∫ z in Ω, gradSq f z := by
  obtain ⟨C, hC, hP⟩ := poincare_wirtinger hb hL hs hsub hpos
  refine ⟨C, hC, fun f hf ⟨_, hB⟩ ⟨B', hB'⟩ h0 => ?_⟩
  have hu := memLp_of_continuous_bounded hb hf.continuous hB
  have hg (v : ℂ) : MemLp (fun w => fderiv ℝ f w v) 2 (volume.restrict Ω) :=
    memLp_of_continuous_bounded hb ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      (B := B' * ‖v‖) fun w => ((fderiv ℝ f w).le_opNorm v).trans (by gcongr; exact hB' _)
  have hmean : ∫ w in s, (hu.toLp f : L2 Ω) w = 0 :=
    (integral_congr_ae (hu.coeFn_toLp.filter_mono (ae_mono
      (Measure.restrict_mono_set volume hsub)))).trans h0
  have h := hP _ _ (isWeakGradient_of_contDiff_one hf hu (fun i => hg (coordDir i))) hmean
  rw [norm_sq_toLp_eq_integral, Fin.sum_univ_two, norm_sq_toLp_eq_integral,
    norm_sq_toLp_eq_integral] at h
  have hi (v : ℂ) := (show MemLp _ (2 : ℕ) _ from hg v).integrable_norm_pow (by decide)
  unfold gradSq
  rwa [integral_add (hi 1) (hi Complex.I)]

/-- Cauchy–Schwarz against the constant function on a finite measure space. -/
lemma sq_integral_norm_le_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℂ} (hg : MemLp g 2 μ) :
    (∫ z, ‖g z‖ ∂μ) ^ 2 ≤ μ.real univ * ∫ z, ‖g z‖ ^ 2 ∂μ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    Real.HolderConjugate.two_two (f := fun _ => (1 : ℂ)) (g := g)
    (memLp_const 1) (by simpa using hg)
  simp only [norm_one, one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one,
    one_pow, Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have hs := pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) h 2
  rwa [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hs

section Herglotz

variable {a : ℝ → ℂ}

section

variable (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ)
include ha k m

lemma contDiff_herglotzCoeff  :
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
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply]
    ring
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
    simp
  have e2 : Complex.I * A + conj Complex.I * B = Complex.I * (A - B) := by
    grind [Complex.conj_I]
  simp only [one_mul, map_one, norm_mul, hc, e2, Complex.norm_I]
  have hpar : ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    have := parallelogram_law_with_norm ℝ A B
    nlinarith
  grind

end

section

variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
include hb hL

/-- Poincaré estimate for coefficients with zero mean on a positive-measure subset. -/
theorem poincare_herglotzCoeff {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ Ω)
    (hpos : volume s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℂ), IntervalIntegrable a volume 0 (2 * π) → ∀ (k : ℝ) (m : ℤ),
      ∫ z in s, herglotzCoeff k a m z = 0 →
        ∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2 ≤
          C * (k ^ 2 / 2 * ∫ z in Ω, (‖herglotzCoeff k a (m + 1) z‖ ^ 2 +
            ‖herglotzCoeff k a (m - 1) z‖ ^ 2)) := by
  obtain ⟨C, hC, hP⟩ := poincare_C1 hb hL hs hsub hpos
  refine ⟨C, hC, fun a ha k m h0 => ?_⟩
  have := hP _ (contDiff_herglotzCoeff ha k m) ⟨_, norm_herglotzCoeff_le k m⟩
    ⟨_, norm_fderiv_herglotzCoeff_le ha k m⟩ h0
  simp  [gradSq_herglotzCoeff ha] at this
  rwa [integral_const_mul] at this

end

end Herglotz

end PolyaNeumann
