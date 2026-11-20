module

public import RequestProject.CircleFourier
public import RequestProject.HerglotzSchurPos

/-!
# Herglotz data with vanishing negative modes at an interior point

Fix points `z₀, z₁`. For `v ∈ ℓ²(ℕ₀)` we synthesize an `L²` density `a_v` (`synthDens`) whose
Herglotz coefficients at `z₁` are `F_n(z₁) = v_n` (`n ≥ 1`), `F₀(z₁) = √2 v₀`, `F_{-j}(z₁) = 0`
(`j ≥ 1`), so that `y_{a_v}(z₁) = v`. The map `T v = y_{a_v}(z₀)` is linear with
`‖T − I‖ ≤ √2 |k| |z₀ − z₁|` (`norm_one_sub_synthOp_le`), hence onto for small `k`. Adjusting along
`e₀` we obtain, for small `k`, for every `w` a density with vanishing negative modes at `z₁`,
zero mean of `u_a` over a bounded `Ω`, and `y_a(z₀) = w + t e₀` (`exists_admissible_herglotzVec`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section
namespace PolyaNeumann

lemma herglotzCoeff_congr_ae {a b : ℝ → ℂ} (h : a =ᵐ[volume.restrict (Ioc 0 (2 * π))] b)
    (k : ℝ) (m : ℤ) (z : ℂ) : herglotzCoeff k a m z = herglotzCoeff k b m z := by
  unfold herglotzCoeff
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity)]
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h
  filter_upwards [h] with x; simp_all

lemma herglotzVec_congr_ae {a b : ℝ → ℂ} (ha : IsDirDensity a) (hb : IsDirDensity b)
    (h : a =ᵐ[volume.restrict (Ioc 0 (2 * π))] b) (k : ℝ) (z : ℂ) :
    herglotzVec ha k z = herglotzVec hb k z := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply, herglotzVec_apply]
  unfold herglotzSeq
  simp  [herglotzCoeff_congr_ae h]

/-- Pull back an a.e. statement on the circle to the parameter interval. -/
lemma ae_restrict_Ioc_of_ae_haar {p : AddCircle (2 * π) → Prop}
    (h : ∀ᵐ x ∂(@AddCircle.haarAddCircle (2 * π) _), p x) :
    ∀ᵐ φ : ℝ ∂(volume.restrict (Ioc 0 (2 * π))), p φ := by
  have hv : ∀ᵐ x ∂(volume : Measure (AddCircle (2 * π))), p x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  have := (AddCircle.measurePreserving_mk (2 * π) 0).quasiMeasurePreserving.ae hv
  simpa using this

section Synth

lemma norm_sq_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2 =
      ‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2 := by
  have h1 := hasSum_sq_herglotzCoeff (isDirDensity_synthDens k z₁ v) k z₁
  simp only [herglotzCoeff_synthDens] at h1
  exact h1.unique (hasSum_sq_synthCoeff v)

lemma synthDens_add_ae (k : ℝ) (z₁ : ℂ) (v w : Ell2) :
    synthDens k z₁ (v + w) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      synthDens k z₁ v + synthDens k z₁ w := by
  have h := Lp.coeFn_add (synthL2 v) (synthL2 w)
  rw [← synthL2_add] at h
  filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
  simp  [synthDens, Pi.add_apply, hφ, add_mul]

lemma synthDens_smul_ae (k : ℝ) (z₁ : ℂ) (c : ℂ) (v : Ell2) :
    synthDens k z₁ (c • v) =ᵐ[volume.restrict (Ioc 0 (2 * π))] c • synthDens k z₁ v := by
  have h := Lp.coeFn_smul c (synthL2 v)
  rw [← synthL2_smul] at h
  filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
  simp  [synthDens, Pi.smul_apply, hφ, smul_eq_mul, mul_assoc]

lemma herglotzVec_synthDens_add (k : ℝ) (z₁ : ℂ) (v w : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (v + w)) k z =
      herglotzVec (isDirDensity_synthDens k z₁ v) k z +
        herglotzVec (isDirDensity_synthDens k z₁ w) k z := by
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).add (isDirDensity_synthDens k z₁ w))
    (synthDens_add_ae k z₁ v w), herglotzVec_add]

lemma herglotzVec_synthDens_smul (k : ℝ) (z₁ : ℂ) (c : ℂ) (v : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (c • v)) k z =
      c • herglotzVec (isDirDensity_synthDens k z₁ v) k z := by
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).const_smul c)
    (synthDens_smul_ae k z₁ c v), herglotzVec_smul]

end Synth
section Op

/-- `v ↦ y_{a_v}(z₀)`, where `a_v` is the synthesized density based at `z₁`. -/
def synthOpLin (k : ℝ) (z₁ z₀ : ℂ) : Ell2 →ₗ[ℂ] Ell2 where
  toFun v := herglotzVec (isDirDensity_synthDens k z₁ v) k z₀
  map_add' v w := herglotzVec_synthDens_add k z₁ v w z₀
  map_smul' c v := herglotzVec_synthDens_smul k z₁ c v z₀

lemma norm_synthDens_sq_le (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_synthDens]
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) v 0
  nlinarith [norm_nonneg ((v : ℕ → ℂ) 0)]

lemma norm_herglotzVec_synthDens_sub_le (k : ℝ) (z₁ z : ℂ) (v : Ell2) :
    ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z - v‖ ≤
      |k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖ := by
  have h := norm_herglotzVec_sub_le (isDirDensity_synthDens k z₁ v) k z z₁
  rw [herglotzVec_synthDens] at h
  refine h.trans ?_
  have hs : Real.sqrt ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2) ≤
      Real.sqrt 2 * ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (norm_synthDens_sq_le k z₁ v)
  have := mul_le_mul_of_nonneg_left hs (abs_nonneg k)
  have := mul_le_mul_of_nonneg_right this (norm_nonneg (z - z₁))
  linarith [show |k| * (Real.sqrt 2 * ‖v‖) * ‖z - z₁‖ = |k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖ by ring]

/-- The synthesis operator as a bounded operator. -/
def synthOp (k : ℝ) (z₁ z₀ : ℂ) : Ell2 →L[ℂ] Ell2 :=
  (synthOpLin k z₁ z₀).mkContinuous (1 + |k| * Real.sqrt 2 * ‖z₀ - z₁‖) fun v => by
    have h := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
    have := norm_le_insert' (herglotzVec (isDirDensity_synthDens k z₁ v) k z₀) v
    show ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z₀‖ ≤ _
    linarith

lemma synthOp_apply (k : ℝ) (z₁ z₀ : ℂ) (v : Ell2) :
    synthOp k z₁ z₀ v = herglotzVec (isDirDensity_synthDens k z₁ v) k z₀ := rfl

lemma norm_one_sub_synthOp_le (k : ℝ) (z₁ z₀ : ℂ) :
    ‖1 - synthOp k z₁ z₀‖ ≤ |k| * Real.sqrt 2 * ‖z₀ - z₁‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, synthOp_apply, norm_sub_rev]
  have := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
  linarith [show |k| * Real.sqrt 2 * ‖v‖ * ‖z₀ - z₁‖ = |k| * Real.sqrt 2 * ‖z₀ - z₁‖ * ‖v‖ by ring]

lemma synthOp_surjective {k : ℝ} {z₁ z₀ : ℂ} (h : |k| * Real.sqrt 2 * ‖z₀ - z₁‖ < 1) :
    Function.Surjective (synthOp k z₁ z₀) := by
  have hu : IsUnit (synthOp k z₁ z₀) := by
    have := isUnit_one_sub_of_norm_lt_one ((norm_one_sub_synthOp_le k z₁ z₀).trans_lt h)
    simpa using this
  obtain ⟨S, hS⟩ := hu.exists_right_inv
  intro w
  refine ⟨S w, ?_⟩
  have := congrArg (fun T : Ell2 →L[ℂ] Ell2 => T w) hS
  simpa using this

end Op
end PolyaNeumann
