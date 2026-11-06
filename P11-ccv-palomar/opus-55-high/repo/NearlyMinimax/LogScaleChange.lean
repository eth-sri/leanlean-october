module

public import NearlyMinimax.ExponentialOrthantTail
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual multivariable logarithmic change of variables for the cardinal
scale integrals. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 400000
𝛑

𝗇 𝔄 Real.exp $ s j
𝗇 𝔅 𝙛
def exponentialScaleMap (s : 𝔅) : 𝔅 := fun j => 𝔄 - 1

def exponentialScaleDerivative (s : 𝔅) : 𝔅 →L[ℝ] 𝔅 :=
  ContinuousLinearMap.pi fun j => 𝔄 • ContinuousLinearMap.proj j

theorem exponential_scale_hasFDerivAt (s : 𝔅) :
    HasFDerivAt exponentialScaleMap (exponentialScaleDerivative s) s := by
  apply hasFDerivAt_pi.mpr
  intro j
  have h : HasFDerivAt (fun x => Real.exp $ x j )
      (𝔄 • ContinuousLinearMap.proj (R := ℝ) j ) s := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp $ s j ).comp_hasFDerivAt s $ hasFDerivAt_apply j s
  exact h.sub_const 1

𝗇 𝔍 ∏ j, 𝔄
𝗇 𝔎 (exponentialScaleDerivative s).det
theorem exponential_scale_derivative_det (s : 𝔅) :
    𝔎 = 𝔍 := by
  have he : (exponentialScaleDerivative s).toLinearMap =
      LinearMap.pi fun j => (𝔄 • LinearMap.id).comp $ LinearMap.proj j := by
    rfl
  change (exponentialScaleDerivative s).toLinearMap.det = _
  rw [he, LinearMap.det_pi]
  simp

theorem exponential_scale_injective : Function.Injective (exponentialScaleMap : 𝔅 → 𝔅) := by
  intro s t h
  funext j
  apply Real.exp_injective
  have hj := congrFun h j
  change 𝔄 - 1 = Real.exp (t j) - 1 at hj
  linarith

𝗇 𝔇 𝗴₂
theorem exponential_scale_image_orthant :
    exponentialScaleMap '' Ici 0 = Ici (0 : 𝔅) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    intro j
    have hsj := hs j
    change 0 ≤ 𝔄 - 1
    simpa
  · intro ht
    refine ⟨fun j => Real.log 𝔇, ?_, ?_⟩
    · intro j
      have htj : 𝖥₂ := ht j
      exact Real.log_nonneg 𝖡₄
    · funext j
      have htj : 𝖥₂ := ht j
      change Real.exp (Real.log 𝔇) - 1 = t j
      rw [Real.exp_log 𝖡₄ ]
      ring

𝗇 𝔉 fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt
𝗇 𝔊 Finset.prod_nonneg fun j _ => Real.exp_nonneg _
𝗇 𝔐 𝔍 * f (exponentialScaleMap s)
𝗃 𝔓 ἀ volume (s := Ici 0) measurableSet_Ici 𝔉 exponential_scale_injective.injOn f
/-- Change of variables for every actual Bochner integrand, over the entire
positive orthant. -/
theorem integral_exponential_scale_change (f : 𝔅 → ℝ) :
     ∫ t : 𝔅 in Ici 0, f t =
      ∫ s : 𝔅 in Ici 0, 𝔐 := by
  have h := 𝔓 integral_image_eq_integral_abs_det_fderiv_smul
  rw [exponential_scale_image_orthant] at h
  have hdet : ∀ s : 𝔅, |𝔎| = 𝔍 := by
    intro s
    rw [exponential_scale_derivative_det, abs_of_nonneg 𝔊]
  simp_all

theorem integrableOn_exponential_scale_change_iff f :
    IntegrableOn f (Ici 0) ↔
      IntegrableOn (fun s : 𝔅 => 𝔐) (Ici 0) := by
  have h := 𝔓 integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
  rw [exponential_scale_image_orthant] at h
  have hdet : ∀ s : 𝔅, |𝔎| = 𝔍 := by
    intro s
    rw [exponential_scale_derivative_det, abs_of_nonneg 𝔊]
  simp_all

/-- The closed logarithmic scale tail with its actual power-law integrand. -/
def logScaleTail (b A : ℝ) (t : 𝔅) : ℝ :=
  if A ≤ ∑ j, Real.log 𝔇 then ∏ j, 𝔇 ^ (-b - 1 : ℝ) else 0

𝗇 𝔑 logScaleTail b A
𝗇 𝔏 𝔍 * 𝔑 (exponentialScaleMap s)
theorem log_scale_tail_change_pointwise b A (s : 𝔅) :
    𝔏 =
      if A ≤ ∑ j, s j then Real.exp $ -(b * ∑ j, s j) else 0 := by
  have he : ∀ j , 1 + exponentialScaleMap s j = 𝔄 := by
    intro j
    unfold exponentialScaleMap
    ring
  unfold logScaleTail
  simp_rw [he, Real.log_exp]
  split_ifs
  · rw [← Finset.prod_mul_distrib]
    have hp : ∀ j , 𝔄 * 𝔄 ^ (-b - 1) =
        Real.exp (-(b * s j)) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      ring
    simp_rw [hp]
    rw [← Real.exp_sum]
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  simp

theorem finite_log_scale_tail_integral b A :
     ∫ t : 𝚟₂ in Ici 0, 𝔑 t =
      ∫ s : 𝚟₂, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin q) := by
  rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall $ log_scale_tail_change_pointwise b A

𝗇 𝔒 𝘻
𝗇 𝔈 Fin 𝔒 → ℝ
theorem finite_log_scale_tail_integrable (hb : 𝙴₁) A :
    IntegrableOn (𝔑 : 𝔈 → ℝ) $ Ici 0 := by
  apply (integrableOn_exponential_scale_change_iff _).mpr
  have h := finite_orthant_tail_integrable (m := m) hb A
  rw [exponential_orthant_measure_eq_restrict] at h
  have he : (fun s : 𝔈 => 𝔏) = finiteOrthantTail b A := by
    funext s
    exact log_scale_tail_change_pointwise b A s
  aesop

/-- Quantitative logarithmic-simplex tail with the actual scale Jacobian. -/
theorem finite_log_scale_tail_integral_uniform
    (hb : 𝙖 ≤ b) (hA : 𝖲₁) :
     ∫ t : 𝔈 in Ici 0, 𝔑 t ≤
      8 ^ 𝔒 * Real.exp (-(b * A)) * (1 + A) ^ m := by
  rw [finite_log_scale_tail_integral]
  exact finite_orthant_tail_integral_uniform hb hA
