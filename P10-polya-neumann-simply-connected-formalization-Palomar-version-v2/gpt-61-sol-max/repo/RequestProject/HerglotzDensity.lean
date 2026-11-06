module

public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

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

noncomputable section
namespace PolyaNeumann



lemma herglotzCoeff_congr_ae  (h : a =ᵐ[volume.restrict boundaryHalfOpenInterval] b)
    k m z : herglotzCoeff k a m z = herglotzCoeff k b m z := by
  unfold herglotzCoeff
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity)]
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h
  filter_upwards [h] with φ hφ hmem
  rw [hφ hmem]

lemma herglotzVec_congr_ae  (ha : IsDirDensity a) (hb : IsDirDensity b)
    (h : a =ᵐ[volume.restrict boundaryHalfOpenInterval] b) k z :
    herglotzVec ha k z = herglotzVec hb k z := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply, herglotzVec_apply]
  grind only [herglotzSeq, herglotzCoeff_congr_ae]

/-- Pull back an a.e. statement on the circle to the parameter interval. -/
lemma ae_restrict_Ioc_of_ae_haar {p : AddCircle circlePeriod → Prop}
    (h : ∀ᵐ x ∂(@AddCircle.haarAddCircle circlePeriod _), p x) :
    ∀ᵐ φ : ℝ ∂(volume.restrict boundaryHalfOpenInterval), p φ := by
  have hv : ∀ᵐ x ∂(volume : Measure (AddCircle circlePeriod)), p x := by
    exact Measure.ae_smul_measure h _
  have := (AddCircle.measurePreserving_mk circlePeriod 0).quasiMeasurePreserving.ae hv
  simpa using this

section Synth

/-- The Fourier coefficients of the synthesized density: `c₀ = √2 v₀`, `c_n = v_n` (`n ≥ 1`),
`c_n = 0` (`n < 0`). -/
def synthCoeff (v : Ell2) (m : ℤ)  :=
  if m = 0 then (Real.sqrt 2 : ℂ) * (v : ComplexSeq) 0 else if 0 < m then (v : ComplexSeq) m.toNat else 0

lemma synthCoeff_add v w m :
    synthCoeff (v + w) m = synthCoeff v m + synthCoeff w m := by
  unfold synthCoeff; split_ifs <;> simp [mul_add]

lemma synthCoeff_smul (c : ℂ) (v : Ell2) (m : ℤ) :
    synthCoeff (c • v) m = c * synthCoeff v m := by
  unfold synthCoeff; split_ifs <;> simp; ring

lemma hasSum_sq_synthCoeff v :
    HasSum (fun m => ‖synthCoeff v m‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ComplexSeq) 0‖ ^ 2) := by
  have hv : HasSum (fun n : ℕ => ‖(v : ComplexSeq) n‖ ^ 2) (‖v‖ ^ 2) := by
    have := lp.hasSum_norm (p := 2) (by norm_num) v
    simpa [] using this
  have hpos : HasSum (fun n : ℕ => ‖synthCoeff v n‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ComplexSeq) 0‖ ^ 2) := by
    have h2 := hv.add (hasSum_ite_eq 0 (‖v 0‖ ^ 2))
    refine h2.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [synthCoeff, mul_pow]
      ring
    grind only [synthCoeff]
  have hneg : HasSum (fun n : ℕ => ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2) 0 := by
    have : ∀ n : ℕ, ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2 = 0 := fun n => by
      have h1 : -((n : ℤ) + 1) ≠ 0 := by omega
      simp_all [synthCoeff]
    simp only [this]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one (f := fun m => ‖synthCoeff v m‖ ^ 2) hpos hneg
  rwa [add_zero] at this

lemma memℓp_synthCoeff v : Memℓp (synthCoeff v) 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa  using (hasSum_sq_synthCoeff v).summable

/-- The synthesized `L²` function on the circle. -/
def synthL2 (v : Ell2) : Lp ℂ 2 (@AddCircle.haarAddCircle circlePeriod _) :=
  fourierBasis.repr.symm ⟨synthCoeff v, memℓp_synthCoeff v⟩

lemma synthL2_add v w : synthL2 (v + w) = synthL2 v + synthL2 w := by
  unfold synthL2
  rw [← map_add]
  congr 1
  exact lp.ext (funext (synthCoeff_add v w))

lemma synthL2_smul (c : ℂ) (v : Ell2) : synthL2 (c • v) = c • synthL2 v := by
  unfold synthL2
  rw [← map_smul]
  congr 1
  ext <;> simp_all [synthCoeff_smul, PolyaNeumann.Ell2]

lemma fourierCoeff_synthL2 v m : fourierCoeff (synthL2 v) m = synthCoeff v m := by
  rw [← fourierBasis_repr, synthL2, LinearIsometryEquiv.apply_symm_apply]

/-- The synthesized density, shifted to the base point `z₁`. -/
def synthDens k z₁ v (φ : ℝ)  :=
  (synthL2 v : AddCircle circlePeriod → ℂ) φ * planeWave k (-z₁) φ

section
variable (k : ℝ) (z₁ : ℂ) (v : Ell2)
include k z₁ v

lemma isDirDensity_synthDens : IsDirDensity (synthDens k z₁ v) := by
  have hfm : MemLp (synthL2 v : AddCircle circlePeriod → ℂ) 2 :=
    memLp_haarAddCircle_iff.mp (Lp.memLp _)
  have ha₀ : IsDirDensity fun φ : ℝ => (synthL2 v : AddCircle circlePeriod → ℂ) φ := by
    have := hfm.comp_measurePreserving (AddCircle.measurePreserving_mk circlePeriod 0)
    rw [zero_add] at this
    exact this
  exact ha₀.of_le ((MemLp.aestronglyMeasurable ha₀).mul (continuous_planeWave k (-z₁)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => by rw [synthDens, norm_mul, norm_planeWave, mul_one])

lemma herglotzCoeff_synthDens m :
    herglotzCoeff k (synthDens k z₁ v) m z₁ = synthCoeff v m := by
  unfold synthDens
  rw [herglotzCoeff_shift, herglotzCoeff_zero_eq_fourierCoeff, fourierCoeff_synthL2]

lemma herglotzCoeff_synthDens_neg (j : ℕ) (hj : 1 ≤ j) :
    herglotzCoeff k (synthDens k z₁ v) (-(j : ℤ)) z₁ = 0 := by
  grind only [herglotzCoeff_synthDens, synthCoeff]

lemma herglotzVec_synthDens :
    herglotzVec (isDirDensity_synthDens k z₁ v) k z₁ = v := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply]
  unfold herglotzSeq
  split_ifs with hn
  · simp_all [herglotzCoeff_synthDens, synthCoeff]
  simp_all [herglotzCoeff_synthDens, synthCoeff]

lemma norm_sq_synthDens :
    circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖synthDens k z₁ v φ‖ ^ 2 =
      ‖v‖ ^ 2 + ‖(v : ComplexSeq) 0‖ ^ 2 := by
  have h1 := hasSum_sq_herglotzCoeff (isDirDensity_synthDens k z₁ v) k z₁
  simp only [herglotzCoeff_synthDens] at h1
  exact h1.unique (hasSum_sq_synthCoeff v)

end


section
variable (k : ℝ) (z₁ : ℂ)
include k z₁

lemma synthDens_add_ae v w :
    synthDens k z₁ (v + w) =ᵐ[volume.restrict boundaryHalfOpenInterval]
      synthDens k z₁ v + synthDens k z₁ w := by
  have h := Lp.coeFn_add (synthL2 v) (synthL2 w)
  rw [← synthL2_add] at h
  filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
  simp  [synthDens, hφ, add_mul]

lemma synthDens_smul_ae (c : ℂ) (v : Ell2) :
    synthDens k z₁ (c • v) =ᵐ[volume.restrict boundaryHalfOpenInterval] c • synthDens k z₁ v := by
  have h := Lp.coeFn_smul c (synthL2 v)
  rw [← synthL2_smul] at h
  filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
  simp  [synthDens, hφ, mul_assoc]

lemma herglotzVec_synthDens_add v w z :
    herglotzVec (isDirDensity_synthDens k z₁ (v + w)) k z =
      herglotzVec (isDirDensity_synthDens k z₁ v) k z +
        herglotzVec (isDirDensity_synthDens k z₁ w) k z := by
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).add (isDirDensity_synthDens k z₁ w))
    (synthDens_add_ae k z₁ v w), herglotzVec_add]

lemma herglotzVec_synthDens_smul (c : ℂ) (v : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (c • v)) k z =
      c • herglotzVec (isDirDensity_synthDens k z₁ v) k z := by
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).const_smul c)
    (synthDens_smul_ae k z₁ c v), herglotzVec_smul]

end


end Synth

/-- `v ↦ y_{a_v}(z₀)`, where `a_v` is the synthesized density based at `z₁`. -/
def synthOpLin (k : ℝ) (z₁ z₀ : ℂ) : Ell2 →ₗ[ℂ] Ell2 where
  toFun v := herglotzVec (isDirDensity_synthDens k z₁ v) k z₀
  map_add' v w := herglotzVec_synthDens_add k z₁ v w z₀
  map_smul' c v := herglotzVec_synthDens_smul k z₁ c v z₀

lemma norm_synthDens_sq_le k z₁ v :
    circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖synthDens k z₁ v φ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_synthDens]
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) v 0
  nlinarith [norm_nonneg (v 0)]

lemma norm_herglotzVec_synthDens_sub_le k z₁ z v :
    ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z - v‖ ≤
      |k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖ := by
  have h := norm_herglotzVec_sub_le (isDirDensity_synthDens k z₁ v) k z z₁
  rw [herglotzVec_synthDens] at h
  have hs : Real.sqrt (circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖synthDens k z₁ v φ‖ ^ 2) ≤
      Real.sqrt 2 * ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (norm_synthDens_sq_le k z₁ v)
  have := mul_le_mul_of_nonneg_left hs (abs_nonneg k)
  have := mul_le_mul_of_nonneg_right this (norm_nonneg (z - z₁))
  linarith

/-- The synthesis operator as a bounded operator. -/
def synthOp (k : ℝ) (z₁ z₀ : ℂ) : ComplexEnd Ell2 :=
  (synthOpLin k z₁ z₀).mkContinuous (1 + |k| * Real.sqrt 2 * ‖z₀ - z₁‖) fun v => by
    have h := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
    have := norm_le_insert' (herglotzVec (isDirDensity_synthDens k z₁ v) k z₀) v
    show ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z₀‖ ≤ _
    nlinarith [norm_nonneg v]

lemma synthOp_apply k z₁ z₀ v :
    synthOp k z₁ z₀ v = herglotzVec (isDirDensity_synthDens k z₁ v) k z₀ := rfl

lemma norm_one_sub_synthOp_le k z₁ z₀ :
    ‖1 - synthOp k z₁ z₀‖ ≤ |k| * Real.sqrt 2 * ‖z₀ - z₁‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, synthOp_apply, norm_sub_rev]
  have := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
  linarith

lemma synthOp_surjective   (h : |k| * Real.sqrt 2 * ‖z₀ - z₁‖ < 1) :
    Function.Surjective (synthOp k z₁ z₀) := by
  have hu : IsUnit (synthOp k z₁ z₀) := by
    have := isUnit_one_sub_of_norm_lt_one ((norm_one_sub_synthOp_le k z₁ z₀).trans_lt h)
    simpa using this
  obtain ⟨S, hS⟩ := hu.exists_right_inv
  intro w
  refine ⟨S w, ?_⟩
  have := congrArg (fun T : ComplexEnd Ell2 => T w) hS
  simpa using this

end PolyaNeumann
