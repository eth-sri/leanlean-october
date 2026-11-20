module

public import NearlyMinimax.AnchoredFeatures


@[expose] public section

/-! Uniform compact bounds and density comparison for the concrete anchored Gram. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax

abbrev AnchoredCoefficientSpace (d ℓ : ℕ) := EuclideanSpace ℝ (AnchoredIndex d ℓ)

section
variable {d ℓ : ℕ}

def anchoredQuadratic (u : Covariate d) (c : AnchoredCoefficientSpace d ℓ) : ℝ :=
  c.ofLp ⬝ᵥ (anchoredGram u *ᵥ c.ofLp)

theorem anchoredGram_entry_continuous (γ δ : AnchoredIndex d ℓ) :
    Continuous (fun u => anchoredGram u γ δ) := continuous_parametric_integral_of_continuous
    (((anchoredMonomial_continuous γ).comp (continuous_snd.sub continuous_fst)).mul ((anchoredMonomial_continuous δ).comp (continuous_snd.sub continuous_fst)))
    (unitCube_isCompact d)

theorem anchoredQuadratic_continuous :
    Continuous (fun z : Covariate d × AnchoredCoefficientSpace d ℓ =>
      anchoredQuadratic z.1 z.2) := by
  apply continuous_finset_sum
  intro γ hγ
  apply Continuous.mul ((PiLp.continuous_apply 2 _ γ).comp continuous_snd)
  apply continuous_finset_sum
  intro δ hδ
  exact ((anchoredGram_entry_continuous γ δ).comp continuous_fst).mul
    ((PiLp.continuous_apply 2 _ δ).comp continuous_snd)

theorem anchoredQuadratic_pos (u : Covariate d)
    {c : AnchoredCoefficientSpace d ℓ} (hc : c ≠ 0) : 0 < anchoredQuadratic u c := by
  have h := (anchoredGram_posDef u).dotProduct_mulVec_pos (by
    solve_by_elim [PiLp.ext])
  positivity

theorem anchoredQuadratic_smul (u : Covariate d)
    (a : ℝ) (c : AnchoredCoefficientSpace d ℓ) :
    anchoredQuadratic u (a • c) = a ^ 2 * anchoredQuadratic u c := by
  change (∑ γ, (a * c γ) * ∑ δ, anchoredGram u γ δ * (a * c δ)) =
    a ^ 2 * ∑ γ, c γ * ∑ δ, anchoredGram u γ δ * c δ
  simp_rw [Finset.mul_sum]
  ring

/-- Compactness supplies uniform positive lower and finite upper bounds on
all anchor Grams. These constants are proved to exist from concrete monomials. -/
theorem anchoredGram_uniform_bounds [Nonempty (AnchoredIndex d ℓ)] :
    ∃ cB CB : ℝ, 0 < cB ∧ 0 < CB ∧
      ∀ u ∈ unitCube d, ∀ c : AnchoredCoefficientSpace d ℓ,
        cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c ∧
        anchoredQuadratic u c ≤ CB * ‖c‖ ^ 2 := by
  classical
  let S : Set (Covariate d × AnchoredCoefficientSpace d ℓ) :=
    unitCube d ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := (unitCube_isCompact d).prod (isCompact_sphere 0 1)
  have hSne : S.Nonempty := by
    refine ⟨(0, EuclideanSpace.single (Classical.choice inferInstance) 1), ?_, ?_⟩
    · intro i; simp
    · simp
  obtain ⟨zmin, hzmin, hmin⟩ := hS.exists_isMinOn hSne anchoredQuadratic_continuous.continuousOn
  obtain ⟨zmax, hzmax, hmax⟩ := hS.exists_isMaxOn hSne anchoredQuadratic_continuous.continuousOn
  refine ⟨anchoredQuadratic zmin.1 zmin.2, max 1 (anchoredQuadratic zmax.1 zmax.2),
    (anchoredQuadratic_pos _ (by
      intro he
      aesop)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu c
  by_cases hc : c = 0
  · subst c
    simp [anchoredQuadratic]
  have hn  := norm_pos_iff.mpr hc
  let c'  := ‖c‖⁻¹ • c
  have huc : (u, c') ∈ S := ⟨hu, by simpa using (by
    simp [c', norm_smul, Real.norm_eq_abs, abs_of_pos hn, hn.ne', inv_mul_cancel₀])⟩
  have hlo  := hmin huc
  have hup := (hmax huc).trans (le_max_right 1 _)
  have hrestore : ‖c‖ • c' = c := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [(Eq.trans (congrArg _ hrestore.symm) (anchoredQuadratic_smul u ‖c‖ c'))]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo (sq_nonneg ‖c‖)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hup (sq_nonneg ‖c‖)

end

variable {d ℓ : ℕ} (u : Covariate d) {p : Covariate d → ℝ} (hpmeas : Measurable p) {a b : ℝ} (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)

/-- The concrete index set is nonempty in the manuscript's sharp regime. -/
theorem anchoredIndex_nonempty (hd : 0 < d) (hℓ : 0 < ℓ) :
    Nonempty (AnchoredIndex d ℓ) := by
  classical
  let γ : PolynomialBox d ℓ := fun i => if i = (⟨0, hd⟩) then ⟨1, by omega⟩ else 0
  have hs : (∑ i, (γ i).val) = 1 := by
    simp only [γ, apply_ite]
    simp
  exact ⟨⟨γ, by exact_mod_cast (by omega)⟩⟩

/-- Density-weighted actual population Gram on the normalized cube. -/
def anchoredDensityGram (p : Covariate d → ℝ) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, p w * (anchoredFeature u w γ * anchoredFeature u w δ) ∂cubeVolume d

theorem anchoredDensityGram_isHermitian
    (p : Covariate d → ℝ) : (anchoredDensityGram (ℓ := ℓ) u p).IsHermitian := by
  ext γ δ
  simp [anchoredDensityGram]
  grind

include hpmeas in
theorem anchoredDensityGram_product_integrable
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => p w * (anchoredFeature u w γ * anchoredFeature u w δ))
      (cubeVolume d) := by
  apply (anchoredFeature_product_integrable u γ δ).bdd_mul hpmeas.aestronglyMeasurable
  exact hp.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)

include hpmeas in
theorem anchoredDensityGram_quadratic
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (c : AnchoredIndex d ℓ → ℝ) :
    c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) =
      ∫ w, p w * (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  classical
  have heq : (fun w => p w * (∑ γ, c γ * anchoredFeature u w γ) ^ 2) =
      (fun w => ∑ γ, ∑ δ, c γ *
        (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ) := by
    funext w
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro δ hδ
    ring
  rw [heq, integral_finset_sum]
  · change (∑ γ, c γ * ∑ δ, anchoredDensityGram u p γ δ * c δ) = _
    simp only [Finset.mul_sum, anchoredDensityGram]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [integral_finset_sum]
    · simp_rw [integral_mul_const, integral_const_mul]
      ring
    · intro δ hδ
      exact ((anchoredDensityGram_product_integrable u hpmeas hp γ δ).const_mul
        (c γ)).mul_const (c δ)
  · intro γ hγ
    exact integrable_finset_sum _ (fun δ hδ =>
      ((anchoredDensityGram_product_integrable u hpmeas hp γ δ).const_mul
        (c γ)).mul_const (c δ))

include hpmeas ha hp in
/-- Density bounds yield the exact quadratic-form comparison in Lemma U1(3). -/
theorem anchoredDensityGram_quadratic_bounds (c : AnchoredIndex d ℓ → ℝ) :
    a * (c ⬝ᵥ (anchoredGram u *ᵥ c)) ≤ c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) ∧
      c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) ≤ b * (c ⬝ᵥ (anchoredGram u *ᵥ c)) := by
  have hp0 : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b :=
    hp.mono (fun w hw => ⟨ha.trans hw.1, hw.2⟩)
  let f  := fun w => (∑ γ, c γ * anchoredFeature u w γ) ^ 2
  have hf : Continuous f := by
    apply Continuous.pow
    apply continuous_finset_sum
    intro γ hγ
    exact ((anchoredMonomial_continuous γ).comp
      (continuous_id.sub continuous_const)).const_mul (c γ)
  have hi : Integrable f (cubeVolume d) :=
    ContinuousOn.integrableOn_compact (unitCube_isCompact d) hf.continuousOn
  have hpi : Integrable (fun w => p w * f w) (cubeVolume d) := by
    apply hi.bdd_mul hpmeas.aestronglyMeasurable
    exact hp0.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)
  rw [anchoredGram_quadratic, anchoredDensityGram_quadratic u hpmeas hp0,
    ← integral_const_mul, ← integral_const_mul]
  constructor
  · exact integral_mono_ae (hi.const_mul a) hpi (hp.mono (fun w hw =>
      mul_le_mul_of_nonneg_right hw.1 (sq_nonneg _)))
  · exact integral_mono_ae hpi (hi.const_mul b) (hp.mono (fun w hw =>
      mul_le_mul_of_nonneg_right hw.2 (sq_nonneg _)))

include hpmeas in
/-- A positive density lower bound makes the actual population Gram invertible. -/
theorem anchoredDensityGram_posDef (ha : 0 < a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    (anchoredDensityGram (ℓ := ℓ) u p).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredDensityGram_isHermitian u p)
  intro c hc
  exact (mul_pos ha ((anchoredGram_posDef u).dotProduct_mulVec_pos hc)).trans_le
    (anchoredDensityGram_quadratic_bounds u hpmeas ha.le hp c).1

include hpmeas ha hp in
/-- The manuscript's two Loewner inequalities for the actual density Gram. -/
theorem anchoredDensityGram_sandwich :
    (anchoredDensityGram (ℓ := ℓ) u p - a • anchoredGram u).PosSemidef ∧
      (b • anchoredGram u - anchoredDensityGram (ℓ := ℓ) u p).PosSemidef := by
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((anchoredDensityGram_isHermitian u p).sub
        ((anchoredGram_isHermitian u).smul (by simp [IsSelfAdjoint])))
    intro c
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact sub_nonneg.mpr (anchoredDensityGram_quadratic_bounds u hpmeas ha hp c).1
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (((anchoredGram_isHermitian u).smul (by simp [IsSelfAdjoint])).sub
        (anchoredDensityGram_isHermitian u p))
    intro c
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact sub_nonneg.mpr (anchoredDensityGram_quadratic_bounds u hpmeas ha hp c).2

end NearlyMinimax
