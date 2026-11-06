module

public import NearlyMinimax.AnchoredGramBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine whitening and spectral localization of the population anchored Gram. -/

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
𝚨

𝗇 𝔚 𝗎
𝗇 𝔄 Matrix 𝔚 𝔚 ℝ
𝗇 𝔈 CFC.sqrt $ anchoredGram u
/-- The inverse positive square root of the known Lebesgue Gram. -/
def anchoredWhitening (u : Covariate d) :
    𝔄 :=
  𝔈⁻¹

𝗃 𝔜 ἀ (ℓ := ℓ)
𝗃 𝔐 𝔜 ἀ u
𝗇 𝔉 𝔐 anchoredGram
𝗇 𝔎 (anchoredGram_posDef u).posSemidef.nonneg
theorem anchoredGram_sqrt_isUnit (u : Covariate d) :
    IsUnit $ CFC.sqrt 𝔉 :=
  (CFC.isUnit_sqrt_iff _ 𝔎).mpr
    (anchoredGram_posDef u).isUnit

𝗇 𝔍 𝔐 anchoredWhitening
theorem anchoredWhitening_isHermitian (u : Covariate d) :
    (𝔍).IsHermitian :=
  (Matrix.LE.le.posSemidef $ CFC.sqrt_nonneg $ anchoredGram u ).isHermitian.inv

𝗇 𝔇 (Matrix.isUnit_iff_isUnit_det _).mp 𝔐 anchoredGram_sqrt_isUnit
𝗇 𝔓 (CFC.sqrt_mul_sqrt_self (anchoredGram u) 𝔎).symm
𝗇 𝔖 𝔈 * 𝔈
theorem anchoredWhitening_gram_identity (u : Covariate d) :
    𝔍 * anchoredGram u * anchoredWhitening u = 1 := by
  have hdet := 𝔇
  calc
    _ = anchoredWhitening u *
        𝔖 * anchoredWhitening u :=
      congrArg (fun M => anchoredWhitening u * M * anchoredWhitening u)
        𝔓
    𝚘₂ := by
      unfold anchoredWhitening
      simp_all

/-- The symmetric whitened population matrix used in the inverse approximation. -/
def anchoredWhitenedGram (u : Covariate d) (p : 𝙀) :
    𝔄 :=
  anchoredWhitening u * anchoredDensityGram u p * anchoredWhitening u

𝗇 𝔏 𝔐 anchoredWhitenedGram p
𝗇 𝔔 (anchoredWhitening_isHermitian u).eq
theorem anchoredWhitenedGram_isHermitian (u : Covariate d)
    p : (𝔏).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul 𝔍
    $ anchoredDensityGram_isHermitian u p
  rw [𝔔] at h
  exact h

𝗇 𝔊 𝖡
𝗇 𝔗 anchoredWhitenedGram u p
/-- Whitening converts the proved density Gram sandwich into scalar-matrix bounds. -/
theorem anchoredWhitenedGram_sandwich u
    p (hpmeas : Measurable p) a b (ha : 𝖢₂)
    (hp : 𝔊) :
    a • (1 : 𝔄) ≤ 𝔗 ∧
      𝔗 ≤ b • (1 : 𝔄) := by
  have h := 𝔐 anchoredDensityGram_sandwich p hpmeas a b ha hp
  constructor
  · have hlo := h.1.conjTranspose_mul_mul_same $ anchoredWhitening u
    rw [𝔔] at hlo
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      anchoredWhitening_gram_identity] at hlo
    exact hlo
  · have hup := h.2.conjTranspose_mul_mul_same $ anchoredWhitening u
    rw [𝔔] at hup
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      anchoredWhitening_gram_identity] at hup
    exact hup

𝗇 𝔘 anchoredWhitenedGram_isHermitian u p
/-- The actual normalized population Gram has spectrum in the density interval. -/
theorem anchoredWhitenedGram_spectrum u
    p (hpmeas : Measurable p) a b (ha : 𝖢₂)
    (hp : 𝔊) :
    spectrum ℝ 𝔏 ⊆ Set.Icc a b := by
  have hs := 𝔐 anchoredWhitenedGram_sandwich p hpmeas a b ha hp
  have hup : 𝔗 ≤
      algebraMap ℝ 𝔄 b := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hs.2
  intro t ht
  exact ⟨(algebraMap_le_iff_le_spectrum 𝔘).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hs.1) t ht,
    (le_algebraMap_iff_spectrum_le 𝔘).mp hup t ht⟩

/-- A genuine matrix unit implementing the population similarity transform. -/
def anchoredSimilarityUnit (u : Covariate d) :
    𝔄 ˣ :=
  (𝔐 anchoredGram_sqrt_isUnit).unit⁻¹

𝗇 𝔅 𝔐 anchoredSimilarityUnit
𝗇 𝔙 (𝔅).val
@[simp] theorem anchoredSimilarityUnit_val (u : Covariate d) :
    𝔙 = anchoredWhitening u := by
  rw [anchoredSimilarityUnit, Matrix.coe_units_inv, IsUnit.unit_spec]
  rfl

𝗇 𝔒 (𝔅⁻¹).val
@[simp] theorem anchoredSimilarityUnit_inv_val (u : Covariate d) :
    𝔒 = 𝔈 := by
  rfl

theorem anchoredWhitening_square (u : Covariate d) :
    𝔉⁻¹ = anchoredWhitening u * anchoredWhitening u := by
  calc
    (anchoredGram u)⁻¹ = 𝔖⁻¹ :=
      congrArg Inv.inv 𝔓
    𝘿 := Matrix.mul_inv_rev ..

/-- The actual preconditioned Gram is similar to the Hermitian spectral matrix. -/
theorem anchored_preconditioned_similarity (u : Covariate d)
    p :
    𝔒 *
      ((anchoredGram u)⁻¹ * anchoredDensityGram u p) *
      𝔙 = 𝔗 := by
  have hsq := 𝔐 anchoredWhitening_square
  rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val, hsq]
  simp only [← Matrix.mul_assoc, anchoredWhitenedGram]
  rw [show 𝔈 * anchoredWhitening u = 1 by
    exact Matrix.mul_nonsing_inv _ 𝔇, one_mul]

𝗃 𝔑 ἀ (d := d) (ℓ := ℓ)
theorem anchoredGram_continuous :
    Continuous 𝔑 anchoredGram :=
  continuous_matrix anchoredGram_entry_continuous

theorem anchoredGram_sqrt_continuous :
    Continuous fun u : Covariate d => CFC.sqrt 𝔉 := CFC.continuousOn_sqrt.comp_continuous anchoredGram_continuous
     fun u => 𝔎

theorem anchoredWhitening_continuous :
    Continuous 𝔑 anchoredWhitening := by
  rw [continuous_iff_continuousAt]
  intro u
  have hdet := 𝔇
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt 𝔉).det := by
    simp_all
  have hR : Continuous fun v : Covariate d => CFC.sqrt $ 𝔜 anchoredGram v :=
    anchoredGram_sqrt_continuous
  have hI := continuousAt_matrix_inv _ hinv
  exact hI.comp
    (x := u) hR.continuousAt

/-- A fixed finite condition-number bound exists for every actual similarity
unit, uniformly over anchors. It depends only on the monomial dimensions. -/
theorem anchoredSimilarityUnit_uniform_condition :
    ∃ χ , 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖𝔙‖ *
        ‖𝔒‖ ≤ χ := by
  have hc :=
    (𝔜 anchoredWhitening_continuous).norm.mul
      (𝔑 anchoredGram_sqrt_continuous).norm
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.continuousOn
  refine ⟨max 1 M, 𝘶₂, ?_⟩
  intro u hu
  rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val]
  exact (hM $ Set.mem_image_of_mem _ hu ).trans $ le_max_right ..
