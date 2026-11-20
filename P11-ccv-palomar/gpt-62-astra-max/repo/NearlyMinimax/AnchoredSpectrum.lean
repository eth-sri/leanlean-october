module

public import NearlyMinimax.AnchoredGramBounds


@[expose] public section

/-! Genuine whitening and spectral localization of the population anchored Gram. -/

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ)

/-- The inverse positive square root of the known Lebesgue Gram. -/
def anchoredWhitening :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (CFC.sqrt (anchoredGram u))⁻¹

theorem anchoredGram_sqrt_isUnit :
    IsUnit (CFC.sqrt (anchoredGram (ℓ := ℓ) u)) :=
  (CFC.isUnit_sqrt_iff _ (anchoredGram_posDef u).posSemidef.nonneg).mpr
    (anchoredGram_posDef u).isUnit

theorem anchoredWhitening_isHermitian :
    (anchoredWhitening (ℓ := ℓ) u).IsHermitian :=
  (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (anchoredGram u))).isHermitian.inv

theorem anchoredWhitening_gram_identity :
    anchoredWhitening (ℓ := ℓ) u * anchoredGram u * anchoredWhitening u = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  calc
    _ = _ :=
      congrArg (fun M => anchoredWhitening u * M * anchoredWhitening u)
        (CFC.sqrt_mul_sqrt_self (anchoredGram u) (anchoredGram_posDef u).posSemidef.nonneg).symm
    _ = 1 := by
      simp_all [anchoredWhitening]

/-- The symmetric whitened population matrix used in the inverse approximation. -/
def anchoredWhitenedGram :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  anchoredWhitening u * anchoredDensityGram u p * anchoredWhitening u

theorem anchoredWhitenedGram_isHermitian : (anchoredWhitenedGram (ℓ := ℓ) u p).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul (anchoredWhitening (ℓ := ℓ) u)
    (anchoredDensityGram_isHermitian u p)
  rw [(anchoredWhitening_isHermitian u).eq] at h
  exact h

/-- Whitening converts the proved density Gram sandwich into scalar-matrix bounds. -/
theorem anchoredWhitenedGram_sandwich
    {p : Covariate d → ℝ} (hpmeas : Measurable p) {a b : ℝ} (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    a • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) ≤ anchoredWhitenedGram u p ∧
      anchoredWhitenedGram u p ≤ b • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) := by
  have h := anchoredDensityGram_sandwich (ℓ := ℓ) u hpmeas ha hp
  constructor
  · have hlo := h.1.conjTranspose_mul_mul_same (anchoredWhitening u)
    rw [(anchoredWhitening_isHermitian u).eq] at hlo
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      anchoredWhitening_gram_identity] at hlo
    exact hlo
  · have hup := h.2.conjTranspose_mul_mul_same (anchoredWhitening u)
    rw [(anchoredWhitening_isHermitian u).eq] at hup
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      anchoredWhitening_gram_identity] at hup
    exact hup

/-- The actual normalized population Gram has spectrum in the density interval. -/
theorem anchoredWhitenedGram_spectrum (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    spectrum ℝ (anchoredWhitenedGram (ℓ := ℓ) u p) ⊆ Set.Icc a b := by
  have hs := anchoredWhitenedGram_sandwich (ℓ := ℓ) u hpmeas ha hp
  intro t ht
  exact ⟨(algebraMap_le_iff_le_spectrum (anchoredWhitenedGram_isHermitian u p)).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hs.1) t ht,
    (le_algebraMap_iff_spectrum_le (anchoredWhitenedGram_isHermitian u p)).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hs.2) t ht⟩

/-- A genuine matrix unit implementing the population similarity transform. -/
def anchoredSimilarityUnit :
    (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ)ˣ :=
  (anchoredGram_sqrt_isUnit u).unit⁻¹

@[simp] theorem anchoredSimilarityUnit_val :
    (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitening u := by
  rw [anchoredSimilarityUnit, Matrix.coe_units_inv]
  rfl

@[simp] theorem anchoredSimilarityUnit_inv_val :
    ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val = CFC.sqrt (anchoredGram u) := rfl

theorem anchoredWhitening_square :
    (anchoredGram (ℓ := ℓ) u)⁻¹ = anchoredWhitening u * anchoredWhitening u := Eq.trans (congrArg Inv.inv (CFC.sqrt_mul_sqrt_self (anchoredGram u) (anchoredGram_posDef u).posSemidef.nonneg).symm) (Matrix.mul_inv_rev _ _)

/-- The actual preconditioned Gram is similar to the Hermitian spectral matrix. -/
theorem anchored_preconditioned_similarity :
    ((anchoredSimilarityUnit u)⁻¹).val *
      ((anchoredGram u)⁻¹ * anchoredDensityGram u p) *
      (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitenedGram u p := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  rw [ anchoredSimilarityUnit_inv_val, (anchoredWhitening_square (ℓ := ℓ) u)]
  simp only [← Matrix.mul_assoc, anchoredWhitenedGram]
  simp_all [anchoredGram, anchoredWhitening]

end

variable {d ℓ : ℕ}

theorem anchoredGram_continuous :
    Continuous (anchoredGram (d := d) (ℓ := ℓ)) :=
  continuous_matrix anchoredGram_entry_continuous

theorem anchoredGram_sqrt_continuous :
    Continuous (fun u : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) u)) := CFC.continuousOn_sqrt.comp_continuous anchoredGram_continuous
    (fun u => (anchoredGram_posDef u).posSemidef.nonneg)

theorem anchoredWhitening_continuous :
    Continuous (anchoredWhitening (d := d) (ℓ := ℓ)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt (anchoredGram (ℓ := ℓ) u)).det := by
    simp_all
  exact (continuousAt_matrix_inv _ hinv).comp
    (x := u) (anchoredGram_sqrt_continuous.continuousAt)

/-- A fixed finite condition-number bound exists for every actual similarity
unit, uniformly over anchors. It depends only on the monomial dimensions. -/
theorem anchoredSimilarityUnit_uniform_condition :
    ∃ χ : ℝ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredSimilarityUnit (ℓ := ℓ) u).val‖ *
        ‖((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
  have hc  :=
    (anchoredWhitening_continuous (ℓ := ℓ)).norm.mul
      (anchoredGram_sqrt_continuous (d := d) (ℓ := ℓ)).norm
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  rw [anchoredSimilarityUnit_val]
  exact (hM (Set.mem_image_of_mem _ hu)).trans (le_max_right _ _)

end NearlyMinimax
