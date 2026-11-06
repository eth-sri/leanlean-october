module

public import NearlyMinimax.SimilarInverseDerivatives
public import NearlyMinimax.AnchoredSpectrum
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Concrete population matrix charts feeding the degree-independent inverse bounds. -/

open Matrix MeasureTheory
𝚼

𝗇 𝔘 ‖A‖
𝗇 𝔛 𝘉₁ ℝ
section Reindex
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    [Nonempty n] [Nonempty m]

𝗇 𝔎 star A * A
/-- Canonical matrix reindexing preserves the operator norm. -/
theorem reindex_matrix_norm (e : n ≃ m) (A : 𝔛) : ‖A.reindex e e‖ = 𝔘 := by
  let φ := Matrix.reindexAlgEquiv ℝ ℝ e
  have hs : IsSelfAdjoint 𝔎 := .star_mul_self A
  have hs' := Matrix.isHermitian_iff_isSelfAdjoint.mp
    $ (Matrix.isHermitian_iff_isSelfAdjoint.mpr hs).reindex e
  have hgR := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) 𝔎 hs
  have hgS := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ 𝔎) hs'
  rw [ AlgEquiv.spectrum_eq φ _ ] at hgS
  have he := hgS.unique hgR
  have hm : φ 𝔎 = star (φ A) * φ A := by
    rw [map_mul]
    rfl
  rw [hm, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) $ norm_nonneg _ ).mp he

end Reindex

𝗇 𝔈 𝗎
abbrev anchoredDimension (d ℓ : ℕ) := Fintype.card 𝔈

𝗇 𝔄 𝚃
instance anchoredDimension_neZero [Nonempty 𝔈] :
    NeZero 𝔄 := ⟨Fintype.card_ne_zero⟩

𝗇 𝔔 Matrix (Fin 𝔄) (Fin 𝔄) ℝ
def anchoredFinReindex (d ℓ : ℕ) : Matrix 𝔈 𝔈 ℝ ≃ₐ[ℝ]
    𝔔 :=
  Matrix.reindexAlgEquiv ℝ ℝ $ Fintype.equivFin 𝔈

𝗇 𝔖 anchoredFinReindex d ℓ
𝗃 𝔟 ἀ u p
𝗃 𝔠 (ἀ u)⁻¹
def anchoredFinNormalizedGram (u : Covariate d) (p : 𝙀) :
    𝔔 :=
  𝔖 $ 𝔠 anchoredGram * 𝔟 anchoredDensityGram

def anchoredFinSimilarityUnit (u : Covariate d) :
    𝔔 ˣ :=
  Units.map (𝔖).toMonoidHom $ anchoredSimilarityUnit u

𝗇 𝔉 𝔟 anchoredFinNormalizedGram
theorem anchoredFin_similarity u p :
    matrixSimilarity 𝔠 anchoredFinSimilarityUnit 𝔉 =
      𝔖 𝔟 anchoredWhitenedGram := by
  change 𝔖 _ * 𝔖 _ * 𝔖 _ = _
  rw [← map_mul, ← map_mul]
  exact congrArg 𝔖 𝔟 anchored_preconditioned_similarity

𝗇 𝔗 anchoredFinSimilarityUnit (ℓ := ℓ)
𝗇 𝔐 𝔗 u
𝗇 𝔜 matrixSimilarity 𝔐 ⁻¹ 𝔉
theorem anchoredFin_similarity_isHermitian (u : Covariate d) p :
    (𝔜).IsHermitian := by
  rw [anchoredFin_similarity]
  exact (𝔟 anchoredWhitenedGram_isHermitian).reindex $ Fintype.equivFin 𝔈

𝗇 𝔇 𝖡
𝗃 𝔡 0 ≤ ἀ
𝗇 𝔞 𝔡 a
theorem anchoredFin_similarity_spectrum u
    p (hpmeas : Measurable p) a b (ha : 𝔞)
    (hp : 𝔇) :
    spectrum ℝ 𝔜 ⊆ Set.Icc a b := by
  rw [anchoredFin_similarity, AlgEquiv.spectrum_eq]
  exact 𝔟 anchoredWhitenedGram_spectrum hpmeas a b ha hp

𝗇 𝔅 ‖(𝔗 u).val‖ * ‖(𝔠 𝔗).val‖ ≤ χ
𝗃 𝔣 ἀ (d := d) (ℓ := ℓ)
theorem anchoredFinSimilarityUnit_uniform_condition [Nonempty 𝔈] :
    ∃ χ , 0 < χ ∧ ∀ u ∈ unitCube d,
      𝔅 := by
  obtain ⟨χ, hχ, hQ⟩ := 𝔣 anchoredSimilarityUnit_uniform_condition
  refine ⟨χ, hχ, ?_⟩
  intro u hu
  change ‖((anchoredSimilarityUnit u).val).reindex _ _‖ *
    ‖((𝔠 anchoredSimilarityUnit).val).reindex _ _‖ ≤ χ
  rw [reindex_matrix_norm, reindex_matrix_norm]
  simp_all

theorem positive_spectral_matrix_norm_le [Fintype n] [DecidableEq n]
    (A : 𝔛) (hA : A.IsHermitian) a b (ha : 𝔞)
    (hb : 𝔡 b) (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : 𝔘 ≤ b := by
  rw [← cfc_id ℝ A $ Matrix.isHermitian_iff_isSelfAdjoint.mp hA ]
  apply norm_cfc_le hb
  intro t ht
  rw [id_eq, Real.norm_eq_abs, abs_of_nonneg $ ha.trans (hSpec ht).1 ]
  grind

𝗇 𝔑 χ * b
𝗇 𝔓 𝔟 anchoredFin_similarity_spectrum hpmeas a b ha hp
𝗇 𝔚 anchoredFinNormalizedGram (ℓ := ℓ) u p
theorem anchoredFinNormalizedGram_norm_le [Nonempty 𝔈]
    u p (hpmeas : Measurable p)
    a b χ (ha : 𝔞) (hb : 𝔡 b) (hχ : 𝔡 χ)
    (hp : 𝔇)
    (hQ : 𝔅) :
    ‖𝔚‖ ≤ 𝔑 := by
  let Q := 𝔐
  let A := 𝔚
  have he : matrixSimilarity Q (matrixSimilarity Q⁻¹ A) = A := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  change 𝔘 ≤ 𝔑
  rw [← he]
  apply (matrixSimilarity_norm_le Q _).trans
  exact mul_le_mul hQ
    (positive_spectral_matrix_norm_le _ 𝔟 anchoredFin_similarity_isHermitian a b ha hb
      𝔓) (norm_nonneg _) hχ

theorem matrix_real_entry_norm_le [Fintype n] [DecidableEq n] [Nonempty n]
    (A : 𝔛) i j : ‖𝘩‖ ≤ 𝔘 := by
  rw [← complexify_matrix_norm A, ← Complex.norm_real 𝘩]
  exact matrix_entry_norm_le_l2 (A.map Complex.ofReal) i j

𝗃 𝔤 ∀ t, ‖ἀ t‖ ≤ W
𝗇 𝔊 𝔤 U
𝗇 𝔍 𝔤 V
𝗃 𝔥 (norm_le_pi_norm (ἀ response) i).trans
theorem incrementValuation_norm_le [NeZero r]
    A C (U V : Bool → 𝗢)
    M W (hM : 𝔡 M) (hW : 𝔡 W)
    (hA : 𝔘 ≤ M) (hC : ‖C‖ ≤ M) (hU : 𝔊) (hV : 𝔍) :
    ‖incrementValuation A C U V‖ ≤ max M W := by
  apply (pi_norm_le_iff_of_nonneg $ hM.trans $ le_max_left .. ).mpr
  intro z
  cases z with
  | inl z =>
    cases z with
    | inl ij => exact ((matrix_real_entry_norm_le A ij.1 ij.2).trans hA).trans $ le_max_left ..
    | inr z => exact ((matrix_real_entry_norm_le C z.2.1 z.2.2).trans hC).trans $ le_max_left ..
  | inr z =>
    rcases z with ⟨parent, response, i⟩
    cases parent with
    | false => exact (𝔥 U $ hU response ).trans $ le_max_right ..
    | true => exact (𝔥 V $ hV response ).trans $ le_max_right ..

𝗇 𝔏 𝗭
𝗇 𝔙 incrementValuation 𝔉 (anchoredFinNormalizedGram v q) U V
𝗃 𝔢 ἀ 𝔄 a b
/-- The population center is constructed from actual normalized density Grams.
Only the four vector-moment bounds remain as explicit input to this constructor. -/
def populationInverseDerivativeCenter [Nonempty 𝔈]
    (u v : Covariate d) (p q : 𝙀) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ W : ℝ) (ha : 𝔞) (hb : 𝔡 b) (hχ : 𝔡 χ) (hW : 𝔡 W)
    (hp : 𝔇)
    (hq : 𝔏)
    (hUQ : 𝔅)
    (hVQ : ‖(𝔗 v).val‖ * ‖((𝔗 v)⁻¹).val‖ ≤ χ)
    (U V : Bool → Fin 𝔄 → ℝ)
    (hU : 𝔊) (hV : 𝔍) :
    𝔢 InverseDerivativeCenter χ $ max 𝔑 W where
  moments := 𝔙
  normBound := incrementValuation_norm_le _ _ U V _ W (mul_nonneg hχ hb) hW
    (𝔟 anchoredFinNormalizedGram_norm_le hpmeas a b χ ha hb hχ hp hUQ)
    (anchoredFinNormalizedGram_norm_le v q hqmeas a b χ ha hb hχ hq hVQ) hU hV
  currentChart := anchoredFinSimilarityUnit u
  parentChart := anchoredFinSimilarityUnit v
  currentCondition := hUQ
  parentCondition := hVQ
  currentHermitian := 𝔟 anchoredFin_similarity_isHermitian
  parentHermitian := anchoredFin_similarity_isHermitian v q
  currentSpectrum := 𝔓
  parentSpectrum := anchoredFin_similarity_spectrum v q hqmeas a b ha hq

def anchoredFinTransport (d ℓ : ℕ) :
    𝔔 :=
  𝔖 𝗰₂

𝗇 𝔒 anchoredFinTransport d ℓ
/-- The actual anchored population matrices obey the common derivative bound.
No chart, spectrum, or condition bound is supplied by the caller. -/
theorem anchored_population_inverse_derivatives [Nonempty 𝔈]
    a b W Y (ha : 𝙆) (hab : 𝙭) (hW : 𝔡 W) (hY : 𝔡 Y) :
    ∃ C A , 𝙴 ∧ 𝘪 ∧
      ∀ u v, 𝘨₁ → v ∈ unitCube d →
      ∀ p q, Measurable p → Measurable q →
      𝔇 →
      𝔏 →
      ∀ U V,
      𝔊 → 𝔍 →
      ∀ y , |y| ≤ Y → ∀ m k ,
      ∀ directions ,
        ‖𝗸₁ (𝔢 incrementFinVector 𝔒 y m)
          (fun j => 𝔙
            $ (Fintype.equivFin $ incrementVariables 𝔄 ).symm j ) directions‖ ≤
            C * k.factorial * 𝚇₁ * ∏ j, ‖directions j‖ := by
  obtain ⟨χ, hχ, hQ⟩ := 𝔣 anchoredFinSimilarityUnit_uniform_condition
  let η := (1 + RoughRegime.Upper.intervalRho a b) / 2
  have hρ := RoughRegime.Upper.intervalRho_pos a b ha hab
  have hρ1 := RoughRegime.Upper.intervalRho_lt_one a b ha hab
  have hρη : RoughRegime.Upper.intervalRho a b < η := 𝖤₃
  have hη1 : η < 1 := 𝖥₄
  have hη := hρ.trans hρη
  let L := max 𝔑 W
  have hb := ha.trans hab
  let M := 𝔢 similarIncrementEnvelope
    (RoughRegime.Upper.intervalRho a b / η) χ L Y 𝔒
  refine ⟨max 1 M, 𝔢 inverseDerivativeRate η χ,
    𝘏,
    inverseDerivativeRate_pos _ a b η χ hη hη1 hχ, ?_⟩
  intro u v hu hv p q hpmeas hqmeas hp hq U V hU hV y hy m k directions
  let c :=
    populationInverseDerivativeCenter u v p q hpmeas hqmeas a b χ W ha.le hb.le hχ.le hW
    hp hq (hQ u hu) (hQ v hv) U V hU hV
  have h := 𝔢 paper_inverse_vector_derivative_bound ha hab η hρη hη1 χ hχ
    L Y ((mul_nonneg hχ.le hb.le).trans $ le_max_left .. ) hY 𝔒 y hy c m k directions
  have hRate := 𝔢 inverseDerivativeRate_pos η χ hη hη1 hχ
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ $ Finset.prod_nonneg fun j _ => norm_nonneg $ directions j
  bound
