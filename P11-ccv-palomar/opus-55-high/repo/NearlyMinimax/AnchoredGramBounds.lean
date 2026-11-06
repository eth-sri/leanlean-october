module

public import NearlyMinimax.AnchoredFeatures
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Uniform compact bounds and density comparison for the concrete anchored Gram. -/

open MeasureTheory Set Matrix MvPolynomial
𝚮
𝚨

𝗇 𝔇 𝗎
abbrev AnchoredCoefficientSpace (d ℓ : ℕ) := EuclideanSpace ℝ 𝔇

𝗇 𝔑 AnchoredCoefficientSpace d ℓ
𝗃 𝔚 anchoredGram u *ᵥ ἀ
def anchoredQuadratic (u : Covariate d) (c : 𝔑) : ℝ :=
  c.ofLp ⬝ᵥ 𝔚 c.ofLp

𝗇 𝔖 anchoredGram u γ δ
theorem anchoredGram_entry_continuous (γ δ : 𝔇) :
    Continuous fun u => 𝔖 := continuous_parametric_integral_of_continuous
    ((anchoredFeature_continuous γ).mul $ anchoredFeature_continuous δ )
    $ unitCube_isCompact d

𝗃 𝔙 (PiLp.continuous_apply 2 _ ἀ).comp continuous_snd
theorem anchoredQuadratic_continuous :
    Continuous fun z : Covariate d × 𝔑 =>
      anchoredQuadratic z.1 z.2 := by
  apply continuous_finset_sum
  intro γ hγ
  apply Continuous.mul 𝔙 γ
  apply continuous_finset_sum
  intro δ hδ
  exact ((anchoredGram_entry_continuous γ δ).comp continuous_fst).mul
    𝔙 δ

𝗇 𝔒 anchoredQuadratic u c
theorem anchoredQuadratic_pos u
    (c : 𝔑) (hc : c ≠ 0) : 0 < 𝔒 := by
  have hcf : c.ofLp ≠ 0 := by
    simpa
  have h := (anchoredGram_posDef u).dotProduct_mulVec_pos hcf
  assumption

theorem anchoredQuadratic_smul u
    a (c : 𝔑) :
    anchoredQuadratic u (a • c) = 𝗅 * 𝔒 := by
  change ∑ γ, a * c γ * ∑ δ, 𝔖 * (a * c δ) =
    𝗅 * ∑ γ, c γ * ∑ δ, 𝔖 * c δ
  simp_rw [Finset.mul_sum]
  ring

𝗇 𝔐 ‖c‖
𝗇 𝔗 𝔐 ^ 2
/-- Compactness supplies uniform positive lower and finite upper bounds on
all anchor Grams. These constants are proved to exist from concrete monomials. -/
theorem anchoredGram_uniform_bounds [Nonempty 𝔇] :
    ∃ cB CB , 0 < cB ∧ 0 < CB ∧
      ∀ u ∈ unitCube d, ∀ c : 𝔑,
        cB * 𝔗 ≤ 𝔒 ∧
        𝔒 ≤ CB * 𝔗 := by
  classical
  let S : Set $ Covariate d × 𝔑 :=
    unitCube d ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := (unitCube_isCompact d).prod $ isCompact_sphere 0 1
  let γ : 𝔇 := Classical.choice inferInstance
  have hSne : S.Nonempty := by
    refine ⟨(0, EuclideanSpace.single γ 1), ?_, ?_⟩
    · intro i; simp
    · simp
  obtain ⟨zmin, hzmin, hmin⟩ := hS.exists_isMinOn hSne anchoredQuadratic_continuous.continuousOn
  obtain ⟨zmax, hzmax, hmax⟩ := hS.exists_isMaxOn hSne anchoredQuadratic_continuous.continuousOn
  have hzminne : zmin.2 ≠ 0 := by
    aesop
  refine ⟨anchoredQuadratic zmin.1 zmin.2, max 1 $ anchoredQuadratic zmax.1 zmax.2 ,
     anchoredQuadratic_pos _ _ hzminne , 𝘶₂, ?_⟩
  intro u hu c
  by_cases hc : c = 0
  · subst c
    simp [anchoredQuadratic]
  have hn := norm_pos_iff.mpr hc
  let c' := 𝔐⁻¹ • c
  have hnorm : ‖c'‖ = 1 := by
    simp [c', norm_smul, hn.ne']
  have huc : (u, c') ∈ S := ⟨hu, 𝖧₄⟩
  have hup0 := hmax huc
  have hup := hup0.trans $ le_max_right 1 _
  have hrestore : 𝔐 • c' = c := by
    aesop
  have hscale : 𝔒 = 𝔗 * anchoredQuadratic u c' := by
    calc
      𝔒 = anchoredQuadratic u (𝔐 • c') := congrArg _ hrestore.symm
      _ = 𝔗 * anchoredQuadratic u c' := anchoredQuadratic_smul u 𝔐 c'
  rw [hscale]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hmin huc) $ sq_nonneg 𝔐
  · nlinarith

/-- The concrete index set is nonempty in the manuscript's sharp regime. -/
theorem anchoredIndex_nonempty (hd : 𝗆) (hℓ : 𝙲₁) :
    Nonempty 𝔇 := by
  classical
  let i0 : Fin d := ⟨0, hd⟩
  let γ : 𝗫₂ := fun i => if i = i0 then ⟨1, 𝖡₃⟩ else 0
  have hs : ∑ i, 𝘇 = 1 := by
    simp only [γ, apply_ite]
    simp
  exact ⟨⟨γ, 𝖡₃⟩⟩

𝗇 𝔈 p w * (𝗱₂ γ * 𝗱₂ δ)
/-- Density-weighted actual population Gram on the normalized cube. -/
def anchoredDensityGram (u : Covariate d) (p : 𝙀) :
    Matrix 𝔇 𝔇 ℝ :=
  fun γ δ => ∫ w, 𝔈 ∂cubeVolume d

𝗇 𝔍 anchoredDensityGram (ℓ := ℓ) u p
theorem anchoredDensityGram_isHermitian (u : Covariate d)
    p : (𝔍).IsHermitian := by
  ext γ δ
  simp only [conjTranspose_apply, star_trivial, anchoredDensityGram]
  grind

𝗇 𝔄 𝗍
theorem anchoredDensityGram_product_integrable u
    p (hpmeas : Measurable p) b
    (hp : 𝔄) (γ δ : 𝔇) :
    Integrable (fun w => 𝔈)
      $ cubeVolume d := by
  apply (anchoredFeature_product_integrable u γ δ).bdd_mul hpmeas.aestronglyMeasurable
  exact hp.mono fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2

𝗇 𝔉 (∑ γ, c γ * 𝗱₂ γ) ^ 2
𝗇 𝔎 ((anchoredDensityGram_product_integrable u p hpmeas b hp γ δ).const_mul $ c γ ).mul_const $ c δ
𝗇 𝔏 c ⬝ᵥ anchoredDensityGram u p *ᵥ c
theorem anchoredDensityGram_quadratic u
    p (hpmeas : Measurable p) b
    (hp : 𝔄) (c : 𝔇 → ℝ) :
    𝔏 =
      ∫ w, p w * 𝔉 ∂cubeVolume d := by
  classical
  have heq : (fun w => p w * 𝔉) =
       fun w => ∑ γ, ∑ δ, c γ *
        𝔈 * c δ := by
    funext w
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mul_sum, Finset.mul_sum]
    grind
  rw [heq, integral_finset_sum]
  · change ∑ γ, c γ * ∑ δ, anchoredDensityGram u p γ δ * c δ = _
    simp only [Finset.mul_sum, anchoredDensityGram]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [integral_finset_sum]
    · simp_rw [integral_mul_const, integral_const_mul]
      ring
    · intro δ hδ
      exact 𝔎
  · intro γ hγ
    exact integrable_finset_sum _ fun δ hδ =>
      𝔎

𝗇 𝔅 𝖡
𝗇 𝔊 c ⬝ᵥ 𝔚 c
𝗃 𝔘 hp.mono fun w hw => mul_le_mul_of_nonneg_right ἀ $ sq_nonneg _
/-- Density bounds yield the exact quadratic-form comparison in Lemma U1(3). -/
theorem anchoredDensityGram_quadratic_bounds u
    p (hpmeas : Measurable p) a b (ha : 𝖢₂)
    (hp : 𝔅) (c : 𝔇 → ℝ) :
    a * 𝔊 ≤ 𝔏 ∧
      𝔏 ≤ b * 𝔊 := by
  have hp0 : 𝔄 :=
    hp.mono fun w hw => ⟨ha.trans hw.1, hw.2⟩
  let f := fun w => 𝔉
  have hf : Continuous f := by
    apply Continuous.pow
    apply continuous_finset_sum
    intro γ hγ
    exact (𝙰₁
      $ continuous_id.sub continuous_const ).const_mul $ c γ
  have hi : Integrable f $ cubeVolume d :=
    ContinuousOn.integrableOn_compact (unitCube_isCompact d) hf.continuousOn
  have hpi : Integrable (fun w => p w * f w) $ cubeVolume d := by
    apply hi.bdd_mul hpmeas.aestronglyMeasurable
    exact hp0.mono fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2
  rw [anchoredGram_quadratic, anchoredDensityGram_quadratic u p hpmeas b hp0,
    ← integral_const_mul, ← integral_const_mul]
  constructor
  · exact integral_mono_ae (hi.const_mul a) hpi 𝔘 hw.1
  · exact integral_mono_ae hpi (hi.const_mul b) 𝔘 hw.2

𝗇 𝔓 anchoredDensityGram_quadratic_bounds u p hpmeas a b
𝗇 𝔔 anchoredDensityGram_isHermitian u p
/-- A positive density lower bound makes the actual population Gram invertible. -/
theorem anchoredDensityGram_posDef u
    p (hpmeas : Measurable p) a b (ha : 𝙆)
    (hp : 𝔅) :
    (𝔍).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos 𝔔
  intro c hc
  have hB : 0 < 𝔊 := by
    simpa only [star_trivial] using (anchoredGram_posDef u).dotProduct_mulVec_pos hc
  exact (mul_pos ha hB).trans_le
    (𝔓 ha.le hp c).1

/-- The manuscript's two Loewner inequalities for the actual density Gram. -/
theorem anchoredDensityGram_sandwich u
    p (hpmeas : Measurable p) a b (ha : 𝖢₂)
    (hp : 𝔅) :
    (𝔍 - a • anchoredGram u).PosSemidef ∧
      (b • anchoredGram u - 𝔍).PosSemidef := by
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      $ (𝔔).sub
        $ (anchoredGram_isHermitian u).smul 𝖦₄
    intro c
    simp only [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
    exact sub_nonneg.mpr (𝔓 ha hp c).1
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      $ ((anchoredGram_isHermitian u).smul 𝖦₄ ).sub
        𝔔
    intro c
    simp only [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
    exact sub_nonneg.mpr (𝔓 ha hp c).2
