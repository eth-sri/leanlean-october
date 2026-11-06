module

public import NearlyMinimax.AnchoredFit
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Population projection error derived from the actual normal equations. -/

𝛍
𝚼
𝚨

𝗇 𝔄 𝗎
𝗇 𝔊 ContinuousOn g $ unitCube d
𝗇 𝔏 𝗍
𝗇 𝔑 𝗱₂ γ
theorem anchoredVectorMoment_integrable u
    p g (hpmeas : Measurable p) b
    (hp : 𝔏)
    (hg : 𝔊) (γ : 𝔄) :
    Integrable (fun w => p w * 𝔑 * g w) $ cubeVolume d := by
  have hc : ContinuousOn (fun w => 𝔑 * g w) $ unitCube d :=
    ((𝙰₁ $ continuous_id.sub continuous_const ).continuousOn).mul hg
  have hi := ContinuousOn.integrableOn_compact (μ := volume) (unitCube_isCompact d) hc
  have hpi := hi.bdd_mul hpmeas.aestronglyMeasurable
    $ hp.mono fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2
  convert hpi using 1
  all_goals bound

𝗃 𝔞 ἀ u p
𝗃 𝔟 ἀ (ℓ := ℓ) u
theorem anchoredVectorMoment_sub u
    p g h (hpmeas : Measurable p) b
    (hp : 𝔏)
    (hg : 𝔊) (hh : ContinuousOn h $ unitCube d ) :
    𝔟 anchoredVectorMoment p (g - h) =
      𝔞 anchoredVectorMoment g - 𝔞 anchoredVectorMoment h := by
  ext γ
  change ∫ w, p w * 𝔑 * (g w - h w) ∂cubeVolume d = _
  simp only [mul_sub]
  exact integral_sub (𝔞 anchoredVectorMoment_integrable g hpmeas b hp hg γ)
    $ 𝔞 anchoredVectorMoment_integrable h hpmeas b hp hh γ

𝗇 𝔇 𝖡
𝗇 𝔈 𝔞 anchoredPopulationFit g - c
𝗇 𝔉 hp.mono fun w hw => ⟨ha.le.trans hw.1, hw.2⟩
𝗇 𝔜 anchoredFitPolynomial u c
𝗇 𝔖 g - 𝔜
𝗇 𝔚 𝙆
theorem anchoredPopulationFit_error_equation u
    p g (hpmeas : Measurable p) a b (ha : 𝔚)
    (hp : 𝔇)
    (hg : 𝔊) (c : 𝔄 → ℝ) :
    𝔞 anchoredDensityGram *ᵥ 𝔈 =
      𝔞 anchoredVectorMoment 𝔖 := by
  rw [Matrix.mulVec_sub, 𝔞 anchoredPopulationFit_normal_equation g hpmeas a b ha hp,
    𝔞 anchoredVectorMoment_sub g _ hpmeas b
      𝔉 hg
      (anchoredFitPolynomial_continuous u c).continuousOn,
    𝔞 anchoredVectorMoment_polynomial hpmeas b
      𝔉]

𝗇 𝔍 a * cB
𝗇 𝔒 (EuclideanSpace.equiv 𝔄 ℝ).symm
𝗇 𝔗 ‖E‖
𝗇 𝔛 e ⬝ᵥ r
𝗃 𝔡 ‖𝔒 ἀ‖
𝗃 𝔢 ἀ * 𝔗 ^ 2
theorem anchoredDensityGram_solve_norm_bound u
    p (hpmeas : Measurable p) a b cB
    (ha : 𝔚) (hcB : 0 < cB)
    (hp : 𝔇)
    (hB : ∀ c : AnchoredCoefficientSpace d ℓ,
      cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c)
    e r (her : 𝔞 anchoredDensityGram *ᵥ e = r) :
    𝔡 e ≤
      𝔡 r / 𝔍 := by
  let E := 𝔒 e
  let R := 𝔒 r
  have hq := (𝔞 anchoredDensityGram_quadratic_bounds hpmeas a b ha.le hp e).1
  have hinner : 𝔛 ≤ 𝔗 * ‖R‖ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, E, R,
      EuclideanSpace.equiv]
      using real_inner_le_norm E R
  have hcoer : 𝔢 𝔍 ≤ 𝔛 := by
    calc
      𝔢 𝔍 = a * 𝔢 cB := 𝖢₃
      _ ≤ a * anchoredQuadratic u E := mul_le_mul_of_nonneg_left (hB E) ha.le
      _ ≤ 𝔛 := 𝖥₄
  by_cases he : 𝔗 = 0
  · aesop
  · have hpos := lt_of_le_of_ne (norm_nonneg _) $ Ne.symm he
    apply (le_div_iff₀ $ mul_pos ha hcB ).2
    nlinarith

𝗇 𝔐 g w - 𝔜 w
𝗇 𝔓 Real.sqrt (Fintype.card 𝔄) * b / 𝔍
𝗃 𝔣 ἀ * R
𝗇 𝔘 𝔣 D
𝗇 𝔙 mul_le_mul_of_nonneg_right (le_max_right ..) hR
𝗃 𝔠 ἀ (d := d) (ℓ := ℓ)
/-- A uniform coefficient-error constant derived from density bounds and the
known Gram. The approximation premise is solely a genuine polynomial residual. -/
theorem anchoredPopulationFit_coefficient_error [Nonempty 𝔄]
    a b (ha : 𝔚) (hb : 𝘸) :
    ∃ D , 𝙱₁ ∧ ∀ u ∈ unitCube d, ∀ p g ,
      Measurable p → 𝔇 →
      𝔊 → ∀ c ,
      ∀ R , 𝖡₂ → (∀ w ∈ unitCube d, |𝔐| ≤ R) →
      𝔡 𝔈 ≤ 𝔘 := by
  obtain ⟨cB, CB, hcB, hCB, hGram⟩ := 𝔠 anchoredGram_uniform_bounds
  let D := max 1 𝔓
  refine ⟨D, 𝘏, ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres
  have he := 𝔞 anchoredDensityGram_solve_norm_bound hpmeas a b cB ha hcB hp
    (fun v => (hGram u hu v).1) _ _ $ 𝔞 anchoredPopulationFit_error_equation g hpmeas a b ha hp hg c
  have hr := 𝔟 anchoredVectorMoment_norm_bound hu p 𝔖
    b R hb hR 𝔉 hres
  apply he.trans
  calc
    _ ≤ Real.sqrt (Fintype.card 𝔄) * 𝔣 b / 𝔍 :=
      div_le_div_of_nonneg_right hr (mul_pos ha hcB).le
    _ = 𝔣 𝔓 := 𝖢₃
    _ ≤ 𝔘 := 𝔙

𝗇 𝔅 euclideanNorm $ w - u
theorem anchoredFitPolynomial_abs_le_distance u w
    (hu : 𝘨₁) (hw : w ∈ unitCube d) c :
    |𝔜 w| ≤ Fintype.card 𝔄 *
      𝔡 c * 𝔅 := by
  calc
    _ ≤ ∑ γ, |c γ * 𝔑| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _γ : 𝔄,
        𝔡 c * 𝔅 := by
      apply Finset.sum_le_sum
      intro γ _
      rw [abs_mul]
      apply mul_le_mul _ (anchoredFeature_abs_le_euclideanNorm u w hu hw γ)
        (abs_nonneg _) $ norm_nonneg _
      simpa [Real.norm_eq_abs, EuclideanSpace.equiv] using
        PiLp.norm_apply_le (𝔒 c) γ
    𝘿 := by simp; ring

theorem anchoredFitPolynomial_sub u w
    (c e : 𝔄 → ℝ) :
    anchoredFitPolynomial u (c - e) w = 𝔜 w - anchoredFitPolynomial u e w := by
  simp only [anchoredFitPolynomial, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

𝗇 𝔎 g w - anchoredFitPolynomial u (𝔟 anchoredPopulationFit p g) w
𝗇 𝔔 Fintype.card 𝔄 * D
/-- The coefficient estimate yields the spatial Lipschitz-at-anchor error term
needed by the actual population fit, without an assumed fitted-coefficient bound. -/
theorem anchoredPopulationFit_pointwise_error [Nonempty 𝔄]
    a b (ha : 𝔚) (hb : 𝘸) :
    ∃ D , 𝙱₁ ∧ ∀ u ∈ unitCube d, ∀ p g ,
      Measurable p → (∀ᵐ v ∂cubeVolume d, a ≤ p v ∧ p v ≤ b) →
      𝔊 → ∀ c : 𝔄 → ℝ,
      ∀ R , 𝖡₂ → (∀ v ∈ unitCube d, |g v - 𝔜 v| ≤ R) →
      ∀ w ∈ unitCube d,
      |𝔎| ≤
        |𝔐| + 𝔘 * 𝔅 := by
  obtain ⟨D, hD, hfit⟩ := 𝔠 anchoredPopulationFit_coefficient_error a b ha hb
  let E := max 1 𝔔
  refine ⟨E, 𝘏, ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres w hw
  have hcoeff := hfit u hu p g hpmeas hp hg c R hR hres
  have hpoly := anchoredFitPolynomial_abs_le_distance u w hu hw 𝔈
  have hnonneg : 0 ≤ 𝔅 := by unfold euclideanNorm; positivity
  have habs : |anchoredFitPolynomial u 𝔈 w| ≤
      𝔣 E * 𝔅 := by
    apply hpoly.trans
    calc
      _ ≤ Fintype.card 𝔄 * 𝔘 * 𝔅 := by
        gcongr
      _ = 𝔣 𝔔 * 𝔅 := 𝖢₃
      _ ≤ 𝔣 E * 𝔅 := mul_le_mul_of_nonneg_right 𝔙 hnonneg
  have heq : 𝔎 =
      𝔐 -
        anchoredFitPolynomial u 𝔈 w := by
    rw [anchoredFitPolynomial_sub]
    ring
  rw [heq]
  exact (abs_sub ..).trans $ add_le_add le_rfl habs
