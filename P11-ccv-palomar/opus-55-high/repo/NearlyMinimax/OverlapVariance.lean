module

public import NearlyMinimax.DesignCounts
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! # Disjoint-support orthogonality and overlap variance

Product response measures give independence of disjoint coordinate patches.
A graph with bounded closed degree converts this orthogonality into an
energy bound for the sum of the patch scores.
-/

𝚨

𝚵

noncomputable section

𝚬

𝗇 𝔙 𝘩
𝗃 𝔛 if 𝔙 then e ἀ else 0
𝗇 𝔥 𝙖
𝗇 𝔅 𝔥 * 𝔛 i + 𝔥 * 𝔛 j
𝗇 𝔇 ∑ i, ∑ j, 𝔛 i
𝗇 𝔊 ∑ i, ∑ j, 𝔛 j
𝗇 𝔏 𝔥
𝗇 𝔒 ∀ i, (Finset.univ.filter $ A i ).card ≤ D
𝗇 𝔓 D * ∑ i, e i
𝗇 𝔖 ∀ i j, 𝔙 ↔ A j i
𝗇 𝔢 c i j
𝗃 𝔨 ∑ i, ∑ j, ἀ
𝗃 𝔪 ∀ i j, ¬𝔙 → ἀ = 0
private theorem overlap_matrix_sum_bound [Fintype ι] (A : ι → ι → Prop)
    (hsym : 𝔖) (D : ℕ) (e : 𝙛) (c : ι → 𝙛)
    (he : ∀ i, 0 ≤ e i) (hdegree : 𝔒)
    (hzero : 𝔪 𝔢)
    (hpair : ∀ i j, 𝔢 ≤ (𝔏 : ℝ) * (e i + e j)) :
    𝔨 𝔢 ≤ 𝔓 := by
  have hpoint i j : 𝔢 ≤
      𝔅 := by
    by_cases h : 𝔙
    · simp only [if_pos h]
      nlinarith [hpair i j]
    · simp [h, hzero i j h]
  have htranspose : 𝔊 =
      𝔇 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hrow : 𝔇 ≤ 𝔓 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_filter]
    simp
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree i) $ he i
  calc
    _ ≤ 𝔨 𝔅 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ => hpoint i j
    _ = 𝔏 * 𝔇 +
        𝔏 * 𝔊 := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 𝔓 := 𝖡₄

𝗇 𝔦 r i x
𝗇 𝔄 ∫ x, 𝔦 * r j x ∂μ
𝗃 𝔫 ∫ x, ἀ ^ 2 ∂μ
𝗇 𝔉 𝔫 𝔦
𝗇 𝔔 r j x
𝗇 𝔗 𝔦
𝗇 𝔞 integral_finset_sum _ fun _ _ => Integrable.of_finite
/-- Bounded-degree covariance aggregation for actual finite-measure expectations. -/
theorem finite_overlap_variance_bound [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : ι → 𝘄) (A : ι → ι → Prop) D
    (hsym : 𝔖) (hdegree : 𝔒)
    (hzero : 𝔪 𝔄) :
     ∫ x, (∑ i, 𝔗) ^ 2 ∂μ ≤ D * ∑ i, 𝔉 := by
  have hpair i j : 𝔄 ≤
      𝔏 * (𝔉 + 𝔫 𝔔) := by
    have h := integral_mono (μ := μ) (f := fun x => 𝔗 * 𝔔)
      (g := fun x => 𝔏 * (𝔗 ^ 2 + 𝔔 ^ 2))
      Integrable.of_finite Integrable.of_finite fun x => by nlinarith [sq_nonneg $ 𝔗 - 𝔔 ]
    rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite] at h
    exact h
  calc
    _ = ∫ x, ∑ i, ∑ j, 𝔗 * 𝔔 ∂μ := by
      congr 1
      funext x
      rw [pow_two, Fintype.sum_mul_sum]
    _ = 𝔨 𝔄 := by
      rw [𝔞]
      apply Finset.sum_congr rfl
      intro i _
      rw [𝔞]
    𝖦 := overlap_matrix_sum_bound A hsym D (fun i => 𝔉)
      (fun i j => 𝔄) (fun i => integral_nonneg fun x => sq_nonneg _ )
      hdegree hzero hpair

𝗇 𝔈 𝘟₁
𝗃 𝔜 (ἀ → Fin 3) → ℝ
𝗇 𝔟 Measure $ Fin 3
𝗇 𝔠 ∀ i, IsProbabilityMeasure $ μ i
𝗃 𝔬 fun y => ἀ 𝔈
/-- Local observables on disjoint response supports are independent under the
actual conditional product probability measure. -/
theorem finite_product_local_observables_independent (n : ℕ)
    (μ : Fin n → 𝔟) [𝔠]
    (S T : 𝙍) (hST : Disjoint S T)
    (R : 𝔜 S) (Q : 𝔜 T) :
    IndepFun 𝔬 R
      𝔬 Q $ Measure.pi μ := by
  have hi : iIndepFun (fun i y => y i) $ Measure.pi μ :=
    iIndepFun_pi fun _ => measurable_id.aemeasurable
  have h := hi.indepFun_finset S T hST measurable_pi_apply
  exact h.comp (measurable_of_countable R) $ measurable_of_countable Q

𝗇 𝔘 𝙈
/-- Centered local scores on disjoint supports are conditionally orthogonal.
Their independence is derived from the product response measure. -/
theorem finite_product_local_scores_orthogonal (n : ℕ)
    (μ : Fin n → 𝔟) [𝔠]
    (S T : 𝙍) (hST : Disjoint S T)
    (R : 𝔜 S) (Q : 𝔜 T)
    (hR : ∫ y : 𝔘, R 𝔈 ∂Measure.pi μ = 0) :
     ∫ y : 𝔘, R 𝔈 * Q 𝔈 ∂Measure.pi μ = 0 := by
  have hi := finite_product_local_observables_independent n μ S T hST R Q
  rw [hi.integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable, hR, zero_mul]

𝗇 𝔚 ternaryMass a f V y
𝗇 𝔍 ∀ y, 0 ≤ 𝔚
/-- The ternary response masses as an actual probability mass function on indices. -/
def ternaryIndexPMF (a f V : ℝ) (ha : 𝙞) (hp : 𝔍) : PMF $ Fin 3 :=
  PMF.ofFintype (fun y => ENNReal.ofReal 𝔚) $ by
    rw [← ENNReal.ofReal_sum_of_nonneg 𝘞₂, ternary_normalized a f V ha]
    norm_num

/-- The corresponding genuine conditional response probability measure. -/
def ternaryIndexMeasure (a f V : ℝ) (ha : 𝙞) (hp : 𝔍) : 𝔟 :=
  (ternaryIndexPMF a f V ha hp).toMeasure

𝗇 𝔡 ternaryIndexMeasure a f V ha hp
instance ternaryIndexMeasure_isProbability (a f V : ℝ) (ha : 𝙞)
    (hp : 𝔍) : IsProbabilityMeasure 𝔡 :=
  PMF.toMeasure.isProbabilityMeasure _

𝗇 𝔣 {y}
theorem ternary_index_measure_singleton a f V ha
    hp y :
    (𝔡).real 𝔣 = 𝔚 := by
  rw [measureReal_def, ternaryIndexMeasure, PMF.toMeasure_apply_singleton _ _ $ measurableSet_singleton y ]
  exact ENNReal.toReal_ofReal $ hp y

𝗃 𝔩 ἀ a (f i) V ha $ hp i
𝗇 𝔎 fun i => 𝔩 ternaryIndexMeasure
𝗇 𝔧 ternaryMass a (f i) V
𝗇 𝔐 ∏ i, 𝔧 (y i)
𝗇 𝔑 ∀ i y, 0 ≤ 𝔧 y
/-- The conditional product measure has exactly the finite likelihood masses
used in the score construction. -/
theorem ternary_index_product_singleton n a V (f : 𝙔) ha
    (hp : 𝔑) y :
    (Measure.pi 𝔎).real 𝔣 =
      𝔐 := by
  have heq : 𝔣 = Set.pi Set.univ fun i => {y i} := by
    grind
  rw [measureReal_def, heq, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact 𝔩 ternary_index_measure_singleton $ y i

/-- Finite score expectations agree exactly with integrals under the actual
conditional response product measure. -/
theorem ternary_index_product_integral n a V (f : 𝙔) ha
    (hp : 𝔑) (F : 𝔘 → ℝ) :
     ∫ y, F y ∂Measure.pi 𝔎 =
      ∑ y, 𝔐 * F y := by
  rw [integral_fintype Integrable.of_finite]
  simp_rw [ternary_index_product_singleton, smul_eq_mul]

𝗇 𝔤 f ξ i
𝗃 𝔭 ἀ m n a V η f w ξ
/-- The actual coordinate scores are centered under the genuine conditional
response product probability measure. -/
theorem ternary_coordinate_score_measure_centered m n a V η
    f w
    ξ j ha
    (hp : ∀ i y, 0 ≤ ternaryMass a 𝔤 V y)
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    (∫ y, 𝔭 finiteCoordinateScore y j
      ∂Measure.pi fun i => ternaryIndexMeasure a 𝔤 V ha $ hp i ) = 0 := by
  rw [ternary_index_product_integral]
  exact 𝔭 finite_coordinate_score_centered j ha hpositive
