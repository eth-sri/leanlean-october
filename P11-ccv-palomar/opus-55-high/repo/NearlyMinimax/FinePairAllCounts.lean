module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.FinePairMatrixCost
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine even-subset expansion of the fine density/response row.
The time-weighted field moments are integrals of the actual hyperplane law. -/
𝚫
𝚨
𝚩
𝚭
𝚬

def finePairEvenSelector (j : ℕ) : ℝ := if 𝘠 then 0 else if Even j then 1 else 0

𝗃 𝔟 if ἀ = 2 then 1 else 0
theorem finePairEvenSelector_split j :
    finePairEvenSelector j = 𝔟 j +
       if 𝙳₁ ∧ Even j then 1 else 0 := by
  by_cases hj0 : 𝘠
  · aesop
  by_cases hj2 : j = 2
  · aesop
  by_cases hj : Even j
  · have hj4 : 𝙳₁ := by grind
    simp [finePairEvenSelector, hj0, hj2, hj4]
  · simp [finePairEvenSelector, hj2, hj]

𝗃 𝔠 ∏ i ∈ ἀ, finePairTimeFieldValue e (U i)
𝗇 𝔈 𝔠 S
𝗇 𝔉 𝙇
𝗇 𝔔 𝖻₂
theorem finePairTimeField_product_measurable (U : 𝔉)
    S :
    Measurable fun e => 𝔈 :=
  Finset.measurable_fun_prod S fun i _ =>
    𝔔

theorem finePairTimeField_product_abs (U : 𝔉)
    S e :
    |𝔈| = 1 := by
  rw [Finset.abs_prod]
  simp only [finePairTimeFieldValue_abs, Finset.prod_const_one]

𝗃 𝔡 ἀ d lo hi
𝗃 𝔣 e.1 * ἀ
theorem finePairTimeField_weighted_product_integrable [NeZero d]
    (lo hi : ℝ) (U : 𝔉) S :
    Integrable (fun e =>
      𝔣 𝔈) 𝔡 finePairTimeFieldMeasure :=
  (𝔡 finePairTimeFieldMeasure_fst_integrable).mul_bdd
    (finePairTimeField_product_measurable U S).aestronglyMeasurable
    $ Filter.Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, finePairTimeField_product_abs]

def finePairTimeSubsetMoment (lo hi : ℝ) (U : 𝔉)
    (S : 𝙍) : ℝ :=
  ∫ e : 𝙺₂,
    𝔣 𝔈 ∂𝔡 finePairTimeFieldMeasure

theorem finePairTimeSubsetMoment_actual [NeZero d]
    (lo hi : ℝ) (U : 𝔉) S :
    finePairTimeSubsetMoment lo hi U S =
      ∫ T in Icc lo hi, T * ∫ z, ∏ i ∈ S, boundedHyperplaneFieldValue z (U i)
        ∂boundedHyperplaneFieldLaw d T := by
  rw [finePairTimeSubsetMoment, 𝔡 finePairTimeFieldMeasure_integral _
    $ finePairTimeField_weighted_product_integrable lo hi U S ]
  simp only [finePairTimeFieldValue, integral_const_mul]

𝗇 𝔄 ∏ i ∈ W, p i
𝗇 𝔎 𝙔
section Generic
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

𝗇 𝔗 ∏ i ∈ W, ψ ζ i
𝗇 𝔞 𝗔 (A ζ) c Φ
𝗇 𝔅 𝔗 * 𝔞
𝗇 𝔏 finePairCountCoefficient a b M n W.card
𝗇 𝔒 finePairDensityReset a b z eps p (ψ ζ) i
𝗇 𝔙 𝔏 * (𝔄 * 𝔗) * finePairEvenSelector W.card
𝗇 𝔜 𝔏 * 𝔄 * finePairEvenSelector W.card
𝗃 𝔤 ἀ q C c Φ
theorem finePairPacket_even_subset_expansion
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 𝙆) (hab : 𝙭)
    (M q : ℕ) (C : ℝ) (A : Z → ι → 𝙛)
    (hA : 𝙚)
    (hcost : 𝙧) (c : 𝙛)
    (p : 𝔎) (hp : ∀ i, p i ∈ 𝘔₂) (ψ : Z → 𝔎)
    (hmψ : ∀ i, Measurable fun ζ => ψ ζ i ) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    Φ :
     ∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, 𝔒) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A =
      ∑ W ∈ Finset.univ.powerset,
        𝔜 *
           ∫ ζ, 𝔅 ∂σ := by
  have hm z eps i :
      Measurable fun ζ => 𝔒 := by
    unfold finePairDensityReset
    fun_prop
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c _
    𝙺
    (b^n) (pow_nonneg 𝙬₁ n) (fun ζ e =>
      finite_density_product_abs_bound _ b 𝙬₁
        $ finePairFieldReset_abs_le a b ha hab M p hp ψ hbψ 𝘕₂ )
    Φ 𝔤 finePairResponseAtomBound 𝔤 finePairResponseAtomBound_le]
  have hiRsp :=
    responseMatrixAction_integrable σ q C A (separatedMatrix_entry_integrable σ A hA hcost) c Φ
  have hi W :
      Integrable (fun ζ => 𝔅) σ := by
    apply hiRsp.bdd_mul
      (Finset.measurable_fun_prod W fun i _ => hmψ i ).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, Finset.abs_prod]
      exact (Finset.prod_le_prod₀ 𝖢 fun i _ => hbψ ζ i ).trans_eq
        Finset.prod_const_one
  have hsubset ζ :
       ∫ᵛ e, ∏ i, finePairDensityReset a b e.1 e.2 p (ψ ζ) i
        ∂<•finePairDensitySignedRule a b M =
      ∑ W ∈ Finset.univ.powerset,
        𝔙 := by
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, finePairEvenSelector] using
      finePairDensitySignedRule_product_expansion a b M Finset.univ p $ ψ ζ
  simp_rw [hsubset]
  have he W ζ :
      𝔙 * 𝔞 =
      𝔜 *
        𝔅 := 𝖢₃
  simp_rw [Finset.sum_mul, he]
  rw [integral_finsetSum _ fun W _ => (hi W).const_mul _ ]
  simp only [integral_const_mul]

end Generic

𝗇 𝔇 𝗔 𝖺₂ c Φ
𝗇 𝔊 𝖲
𝗇 𝔍 𝔠 W
𝗃 𝔘 ἀ ad bd T0 N M q C U p c Φ
𝗇 𝔐 𝔘 finePairFineFirstAction
𝗇 𝔓 finePairCountCoefficient ad bd M n W.card
𝗇 𝔚 𝖳
𝗇 𝔛 finePairTimeSubsetMoment T0 N U W
theorem finePairFineFirstAction_even_subset_expansion [NeZero d]
    (ad bd T0 N : ℝ) (ha : 𝖼) (hab : 𝖽) (M q : ℕ) (C : ℝ)
    (U : 𝔉) (p : 𝔎) (hp : 𝔚)
    (c : 𝔊) Φ :
    𝔐 =
      ∑ W ∈ Finset.univ.powerset,
        𝔓 * 𝔄 * finePairEvenSelector W.card *
          𝔛 * 𝔇 := by
  rw [finePairFineFirstAction, finePairPacket_even_subset_expansion _ ad bd ha hab M q C _
    𝖼₂ (finePairTimeMatrix_cost_integrable d T0 N _)
    c p hp (fun ζ i => finePairTimeFieldValue ζ $ U i )
    (fun i => 𝔔)
    𝗀₁]
  apply Finset.sum_congr rfl
  intro W _
  change _ * ∫ e : 𝙺₂, 𝔍 *
    𝗔 (fun i j => e.1 * 𝖺₂ i j) c Φ
    ∂finePairTimeFieldMeasure d T0 N = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he e :
      𝔍 *
        𝔣 𝔇 =
      𝔣 𝔍 *
        𝔇 := 𝖢₃
  simp_rw [he]
  rw [integral_mul_const]
  unfold finePairTimeSubsetMoment
  ring

𝗇 𝔖 (Finset.univ : 𝙍).powerset
def finePairPairAliasAction (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : 𝔉) (p : 𝔎) (c : 𝔊)
    (Φ : 𝔊 → ℝ) : ℝ :=
  ∑ W ∈ 𝔖,
    𝔓 * 𝔄 * 𝔟 W.card *
      𝔛 * 𝔇

def finePairEvenFieldAction (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : 𝔉) (p : 𝔎) (c : 𝔊)
    (Φ : 𝔊 → ℝ) : ℝ :=
  ∑ W ∈ 𝔖,
    𝔓 * 𝔄 *
      (if 4 ≤ W.card ∧ Even W.card then 1 else 0) *
        𝔛 * 𝔇

𝗇 𝔑 𝔘 finePairPairAliasAction
theorem finePairFineFirstAction_alias_even_field [NeZero d]
    (ad bd T0 N : ℝ) (ha : 𝖼) (hab : 𝖽) (M q : ℕ) (C : ℝ)
    (U : 𝔉) (p : 𝔎) (hp : 𝔚)
    (c : 𝔊) Φ :
    𝔐 =
      𝔑 +
        𝔘 finePairEvenFieldAction := by
  rw [finePairFineFirstAction_even_subset_expansion ad bd T0 N ha hab M q C U p hp c Φ]
  simp only [finePairEvenSelector_split, finePairPairAliasAction, finePairEvenFieldAction,
    mul_add, add_mul, Finset.sum_add_distrib]

theorem finePairPairAliasAction_zero_selected_count
    ad bd T0 N (ha : 𝖼) (hab : 𝖽) M q
    (hn : 𝖬₂) (hM : n ≤ M) C
    U (p : 𝔎) (c : 𝔊)
    Φ :
    𝔑 = 0 := by
  apply Finset.sum_eq_zero
  intro W _
  by_cases hW : W.card = 2
  · rw [hW, finePairCountCoefficient_two_exact ad bd ha hab M n  𝖡₃  hM]
    bound
  simp_all
