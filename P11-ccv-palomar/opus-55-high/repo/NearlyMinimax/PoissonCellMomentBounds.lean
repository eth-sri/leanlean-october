module

public import NearlyMinimax.PoissonCellMoments
public import NearlyMinimax.PoissonCellPairEvents
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

/-! Higher moment bounds for the genuine Poisson cell field, derived from
the fair-sign occupancy formula and two actual disjoint same-cell pairs. -/
𝚵
open scoped ENNReal NNReal
𝚨
𝚬

/-- Ordered four distinct observation indices, giving two disjoint pairs. -/
abbrev CellMomentQuadruple (j : ℕ) := {q : Fin 4 → Fin j // Function.Injective q}

theorem cellMomentQuadruple_card_le j :
    Fintype.card (CellMomentQuadruple j) ≤ j^4 := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_subtype_le fun q : Fin 4 → Fin j => Function.Injective q

𝛝

𝗇 𝔏 H → X → Fin 2
𝗇 𝔐 Fin j → X
𝗇 𝔑 Fin n → Fin 2
𝗇 𝔒 partitionFieldPattern ρ h $ U l
𝗇 𝔠 Fin n → H
def partitionFiberEvenIndicator (ρ : 𝔏) (n j : ℕ)
    (U : 𝔐) (h : 𝔠) : ℝ :=
  if ∀ p : 𝔑,
    Even (Finset.univ.filter fun l => 𝔒 = p ).card
    then 1 else 0

𝗇 𝔍 Measurable $ Function.uncurry ρ
𝗇 𝔙 partitionFiberEvenIndicator ρ n j U
theorem partitionFiberEvenIndicator_measurable (ρ : 𝔏)
    (hρ : 𝔍) n j U :
    Measurable 𝔙 := by
  let F : (Fin j → 𝔑) → ℝ := fun p =>
    if ∀ c , Even (Finset.univ.filter fun l => p l = c ).card
      then 1 else 0
  have hF : Measurable F := measurable_of_finite _
  have hp : Measurable fun h : 𝔠 => fun l => 𝔒 := by
    apply Measurable.of_eval
    intro l
    exact (partitionFieldPattern_measurable ρ hρ n).comp
      $ measurable_id.prodMk measurable_const
  exact hF.comp hp

𝗇 𝔣 U $ q.val 0
𝗇 𝔤 U $ q.val 1
𝗇 𝔥 U $ q.val 2
𝗇 𝔦 U $ q.val 3
𝗇 𝔄 partitionFiberBothIndicator ρ n 𝔣 𝔤 𝔥 𝔦 h
𝗇 𝔔 ![a,b,c,e]
theorem partitionFiberEvenIndicator_le_pairs ρ n j
    (hj : 𝙳₁) (U : 𝔐) (h : 𝔠) :
    𝔙 h ≤
      ∑ q : CellMomentQuadruple j, 𝔄 := by
  unfold partitionFiberEvenIndicator
  split_ifs with heven
  · obtain ⟨a, _, b, _, c, _, e, _, hba, hca, hcb, hea, heb, hec, hab, hce⟩ :=
      even_cells_two_disjoint_pairs Finset.univ
        (fun l => 𝔒) (by simpa using hj) heven
    have hinj : Function.Injective 𝔔 := by
      intro i l hil
      fin_cases i <;> fin_cases l <;> simp_all
    let q : CellMomentQuadruple j := ⟨𝔔, hinj⟩
    have hq : 𝔄 = 1 := by
      simp only [q, partitionFiberBothIndicator]
      simp_all
    rw [← hq]
    exact Finset.single_le_sum (f := fun q =>
      𝔄) fun q _ => by
      unfold partitionFiberBothIndicator
      positivity (Finset.mem_univ q)
  · apply Finset.sum_nonneg
    intro q _
    unfold partitionFiberBothIndicator
    positivity

def poissonCellEvenIndicator (ρ : 𝔏) (j : ℕ) (U : 𝔐)
    (z : partitionFieldMark H) : ℝ := partitionFiberEvenIndicator ρ z.1 j U z.2.1

𝗇 𝔚 poissonCellEvenIndicator ρ j U
theorem poissonCellEvenIndicator_measurable (ρ : 𝔏)
    (hρ : 𝔍) j U :
    Measurable 𝔚 :=
  measurable_sigma_of_fibers _ fun n =>
    (partitionFiberEvenIndicator_measurable ρ hρ n j U).comp measurable_fst

𝗃 𝔨 ∏ l, ἀ ρ z (U l)
𝗇 𝔅 ∫ z, 𝔨 poissonCellFieldValue ∂poissonCellFieldLaw μ r
𝗇 𝔖 poissonCellFieldLaw μ r
𝗇 𝔜 𝘫
𝗇 𝔡 poissonCellEvenIndicator_measurable ρ hρ j U
/-- The actual field moment is the probability of even occupancy, from the
constructed independent fair signs and the true Poisson mark law. -/
theorem poissonCellField_product_moment_eq_even (μ : Measure H) [IsProbabilityMeasure μ]
    r ρ (hρ : 𝔍)
    j (U : 𝔐) :
    𝔅 =
      ∫ z, 𝔚 z ∂𝔖 := by
  rw [poissonCellField_integral_series μ r _
    𝗛₂
     fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
      Finset.prod_const_one, le_refl] ,
    poissonCellField_integral_series μ r _ 𝔡
       fun z => by unfold poissonCellEvenIndicator partitionFiberEvenIndicator
                   bound ]
  apply tsum_congr
  intro n
  congr 1
  change ∫ z, 𝔨 partitionFieldFiberValue ∂partitionFieldFiberLaw μ n = _
  rw [partitionFieldFiber_product_moment μ ρ hρ n j U]
  change ∫ h, 𝔙 h ∂Measure.pi 𝔜 =
    ∫ z, 𝔙 z.1
      ∂(Measure.pi 𝔜).prod (cellSignLaw 𝔑)
  rw [integral_fun_fst]
  simp

𝗇 𝔇 𝔣
𝗇 𝔈 𝔤
𝗇 𝔉 𝔥
𝗇 𝔊 𝔦
𝗇 𝔗 fun q _ => hq q
𝗇 𝔞 poissonCellBothIndicator ρ 𝔇 𝔈 𝔉 𝔊
/-- The higher field moment is bounded by the genuine probabilities of two
disjoint same-cell pairs, with no assumed field moment bound. -/
theorem poissonCellField_product_moment_le_two_pair_probabilities
    (μ : Measure H) [IsProbabilityMeasure μ] r
    ρ (hρ : 𝔍)
    j (hj : 𝙳₁) (U : 𝔐) :
    𝔅 ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-r *
        (1 - partitionBothProbability μ ρ 𝔇 𝔈
          𝔉 𝔊)) := by
  rw [poissonCellField_product_moment_eq_even μ r ρ hρ j U]
  have hi : Integrable 𝔚 𝔖 :=
    Integrable.of_bound (𝔡).aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun z => by
        unfold poissonCellEvenIndicator partitionFiberEvenIndicator
        bound
  have hq (q : CellMomentQuadruple j) : Integrable 𝔞 𝔖 :=
    Integrable.of_bound (poissonCellBothIndicator_measurable ρ hρ ..).aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun z => by
        unfold poissonCellBothIndicator partitionFiberBothIndicator
        bound
  calc
    _ ≤ ∫ z, ∑ q : CellMomentQuadruple j, 𝔞 z ∂𝔖 :=
      integral_mono hi (integrable_finsetSum Finset.univ 𝔗)
         fun z => partitionFiberEvenIndicator_le_pairs ρ z.1 j hj U z.2.1
    𝘿 := by
      rw [integral_finsetSum Finset.univ 𝔗]
      apply Finset.sum_congr rfl
      intro q _
      exact poissonCellBothIndicator_integral μ r ρ hρ ..

𝗇 𝔎 pairSameIndicator ρ a b h * pairSameIndicator ρ c e h
𝗇 𝔓 pairSameIndicator ρ a b h + pairSameIndicator ρ c e h
𝗇 𝔘 pairSameIndicator_integrable μ ρ hρ c e
𝗇 𝔛 partitionSameProbability μ ρ
𝗇 𝔟 pairSameIndicator_integrable μ ρ hρ a b
𝗇 𝔢 partitionBothProbability μ ρ a b c e
𝗃 𝔩 ∫ h, ἀ ∂μ
/-- The union separation probability dominates half the sum of the two
individual separation probabilities. This comes from the actual indicators. -/
theorem partition_union_separation_ge_half (μ : Measure H) [IsProbabilityMeasure μ]
    ρ (hρ : 𝔍) (a b c e : X) :
    ( 1 - 𝔛 a b +
      (1 - 𝔛 c e)) / 2 ≤
        1 - 𝔢 := by
  have hp : Integrable (fun h => 𝔎) μ :=
    Integrable.of_bound
      ((pairSameIndicator_measurable ρ hρ a b).mul
        $ pairSameIndicator_measurable ρ hρ c e ).aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun h => by
        unfold pairSameIndicator
        bound
  have hs := ((𝔟).add
    𝔘).div_const 2
  have h := integral_mono hp hs fun h => show
      𝔎 ≤
        𝔓 / 2 by
      unfold pairSameIndicator
      bound
  rw [integral_div] at h
  change 𝔩 𝔎 ≤
    𝔩 𝔓 / 2 at h
  rw [integral_add 𝔟
    𝔘] at h
  change 𝔢 ≤
    (𝔛 a b + 𝔛 c e) / 2 at h
  linarith

/-- The source two-pair exponential higher-moment envelope for the actual
constructed Poisson cell field, for all orders at least four. -/
theorem poissonCellField_product_moment_abs_le_two_pairs
    (μ : Measure H) [IsProbabilityMeasure μ] r
    ρ (hρ : 𝔍)
    j (hj : 𝙳₁) (U : 𝔐) :
    |𝔅| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-r / 2 *
        ( 1 - 𝔛 𝔇 𝔈 +
          (1 - 𝔛 𝔉 𝔊))) := by
  rw [abs_of_nonneg $ poissonCellField_product_moment_nonneg μ r ρ hρ j U ]
  apply (poissonCellField_product_moment_le_two_pair_probabilities μ r ρ hρ j hj U).trans
  apply Finset.sum_le_sum
  intro q _
  apply Real.exp_le_exp.mpr
  have h := partition_union_separation_ge_half μ ρ hρ
    𝔇 𝔈 𝔉 𝔊
  nlinarith
