module

public import NearlyMinimax.PreconditionedPilot
public import NearlyMinimax.DyadicNesting
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The exact current/parent free-moment input of the determinant-cleared
increment polynomial, including the virtual identity parent at level zero. -/

open MeasureTheory ProbabilityTheory Matrix
𝚼
𝚨

𝚭
𝚩

𝗇 𝔥 𝚃
𝗇 𝔉 Fin 𝔥
def anchoredFinIndex (i : 𝔉) : 𝗎 :=
  (Fintype.equivFin 𝗎).symm i

𝗇 𝔄 incrementVariables 𝔥
𝗇 𝔦 𝘮
𝗇 𝔊 𝔦
𝗇 𝔖 𝘠
𝗃 𝔞 ἀ j x
𝗇 𝔧 j == 0
def dyadicIncrementFeature (j : ℕ) (x : Covariate d)
    (v : 𝔄) (z : Observation d) : ℝ :=
  match v with
  | Sum.inl m => match m with
    | Sum.inl it =>
      𝔞 preconditionedPilotFeature (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2)) z
    | Sum.inr it =>
      if 𝔖 then if it.2.1 = it.2.2 then 1 else 0 else
        preconditionedPilotFeature 𝔊 x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2)) z
  | Sum.inr pri =>
    if pri.1 && 𝔧 then 0 else
      preconditionedPilotFeature (if pri.1 then 𝔊 else j) x
        𝘳₁ z

𝗇 𝔓 (Fintype.equivFin 𝔄).symm a
𝗇 𝔣 Fin (Fintype.card 𝔄) → ℝ
def dyadicIncrementRawVector (j : ℕ) (x : Covariate d) (z : Observation d) :
    𝔣 :=
  fun a => 𝔞 dyadicIncrementFeature
    𝔓 z

def dyadicIncrementRawMean (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    𝔣 :=
  fun a => ∫ z, 𝔞 dyadicIncrementRawVector z a ∂observationLaw θ

𝗇 𝔨 𝘟
theorem dyadicPilotScale_parent_le d j : dyadicPilotScale d 𝔊 ≤ 𝔨 := by
  unfold dyadicPilotScale
  bound

𝗃 𝔟 Sum.inr $ ἀ $ anchoredFinIndex i
𝗇 𝔅 fun z => if parent && 𝔧 then 0 else preconditionedPilotFeature (if parent then 𝔦 else j) x (if response then 𝔟 Sum.inr else 𝔟 Sum.inl) z
𝗇 𝔇 fun z => if 𝘠 then if v.2.1 = v.2.2 then 1 else 0 else preconditionedPilotFeature 𝔦 x (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z
𝗇 𝔗 𝔞 dyadicIncrementFeature v
theorem dyadicIncrementFeature_measurable j x
    (v : 𝔄) : Measurable 𝔗 := by
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      exact 𝔞 preconditionedPilotFeature_measurable _
    | inr v =>
      change Measurable 𝔇
      split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_measurable _ x _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    change Measurable 𝔅
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_measurable _ x _

𝗃 𝔫 ἀ (ℓ := ℓ)
𝗇 𝔤 𝔫 dyadicIncrementRawVector j x
𝗇 𝔈 𝔤
theorem dyadicIncrementRawVector_measurable j (x : Covariate d) :
    Measurable 𝔈 :=
  measurable_pi_iff.mpr fun _ => 𝔞 dyadicIncrementFeature_measurable _

𝗇 𝔐 𝗌
𝗃 𝔩 ἀ C θ hθ
𝗇 𝔑 𝔩 observationLaw_isProbability
𝗇 𝔒 𝙟
𝗃 𝔛 𝔩 ἀ j x hx
𝗇 𝔢 𝔩 preconditionedPilotFeature_memLp_two _ x hx _
𝗃 𝔪 MemLp ἀ 2 $ observationLaw θ
theorem dyadicIncrementFeature_memLp_two (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : 𝔒) (j : ℕ) (x : Covariate d)
    (hx : 𝔐) (v : 𝔄) :
    𝔪 𝔗 := by
  let := 𝔑
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      exact 𝔛 preconditionedPilotFeature_memLp_two _
    | inr v =>
      change 𝔪 𝔇
      split_ifs <;> first | exact memLp_const _ | exact 𝔢
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    change 𝔪 𝔅
    split_ifs <;> first | exact memLp_const _ | exact 𝔢

𝗇 𝔎 𝔟 Sum.inr
𝗇 𝔏 𝔟 Sum.inl
𝗇 𝔚 Fintype.card 𝔄 * preconditionedPilotMomentConstant C ℓ * 𝔨
section

variable (C)
    (θ)
    (hθ : 𝔒)
    (j)
    (x)
    (hx : 𝔐)

include hθ j hx

𝗇 𝔘 𝔛 preconditionedPilotFeature_uniform_second_le
/-- Original-law moment bound for every current/parent free coordinate;
the level-zero identity parent is covered by the same fixed constant. -/
theorem dyadicIncrementFeature_second_le (v : 𝔄) :
     ∫ z, 𝔗 z ^ 2 ∂observationLaw θ ≤
      preconditionedPilotMomentConstant C ℓ * 𝔨 := by
  let := 𝔑
  have hC := preconditionedPilotMomentConstant_pos C ℓ
  have hroot : 1 ≤ preconditionedPilotMomentConstant C ℓ := le_max_left ..
  have hK : 1 ≤ 𝔨 := by
    unfold dyadicPilotScale
    bound
  have hnon :=
    mul_nonneg hC.le (dyadicPilotScale_pos d j).le
  have hparent a :=
    (𝔩 preconditionedPilotFeature_uniform_second_le 𝔊 x hx a).trans
      $ mul_le_mul_of_nonneg_left (dyadicPilotScale_parent_le d j) hC.le
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      exact 𝔘 _
    | inr v =>
      dsimp only [dyadicIncrementFeature]
      split_ifs <;> first
        | simpa using mul_le_mul hroot hK  𝖠₄  hC.le
        | simpa using hnon
        | exact hparent _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent with
    | false =>
      cases response
      all_goals first
        | simpa [dyadicIncrementFeature] using 𝔘
            𝔏
        | simpa [dyadicIncrementFeature] using 𝔘
            𝔎
    | true =>
      cases response <;> by_cases hj : 𝔖
      all_goals first
        | simpa [dyadicIncrementFeature, hj] using hnon
        | simpa [dyadicIncrementFeature, hj] using hparent
            𝔏
        | simpa [dyadicIncrementFeature, hj] using hparent
            𝔎

theorem dyadicIncrementRawVector_second_le :
     ∫ z, ‖𝔈 z‖ ^ 2 ∂observationLaw θ ≤
      𝔚 := by
  let := 𝔑
  apply (KernelMomentBounds.vector_second_le_sum_coordinates 𝔞 dyadicIncrementRawVector
    𝔞 dyadicIncrementRawVector_measurable fun _ => 𝔛 dyadicIncrementFeature_memLp_two _ ).trans
  exact (Finset.sum_le_sum fun a _ => 𝔛 dyadicIncrementFeature_second_le _ ).trans_eq
    $ by simp [mul_assoc]

end

𝗃 𝔜 ἀ θ j x
/-- The finite-coordinate current Gram and the two true vector moment families. -/
def dyadicFinPilotGram (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix 𝔉 𝔉 ℝ :=
  anchoredFinReindex d ℓ 𝔜 dyadicPreconditionedGram

def dyadicFinPilotMoments (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Bool → 𝔉 → ℝ :=
  fun response i => 𝔜 preconditionedPilotPopulation
    $ if response then 𝔎
      else 𝔏

def dyadicIncrementPopulation (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    𝔄 → ℝ :=
  incrementValuation 𝔜 dyadicFinPilotGram
    (if 𝔖 then 1 else dyadicFinPilotGram θ 𝔊 x)
    𝔜 dyadicFinPilotMoments
    $ if 𝔖 then 0 else dyadicFinPilotMoments θ 𝔊 x

/-- Original observation-law integration produces precisely the free-moment
population point, including the deterministic identity/zero root parent. -/
theorem dyadicIncrementFeature_integral C
    θ (hθ : 𝔒) j x
    (hx : 𝔐) (v : 𝔄) :
     ∫ z, 𝔗 z ∂observationLaw θ =
      𝔜 dyadicIncrementPopulation v := by
  let := 𝔑
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
        RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
        anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex,
        preconditionedPilotPopulation] using
        𝔛 preconditionedPilotPopulation_gram (anchoredFinIndex i) $ anchoredFinIndex t
    | inr v =>
      by_cases hj : 𝔖
      · simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, hj, Matrix.one_apply]
      · simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
          anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex, hj,
          preconditionedPilotPopulation] using
          𝔩 preconditionedPilotPopulation_gram 𝔊 x hx
            (anchoredFinIndex v.2.1) $ anchoredFinIndex v.2.2
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response <;> by_cases hj : 𝔖
    all_goals simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
      dyadicFinPilotMoments, hj, preconditionedPilotPopulation]

theorem dyadicIncrementRawMean_eq_population C
    θ (hθ : 𝔒) j x
    (hx : 𝔐) :
    𝔜 dyadicIncrementRawMean = fun a =>
      𝔜 dyadicIncrementPopulation
        𝔓 := by
  funext a
  exact 𝔛 dyadicIncrementFeature_integral _

theorem dyadicFinPilotGram_eq_normalized C
    θ (hθ : 𝔒) j (x : Covariate d) :
    𝔫 dyadicFinPilotGram θ j x =
      anchoredFinNormalizedGram 𝔞 dyadicNormalizedAnchor 𝔜 dyadicNormalizedDensity := by
  unfold dyadicFinPilotGram dyadicPreconditionedGram anchoredFinNormalizedGram
  rw [dyadicKnownGram_eq_normalized, 𝔩 dyadicPopulationGram_eq_normalized]

theorem dyadicFinPilotMoments_eq_normalized C
    θ (hθ : 𝔒) j x
    (hx : 𝔐) t (i : 𝔉) :
    𝔜 dyadicFinPilotMoments t i =
      anchoredPreconditionedMoment 𝔞 dyadicNormalizedAnchor 𝔜 dyadicNormalizedDensity
        (if t then 𝙃 else θ.regression ∘ 𝔞 dyadicCellAffine) (anchoredFinIndex i) := by
  cases t
  · exact 𝔛 preconditionedPilotPopulation_response _
  · exact 𝔛 preconditionedPilotPopulation_constant _

𝗇 𝔔 𝔤 (z i) a
𝗇 𝔍 𝗷
𝗇 𝔙 𝙌
𝗇 𝔠 𝔈 $ z i
𝗇 𝔡 fun z => z i
theorem dyadicIncrementRawVector_sample_facts C
    θ (hθ : 𝔒) j x
    (hx : 𝔐) :
    iIndepFun (fun i (z : 𝔙) => 𝔠) 𝔍 ∧
    (∀ i , Measurable fun z : 𝔙 => 𝔠 ) ∧
    (∀ i t , IdentDistrib
      (fun z => 𝔞 dyadicIncrementRawVector $ z i )
      (fun z => 𝔈 $ z t ) 𝔍 𝔍) ∧
    (∀ i a, MemLp (fun z => 𝔔)
      2 𝔍) ∧
     ∀ i a, ∫ z : 𝔙, 𝔔 ∂𝔍 =
      𝔜 dyadicIncrementRawMean a := by
  let := 𝔑
  have hm := 𝔫 dyadicIncrementRawVector_measurable j x
  have hp i : MeasurePreserving 𝔡
      𝔍 $ observationLaw θ := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi fun _ => hm.aemeasurable ,
    𝘋₂, ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib 𝔡
        (fun z => z t) 𝔍 𝔍 :=
      𝘏₁
    exact ht.comp hm
  · intro i a
    exact (𝔛 dyadicIncrementFeature_memLp_two _).comp_measurePreserving $ hp i
  · intro i a
    exact integral_comp_eval
       (𝔞 dyadicIncrementFeature_measurable
        𝔓).aestronglyMeasurable

theorem dyadicIncrementRawVector_sample_second_le C
    θ (hθ : 𝔒) j x
    (hx : 𝔐) i :
     ∫ z : 𝔙, ‖𝔠‖ ^ 2 ∂𝔍 ≤
      𝔚 := by
  let := 𝔑
  unfold sampleLaw
  rw [integral_comp_eval (μ := fun _ => observationLaw θ)
     ((𝔞 dyadicIncrementRawVector_measurable).norm.pow_const 2).aestronglyMeasurable ]
  exact 𝔛 dyadicIncrementRawVector_second_le
