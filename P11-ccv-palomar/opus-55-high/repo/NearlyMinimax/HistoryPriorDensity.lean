module

public import NearlyMinimax.HistoryReferenceMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# The actual positive polynomial density on independently marked histories

Each history is evaluated in its canonical word. Its signed weight is the
proved finite upper-set polynomial, not a prescribed prior density.
-/

𝚩
𝚯
𝚮
𝚨

𝚲

𝗇 𝔅 𝙁
𝗇 𝔓 𝙏
𝗇 𝔔 𝙗
𝗃 𝔪 Fin.cast (historyShapeLength_out dependent ἀ).symm x.position
/-- The signed mark at an actual canonical heap occurrence. -/
def historyMarkedPieceWeight (dependent : 𝔅)
    (a : 𝔓) (h : 𝔔) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a $ h.2 𝔪 h.1

𝗇 𝔡 historyMarkedPieceWeight dependent a h
/-- The source upper-set polynomial on the actual marked dependency heap. -/
def historyMarkedDensity (dependent : 𝔅) (ρ t : ℝ)
    (a : 𝔓) (h : 𝔔) : ℝ :=
  historyScaledUpperDensity 𝔡 ρ Finset.univ t

𝗇 𝔏 (t / ρ) ^ P.card * historyOrderVolume P
𝗇 𝔐 𝘡₂ t a
𝗇 𝔑 𝗬
𝗇 𝔙 Fin 𝗠₁
𝗇 𝔜 𝔪 g
theorem historyMarkedDensity_fiber_measurable (dependent : 𝔅) (ρ t : ℝ)
    [MeasurableSpace E] (a : 𝔓) (ha : Measurable a)
    g :
    Measurable fun marks => 𝔐 𝔑 := by
  classical
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable fun marks : 𝔙 → E =>
    ∑ P ∈ historyUpperSets (Finset.univ : Finset $ WordHeapPiece g.out dependent ),
      𝔏 * ∏ x ∈ P,
        a (marks 𝔜)
  apply Finset.measurable_fun_sum _
  intro P hP
  apply Measurable.const_mul
  apply Finset.measurable_fun_prod _
  intro x hx
  exact ha.comp $ measurable_pi_apply _

theorem historyMarkedDensity_measurable (dependent : 𝔅) (ρ t : ℝ)
    [MeasurableSpace E] (a : 𝔓) (ha : Measurable a) :
    Measurable 𝔐 :=
  (historyMarked_measurable_iff dependent _).2
    $ historyMarkedDensity_fiber_measurable dependent ρ t a ha

𝗇 𝔉 𝘼
𝗇 𝔍 𝘽
𝗇 𝔒 𝙂
𝗇 𝔢 𝘈
𝗇 𝔣 𝙐
/-- The source positivity interval is uniform over all shapes and all bounded marks. -/
theorem historyMarkedDensity_bounds (dependent : 𝔅)
    (hrefl : 𝔒) (hsymm : 𝔉)
    Δ (hlabels : 𝔍)
    ρ t B (hρ : 𝘢₁) (ht : 𝔢) (hB : 𝔣)
    a (ha : ∀ e, |a e| ≤ B)
    (hsmall : 𝘡₁ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : 𝔔) :
    𝙖 ^ Fintype.card J ≤ 𝔐 h ∧
      𝔐 h ≤ 𝗞 ^ Fintype.card J :=
  wordHeap_density_bounds h.1.out dependent hrefl hsymm Δ hlabels
    𝔡 ρ t B hρ ht hB (fun _ => ha _) hsmall

𝗇 𝔄 𝘰
𝗇 𝔇 ∏ x ∈ P, a (marks $ index x )
𝗇 𝔈 ∫ e, a e ∂π
𝗇 𝔚 Integrable a π
section

variable [Fintype I]
    [DecidableEq I]
    [MeasurableSpace E]
    (π : Measure E)
    [IsProbabilityMeasure π]
    (a : 𝔓)

𝗇 𝔎 a $ marks i
𝗇 𝔖 fun i e => if 𝚒₁ then a e else 1
𝗇 𝔗 I → E
𝗇 𝔞 ∏ i ∈ S, 𝔎
𝗃 𝔦 ∫ marks : 𝔗, ἀ ∂𝔄
𝗃 𝔩 ∏ i : I, if i ∈ S then ἀ else 1
/-- A finite product over selected independent coordinates factors into expectations. -/
theorem historyIntegral_pi_finset_prod S :
    𝔦 𝔞 =
      ∏ _i ∈ S, 𝔈 := by
  classical
  have hp : ∀ marks : 𝔗, 𝔩 𝔎 =
      𝔞 := fun marks => Finset.prod_ite_mem_eq S _
  simp_rw [← hp]
  rw [integral_fintype_prod_eq_prod 𝔖]
  calc
    _ = 𝔩 𝔈 := by
      apply Finset.prod_congr rfl
      bound
    𝘿 := Finset.prod_ite_mem_eq S _

𝗃 𝔫 Integrable (fun marks : 𝔗 => ἀ) 𝔄
theorem historyIntegrable_pi_finset_prod (ha : 𝔚) S :
    𝔫 𝔞 := by
  classical
  have hp := Integrable.fintype_prod
    (f := 𝔖)
     fun i => 𝖥₄
  simpa only [Finset.prod_ite_mem_eq] using hp

𝗇 𝔠 ∏ i ∈ P.image index, 𝔎
/-- Selected independent mark products factor even with an injective piece indexing. -/
theorem historyIntegral_pi_indexed_prod [DecidableEq A] index (hi : Function.Injective index) (P : Finset A) :
    𝔦 𝔇 =
      ∏ _x ∈ P, 𝔈 := by
  have hp : ∀ marks : 𝔗, 𝔠 =
      𝔇 := fun marks => Finset.prod_image hi.injOn
  calc
    _ = 𝔦 𝔠 := by
      simp_all
    _ = ∏ _i ∈ P.image index, 𝔈 := historyIntegral_pi_finset_prod π a _
    𝘿 := Finset.prod_image hi.injOn

theorem historyIntegrable_pi_indexed_prod [DecidableEq A] (ha : 𝔚) index
    (hi : Function.Injective index) (P : Finset A) :
    𝔫 𝔇 := by
  simpa only [Finset.prod_image hi.injOn] using historyIntegrable_pi_finset_prod π a ha $ P.image index

end

𝗇 𝔘 fun i j => ¬ dependent i j
/-- Occurrences in a canonical heap have distinct independent mark coordinates. -/
def historyMarkedPieceIndex (dependent : 𝔅)
    (g : HistoryShape 𝔘) : WordHeapPiece g.out dependent → 𝔙 :=
  fun x => 𝔜

𝗇 𝔤 𝔈 = 0
section

variable (dependent : 𝔅)

theorem historyMarkedPieceIndex_injective g :
    Function.Injective $ historyMarkedPieceIndex dependent g := by
  intro x y hxy
  apply WordHeapPiece.ext
  exact Fin.cast_injective _ hxy

/-- Centering kills every nonempty upper-set monomial of the actual density. -/
theorem historyMarkedDensity_fiber_integral_one (ρ t : ℝ)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    a (ha : 𝔚) (hcenter : 𝔤)
    g :
     ∫ marks, 𝔐 𝔑
      ∂𝔄 = 1 := by
  classical
  let index := historyMarkedPieceIndex dependent g
  have hi := historyMarkedPieceIndex_injective dependent g
  have hterm : ∀ P ,
      Integrable (fun marks => 𝔏 * 𝔇)
        𝔄 := by
    intro P
    exact (historyIntegrable_pi_indexed_prod π a ha index hi P).const_mul _
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change ∫ marks, ∑ P ∈ historyUpperSets Finset.univ,
    𝔏 * 𝔇
    ∂𝔄 = 1
  rw [integral_finsetSum _ fun P _ => hterm P ]
  simp_rw [integral_const_mul, historyIntegral_pi_indexed_prod π a index hi, hcenter]
  rw [Finset.sum_eq_single ∅]
  · simp
  · simp_all
  · simp

@[simp] theorem historyMarkedDensity_zero ρ
    a (h : 𝔔) : 𝘡₂ 0 a h = 1 := by
  unfold historyMarkedDensity historyScaledUpperDensity
  simp

end

𝗇 𝔟 𝚇₂ t a 𝔑
/-- The actual polynomial tilts the independent marks within a shape. -/
def historyMarkedFiberPrior (dependent : 𝔅) (Δ : ℕ) (t : ℝ)
    [MeasurableSpace E] (π : Measure E) (a : 𝔓)
    (g : HistoryShape 𝔘) :
    Measure $ 𝔙 → E :=
  (𝔄).withDensity
     fun marks => ENNReal.ofReal 𝔟

𝗇 𝔊 t * B / historyReferenceRho Δ ≤ 𝙥
𝗃 𝔧 ἀ dependent Δ t π a
𝗇 𝔛 𝔧 historyMarkedFiberPrior g
/-- Positivity is derived from the dependency heap, and normalization from centered marks. -/
theorem historyMarkedFiberPrior_probability (dependent : 𝔅)
    (hrefl : 𝔒) (hsymm : 𝔉)
    (Δ : ℕ) (hlabels : 𝔍)
    (t B : ℝ) (ht : 𝔢) (hB : 𝔣) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : 𝔚)
    (hcenter : 𝔤) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔊)
    g :
    IsProbabilityMeasure 𝔛 := by
  have he := historyMarkedDensity_fiber_integral_one dependent (historyReferenceRho Δ) t π a ha hcenter g
  have hnonneg : ∀ marks, 0 ≤ 𝔟 := by
    intro marks
    have hb := 𝚉₂ _ t B
      (historyReferenceRho_pos Δ) ht hB a habound hsmall 𝔑
    exact (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1
  constructor
  unfold historyMarkedFiberPrior
  rw [𝚒₂, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one he) $ Filter.Eventually.of_forall hnonneg , he]
  simp

/-- The actual positive marked-history prior before source reference normalization. -/
def historyMarkedPriorRaw (dependent : 𝔅) (Δ : ℕ) (t : ℝ)
    [MeasurableSpace E] (π : Measure E) (a : 𝔓) : Measure 𝔔 :=
  Measure.sum fun g => ENNReal.ofReal 𝘎₁ •
    Measure.map (Sigma.mk g) 𝔛

𝗇 𝔥 𝚊₂ Set.univ
/-- The path uses exactly the same time-independent source normalizer. -/
def historyMarkedPrior (dependent : 𝔅) (Δ : ℕ) (t : ℝ)
    [MeasurableSpace E] (π : Measure E) (a : 𝔓) : Measure 𝔔 :=
  𝔥⁻¹ • 𝔧 historyMarkedPriorRaw

𝗃 𝔨 ἀ dependent hrefl hsymm Δ hlabels t B ht hB π a ha hcenter habound hsmall
theorem historyMarkedPriorRaw_univ (dependent : 𝔅)
    (hrefl : 𝔒) (hsymm : 𝔉)
    (Δ : ℕ) (hlabels : 𝔍)
    (t B : ℝ) (ht : 𝔢) (hB : 𝔣) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : 𝔚)
    (hcenter : 𝔤) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔊) :
    𝔧 historyMarkedPriorRaw Set.univ = 𝔥 := by
  rw [historyMarkedReferenceRaw_univ]
  unfold historyMarkedPriorRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1
  funext g
  let :=
    𝔨 historyMarkedFiberPrior_probability g
  simp

/-- The source path of positive prior measures is genuinely constructed for the whole interval. -/
theorem historyMarkedPrior_probability (dependent : 𝔅)
    (hrefl : 𝔒) (hsymm : 𝔉)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔍)
    (t B : ℝ) (ht : 𝔢) (hB : 𝔣) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : 𝔚)
    (hcenter : 𝔤) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔊) :
    IsProbabilityMeasure 𝔧 historyMarkedPrior := by
  let :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  constructor
  unfold historyMarkedPrior
  rw [Measure.smul_apply, 𝔨 historyMarkedPriorRaw_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt $ lt_of_lt_of_le zero_lt_one $ historyMarkedReferenceRaw_univ_one_le dependent Δ π ) 𝚃₁
