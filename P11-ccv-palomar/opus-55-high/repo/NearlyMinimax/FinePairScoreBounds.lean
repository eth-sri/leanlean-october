module

public import NearlyMinimax.FinePairHyperplanePacket
public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.SpatialLaplaceTail
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact count-two action of the genuine three source fine-pair rows.
The density selectors and the Lebesgue/field carrier are evaluated before
the single response variance correction is applied. -/
𝚫
𝚨

𝗇 𝔎 fun i _ => ψ i
𝗇 𝔜 𝖷₂
theorem densitySeparatedSym_identical_columns (ψ : 𝔜) :
    densitySeparatedSym 2 𝔎 Finset.univ = ψ 0 * ψ 1 := by
  classical
  let e :=
    (Equiv.subtypeUnivEquiv fun i : Fin 2 => Finset.mem_univ i ).symm
  rw [densitySeparatedSym_eq_permutation_average 2 _ Finset.univ e]
  simp only [e]
  simp [Fintype.card_perm]

𝗇 𝔅 p 0 * p 1
𝗇 𝔫 𝙆
𝗇 𝔬 𝙭
𝗇 𝔭 2 ≤ D
𝗃 𝕯 ἀ a b
𝗃 𝖅 𝕯 ἀ m 2 D
𝗇 𝔵 𝖅 densityPacketAction fun z eps => ∏ i, 𝕯 localDensityReset 2 z eps p 𝔎 i
theorem ordinaryPairDensity_action a b (ha : 𝔫) (hab : 𝔬)
    m D (hm : 2 ≤ m) (hD : 𝔭) (p ψ : 𝔜) :
    𝔵 =
      𝔅 * ψ 0 * ψ 1 := by
  have hh := density_packet_product_count_selector Finset.univ
    a b ha hab m 2 D  𝖡₃   𝖡₃  (by simpa using hD)
    (by simpa using hm) p 𝔎
  have hpow : (Finset.univ : Finset $ Fin 2 ).powersetCard 2 = {Finset.univ} := by
    rfl
  simpa only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton,
    Fin.prod_univ_two, densitySeparatedSym_identical_columns, mul_assoc] using hh

𝗇 𝔓 𝙔
𝗇 𝕷 n < 2
section

variable (hn : 𝕷)

include hn

theorem ordinaryPairDensity_action_small_count a b (ha : 𝔫) (hab : 𝔬) m D (hD : 𝗮)
    p (ψ : 𝔓) :
    𝔵 = 0 := density_packet_product_zero_of_small_count Finset.univ a b ha hab m 2 D
     𝖡₃  hD (by simpa using 𝖡₃ ) (by simpa using hn) p _

theorem finePairDensity_action_small_count a b M (p ψ : 𝔓) :
     ∫ᵛ e, ∏ i, 𝕯 finePairDensityReset e.1 e.2 p ψ i
      ∂<•𝕯 finePairDensitySignedRule M = 0 := by
  rcases show n = 0 ∨ n = 1 by omega with rfl | rfl
  · simpa only [Finset.univ_eq_empty, Finset.prod_empty] using
      𝕯 finePairDensitySignedRule_mass_zero M
  · simpa only [Fin.prod_univ_one] using
      𝕯 finePairDensitySignedRule_linear_zero M p ψ 0

end

𝗇 𝔟 finePairTimeFieldValue e u * finePairTimeFieldValue e v
𝗇 𝔥 𝗔 A c Φ
𝗇 𝔦 𝙛
𝗇 𝔶 𝗔
theorem finePairTime_response_integral [Fintype ι] [DecidableEq ι]
    (d : ℕ) [NeZero d] lo hi (hlo : 0 ≤ lo)
    u v (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d)
    q C A (c : 𝔦) Φ :
     ∫ e, 𝔟 *
      𝔶 (finePairTimeMatrix d A e) c Φ
      ∂finePairTimeFieldMeasure d lo hi =
      (∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm 𝖤₂)) *
        𝔥 := by
  change ∫ e, 𝔟 *
    𝔶 (fun i j => e.1 * 𝘩) c Φ
    ∂finePairTimeFieldMeasure d lo hi = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he e : 𝔟 *
      (e.1 * 𝔥) =
       e.1 * 𝔟 *
        𝔥 := 𝖢₃
  simp_rw [he]
  rw [integral_mul_const, finePairTimeFieldValue_weighted_covariance d lo hi hlo u v hu hv]

𝗇 𝔮 T * Real.exp (-(T*r))
𝗇 𝕸 0 ≤ T0
𝗃 𝖂 ∫ T in Icc 0 T0, ἀ
𝗃 𝖃 ∫ T in Icc T0 N, ἀ
theorem pairLaplaceKernel_split (hT0 : 𝕸) (hN : 𝖽₂) r :
    𝖂 𝔮 +
      𝖃 𝔮 = pairLaplaceKernel N r := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT0, ← intervalIntegral.integral_of_le hN]
  exact intervalIntegral.integral_add_adjacent_intervals
    (by apply Continuous.intervalIntegrable; fun_prop)
    $ by apply Continuous.intervalIntegrable; fun_prop

𝗇 𝔘 finePairResponseAtomBound q C c Φ
𝗇 𝔠 finePairResponseAtomBound_le q C c Φ
𝗃 𝖆 fun _ _ => ἀ _
𝗃 𝖋 fun i _ => ἀ
section SignedPacket
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

𝗇 𝔏 Φ $ coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1
def finePairResponseAtomBound (q : ℕ) (C : ℝ) (c : 𝔦) (Φ : 𝔦 → ℝ) : ℝ :=
  ∑ h : 𝗧₂,
    |𝔏|

theorem finePairResponseAtomBound_le q C c Φ
    (h : 𝗧₂) :
    |𝔏| ≤
      𝔘 := Finset.single_le_sum
    (f := fun h =>
      |𝔏|)
    𝖆 abs_nonneg $ Finset.mem_univ h

𝗇 𝕽 ψ ζ i
𝗃 𝖄 Measurable fun ζ => ἀ
𝗇 𝔒 ∀ i, 𝖄 𝕽
𝗇 𝕬 𝕯 localDensityReset 2 z eps p 𝖋 𝕽 i
theorem ordinaryPairReset_measurable a b p
    (ψ : Z → 𝔓) (hψ : 𝔒)
    z eps i :
    𝖄 𝕬 := by
  unfold localDensityReset
  fun_prop

𝗇 𝔙 ∀ i, p i ∈ 𝕯 Icc
theorem ordinaryPairReset_atom_abs_le a b (ha : 𝔫) (hab : 𝔬)
    m D p (hp : 𝔙)
    (ψ : 𝔓) (hψ : ∀ i, |ψ i| ≤ 1)
    (e : HighDensityMarkIndex m 2 D) i :
    |𝕯 localDensityReset 2 (𝖅 densityPacketAtom e).1
      (𝖅 densityPacketAtom e).2 p 𝔎 i| ≤ b := by
  have hz := 𝕯 densityPacketAtom_mem hab.le m 2 D e
  have hh := 𝕯 localDensityReset_mem_interval ha hab 2  𝖡₃  _ hz.1 _ hz.2 p
    𝔎 i
    (hp i) fun _ => hψ i
  grind

𝗃 𝖁 fun ζ z eps => ∏ i, ἀ
𝗃 𝖇 ἀ σ a b m 2 D q C A
𝗇 𝔄 ∫ᵛ e, 𝖅 highPacketObservable q C c 𝖁 𝕬 Φ e ∂<•𝖇 highPacketSignedMeasure
𝗇 𝕾 𝙬₁
𝗇 𝔐 fun ζ e => finite_density_product_abs_bound _ b 𝕾 $ 𝕯 ordinaryPairReset_atom_abs_le ha hab m D p hp (ψ ζ) (hbψ ζ) e
𝗇 𝔖 𝙚
𝗇 𝔚 fun z eps => Finset.measurable_fun_prod _ fun i _ => 𝕯 ordinaryPairReset_measurable p ψ hmψ z eps i
𝗇 𝔢 ψ ζ 0 * ψ ζ 1 * 𝗔 (A ζ) c Φ
𝗇 𝔯 𝙧
𝗇 𝔷 𝖇 highPacketSignedMeasure_factor_integral hA hcost c _ 𝔚
theorem ordinaryPairPacket_pair_action (σ : Measure Z) [IsFiniteMeasure σ]
    a b (ha : 𝔫) (hab : 𝔬) m D q (hm : 2 ≤ m) (hD : 𝔭)
    C A (hA : 𝔖)
    (hcost : 𝔯) (c : 𝔦)
    p (hp : 𝔙) (ψ : Z → 𝔜)
    (hmψ : 𝔒) (hbψ : ∀ ζ i, |𝕽| ≤ 1)
    Φ :
    𝔄 =
      𝔅 * ∫ ζ, 𝔢 ∂σ := by
  rw [𝔷
    𝘺  𝖠₃ 
    𝔐
    Φ 𝔘 𝔠]
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, 𝕯 ordinaryPairDensity_action ha hab m D hm hD]
  have he ζ : 𝔅 * ψ ζ 0 * ψ ζ 1 * 𝔶 (A ζ) c Φ =
      𝔅 * 𝔢 := 𝖢₃
  simp_rw [he]
  exact integral_const_mul ..

𝗇 𝔰 pow_nonneg 𝕾 n
𝗇 𝕹 b^n
theorem ordinaryPairPacket_small_count (hn : 𝕷)
    (σ : Measure Z) [IsFiniteMeasure σ] a b (ha : 𝔫) (hab : 𝔬)
    m D q (hD : 𝗮) C
    A (hA : 𝔖)
    (hcost : 𝔯) (c : 𝔦)
    p (hp : 𝔙) (ψ : Z → 𝔓)
    (hmψ : 𝔒) (hbψ : ∀ ζ i, |𝕽| ≤ 1)
    Φ :
    𝔄 = 0 := by
  rw [𝔷
    𝕹 𝔰
    𝔐
    Φ 𝔘 𝔠]
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, ordinaryPairDensity_action_small_count hn a b ha hab m D hD,
    zero_mul]
  simp

𝗇 𝔱 𝕯 finePairDensityReset z eps p (ψ ζ) i
theorem finePairPacket_small_count (hn : 𝕷)
    (σ : Measure Z) [IsFiniteMeasure σ] a b (ha : 𝔫) (hab : 𝔬)
    M q C A
    (hA : 𝔖)
    (hcost : 𝔯) (c : 𝔦)
    p (hp : 𝔙) (ψ : Z → 𝔓)
    (hmψ : 𝔒) (hbψ : ∀ ζ i, |𝕽| ≤ 1)
    Φ :
     ∫ᵛ e, 𝕯 finePairPacketObservable M q C c
      𝖁 𝔱 Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A = 0 := by
  have hm z eps i :
      𝖄 𝔱 := by
    unfold finePairDensityReset
    fun_prop
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c _
    𝙺
    𝕹 𝔰 (fun ζ e => finite_density_product_abs_bound _ b 𝕾
      $ 𝕯 finePairFieldReset_abs_le ha hab M p hp ψ hbψ 𝘕₂ )
    Φ 𝔘 𝔠]
  simp_rw [finePairDensity_action_small_count hn a b M, zero_mul]
  simp

end SignedPacket

theorem responseMatrixAction_matrix_add [Fintype ι] [DecidableEq ι]
    q C A B (c : 𝔦) Φ :
    𝔶 (fun i j => 𝘩 + B i j) c Φ =
      𝔥 + 𝔶 B c Φ := by
  simp only [responseMatrixAction_entry_sum, add_mul, Finset.sum_add_distrib]

section ActualRows
variable {d F : ℕ} [NeZero d]

𝗇 𝔈 𝖲
𝗇 𝕿 finePairUnitMatrix d F
𝗇 𝔣 fun _ => 𝕿
𝗇 𝔧 𝘞
𝗇 𝔲 𝖶₁
𝗃 𝖀 ἀ ad bd
𝗇 𝕰 𝖀 highPacketObservable D 2 D q C c
𝗇 𝕺 𝔈 → ℝ
𝗇 𝕻 𝖀 localDensityReset 2 z eps p
def finePairUnitFirstAction (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : 𝔓) (c : 𝔈)
    (Φ : 𝕺) : ℝ :=
  ∫ᵛ e, 𝕰
    (fun _ z eps => ∏ i, 𝕻 𝔧 i) Φ e
    ∂<•highPacketSignedMeasure 𝔲 ad bd D 2 D q C 𝔣

𝗇 𝔨 𝖺₂
𝗇 𝕮 finePairTimeFieldValue ζ $ U i
𝗇 𝕱 𝙇
𝗇 𝕼 finePairTimeMatrix d 𝔨
def finePairCoarseFirstAction (ad bd T0 : ℝ) (D q : ℕ) (C : ℝ)
    (U : 𝕱) (p : 𝔓) (c : 𝔈)
    (Φ : 𝕺) : ℝ :=
  ∫ᵛ e, 𝕰
    (fun ζ z eps => ∏ i, 𝕻
      𝖋 𝕮 i) Φ e
    ∂<•highPacketSignedMeasure (finePairTimeFieldMeasure d 0 T0) ad bd D 2 D q C
      𝕼

def finePairFineFirstAction (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : 𝕱) (p : 𝔓) (c : 𝔈)
    (Φ : 𝕺) : ℝ :=
  ∫ᵛ e, 𝖀 finePairPacketObservable M q C c
    (fun ζ z eps => ∏ i, 𝖀 finePairDensityReset z eps p
      (fun i => 𝕮) i) Φ e
    ∂<•finePairPacketSignedMeasure (finePairTimeFieldMeasure d T0 N) ad bd M q C
      𝕼

𝗇 𝔛 𝖀 finePairFineFirstAction T0 N M q C U p c Φ
𝗇 𝔡 𝖀 finePairCoarseFirstAction T0 D q C U p c Φ
𝗇 𝔤 𝖀 finePairUnitFirstAction D q C p c Φ
def finePairThreeRowFirstAction (ad bd T0 N : ℝ) (D M q : ℕ) (C : ℝ)
    (U : 𝕱) (p : 𝔓) (c : 𝔈)
    (Φ : 𝕺) : ℝ :=
  𝔤 + 𝔡 +
    𝔛

𝗇 𝔍 ∀ i, p i ∈ 𝖀 Icc
𝗇 𝔳 𝖼
𝗇 𝔴 𝖽
𝗇 𝕲 𝗱
𝗇 𝕶 fun _ => measurable_const
theorem finePairUnitFirstAction_pair ad bd (ha : 𝔳) (hab : 𝔴)
    D q (hD : 𝔭) C (p : 𝔜) (hp : 𝔍)
    c Φ :
    𝔤 =
      𝔅 * 𝔶 𝕿 c Φ := by
  rw [finePairUnitFirstAction, ordinaryPairPacket_pair_action 𝔲 ad bd ha hab D D q hD hD C
    𝔣 𝕲
    (integrable_const _) c p hp 𝔧 𝕶 𝖢₄ ]
  simp

𝗇 𝔉 fun i => 𝖻₂
𝗇 𝔊 𝗀₁
𝗇 𝔑 fun ζ i => 𝕮
𝗇 𝔗 euclideanNorm fun r => U 0 r - U 1 r
𝗇 𝔞 𝖾₁
𝗇 𝔩 𝖼₂
𝗇 𝕳 T * Real.exp (-T * 𝔗)
𝗇 𝕴 finePairTimeMatrix_cost_integrable d 0 T0 _
theorem finePairCoarseFirstAction_pair ad bd T0 (ha : 𝔳) (hab : 𝔴)
    D q (hD : 𝔭) C U
    (hU : 𝔞) (p : 𝔜) (hp : 𝔍)
    c Φ :
    𝔡 = 𝔅 *
      (𝖂 𝕳 *
        𝔶 𝔨 c Φ) := by
  rw [finePairCoarseFirstAction, ordinaryPairPacket_pair_action _ ad bd ha hab D D q hD hD C
    _ 𝔩 𝕴
    c p hp 𝔑
    𝔉
    𝔊]
  rw [finePairTime_response_integral d 0 T0 (le_refl 0) (U 0) (U 1) (hU 0) $ hU 1 ]

𝗇 𝕵 finePairTimeMatrix_cost_integrable d T0 N _
theorem finePairFineFirstAction_pair ad bd T0 N (ha : 𝔳) (hab : 𝔴)
    (hT0 : 𝕸) M q (hM : 𝗜₁) C U
    (hU : 𝔞) (p : 𝔜) (hp : 𝔍)
    c Φ :
    𝔛 = 𝔅 *
      (𝖃 𝕳 *
        𝔶 𝔨 c Φ) := by
  unfold finePairFineFirstAction
  simp only [Fin.prod_univ_two]
  rw [finePairPacketSignedMeasure_pair_action _ ad bd ha hab M q hM C
    _ 𝔩 𝕵
    c p hp 𝔑
    𝔉
    𝔊 0 1
    Φ 𝔘 𝔠]
  rw [finePairTime_response_integral d T0 N hT0 (U 0) (U 1) (hU 0) $ hU 1 ]

𝗇 𝔇 𝙹
𝗇 𝕭 𝖀 finePairThreeRowFirstAction T0 N D M q C U p c
𝗇 𝔪 𝕭 Φ
theorem finePairThreeRowFirstAction_pair ad bd T0 N (ha : 𝔳) (hab : 𝔴)
    (hT0 : 𝕸) (hN : 𝖽₂) D M q (hD : 𝔭) (hM : 𝗜₁)
    C U (hU : 𝔞)
    (p : 𝔜) (hp : 𝔍) c
    Φ :
    𝔪 = 𝔅 *
      𝔶
        (finePairCombinedMatrix d F $ pairLaplaceKernel N 𝔇 ) c Φ := by
  rw [finePairThreeRowFirstAction, 𝖀 finePairUnitFirstAction_pair ha hab D q hD C p hp,
    𝖀 finePairCoarseFirstAction_pair T0 ha hab D q hD C U hU p hp,
    𝖀 finePairFineFirstAction_pair T0 N ha hab hT0 M q hM C U hU p hp]
  change _ = 𝔅 * 𝔶
    (fun i j => 𝕿 i j +
      pairLaplaceKernel N 𝔇 * 𝖺₂ i j) c Φ
  rw [responseMatrixAction_matrix_add, responseMatrixAction_scalar_matrix]
  rw [exactEuclideanDistance_eq_euclideanNorm]
  have hsplit := pairLaplaceKernel_split hT0 hN 𝔗
  grind

𝗇 𝔔 𝙬
theorem finePairThreeRow_count_two_numerator (hF : 3 ≤ F)
    ad bd T0 N (ha : 𝔳) (hab : 𝔴) (hT0 : 𝕸) (hN : 𝖽₂)
    D M q (hD : 𝔭) (hM : 𝗜₁) (hq : 𝖯₂)
    C a V η (hC : 𝚆)
    U (hU : 𝔞)
    p (hp : 𝔍) (g w : 𝔜)
    (c : 𝔈) y :
    𝕭
      (fun v => 𝖨 𝔔 v y) -
      𝙎 * 𝔅 * ∑ i, 𝖩 *
        𝖷 𝔔 c y i =
      𝙎 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * 𝔇) *
          Real.exp (-(N * 𝔇))) *
        ternaryMeanDerivative a (𝗡 𝔔 c 0) (y 0) *
        ternaryMeanDerivative a (𝗡 𝔔 c 1) (y 1) := by
  rw [𝖀 finePairThreeRowFirstAction_pair T0 N ha hab hT0 hN D M q hD hM C U hU p hp,
    finePairResponseCountTwo_numerator hF q hq C a V η _ hC U p g w c y]
  have hr : 0 ≤ 𝔇 := Real.sqrt_nonneg _
  have hsq : 𝔇^2 = 𝘘₂ :=
    Real.sq_sqrt $ Finset.sum_nonneg 𝖆 sq_nonneg
  rw [← hsq, mul_comm $ pairLaplaceKernel .. , pairLaplaceKernel_defect N _ hr]

theorem finePairThreeRowFirstAction_small_count (hn : 𝕷)
    ad bd T0 N (ha : 𝔳) (hab : 𝔴) D M q (hD : 𝗮)
    C U (p : 𝔓) (hp : 𝔍)
    (c : 𝔈) Φ :
    𝔪 = 0 := by
  have hunit : 𝔤 = 0 := ordinaryPairPacket_small_count hn 𝔲 ad bd ha hab D D q hD C
      𝔣 𝕲 (integrable_const _) c p hp
      𝔧 𝕶  𝖢₄  Φ
  have hcoarse : 𝔡 = 0 := ordinaryPairPacket_small_count hn _ ad bd ha hab D D q hD C _
      𝔩 𝕴 c p hp
      𝔑
      𝔉
      𝔊 Φ
  have hfine : 𝔛 = 0 := finePairPacket_small_count hn _ ad bd ha hab M q C _
      𝔩 𝕵 c p hp
      𝔑
      𝔉
      𝔊 Φ
  simp only [finePairThreeRowFirstAction, hunit, hcoarse, hfine, add_zero]
