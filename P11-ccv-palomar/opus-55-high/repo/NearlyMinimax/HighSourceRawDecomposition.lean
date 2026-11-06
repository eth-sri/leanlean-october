module

public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.FinePairAllCounts
public import NearlyMinimax.HighCardinalScores
public import NearlyMinimax.CardinalGlobalBandL2
public import NearlyMinimax.SpatialSubsetIntegral
public import NearlyMinimax.FinePairUnionMassAnnihilation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact count decomposition of the actual complete source packets.
The statements below evaluate genuine signed integrals; no local action
identity or count cancellation is supplied as a hypothesis. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 1400000
𝚬

𝗃 𝕮 ἀ d r lam fine ζ l $ U i
𝗇 𝔄 𝕮 higherBandCarrierFactor
𝗇 𝔅 𝙮 → ℝ
𝗇 𝔊 𝙔
𝗇 𝔑 𝙇
𝗇 𝔩 fun i l => 𝔄
𝗃 𝔭 ἀ ad bd
𝗇 𝔧 ∏ i, 𝔭 localDensityReset r z eps p 𝔩 i
𝗇 𝔫 fun ζ z eps => 𝔧
𝗇 𝔲 𝔅 → ℝ
𝗃 𝕯 𝔭 ἀ m r
def higherBandFirstAction (ad bd lam L T : ℝ) (r m D q : ℕ)
    (C : ℝ) (fine : Bool) (U : 𝔑) (p : 𝔊)
    (c : 𝔅) (Φ : 𝔲) : ℝ :=
  ∫ᵛ e, 𝕯 highPacketObservable D q C c
    𝔫 Φ e
    ∂<•higherBandSignedRow d r m D q ad bd C lam L T fine

𝗇 𝔇 𝔭 higherBandFirstAction lam L T r m D q C fine U p c Φ
𝗇 𝔈 ∀ i, p i ∈ 𝔭 Icc
𝗇 𝔒 higherBandCarrierMeasure d r L T fine
𝗇 𝔔 𝖼
𝗇 𝔖 𝖽
𝗇 𝔗 𝕮 higherBandCarrierFactor_bound $ hU i
𝗇 𝔙 (higherBandCarrierFactor_joint_measurable d r lam fine l).comp $ measurable_id.prodMk measurable_const
𝗇 𝔚 𝚜₁
𝗇 𝔛 𝙬₁
𝗇 𝔠 𝖹
𝗇 𝔡 𝗒₂
𝗇 𝔥 higherBandCarrierAmplitude d r D lam fine
𝗇 𝔦 higherBandCarrierAmplitude_measurable d r D lam fine
𝗃 𝔮 ἀ q C c Φ
𝗇 𝔱 fun ζ => 𝔄
𝗇 𝔳 𝘗
𝗇 𝔴 𝖿₂
𝗇 𝔵 pow_nonneg 𝔛 n
theorem higherBandFirstAction_eq_packet
    ad bd lam L T (ha : 𝔔) (hab : 𝔖) (hT : 𝔠)
    r m D q (hr : 𝔳) C fine
    U (hU : ∀ i j, |𝔡| ≤ 2)
    (p : 𝔊) (hp : 𝔈)
    c Φ :
    𝔇 =
      highSeparatedPacketAction 𝔒
        ad bd m r D q C 𝔥 c
        𝔫 Φ := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  have hm i l :
      Measurable 𝔱 :=
    𝔙
  have hG z eps : Measurable
       fun ζ => 𝔧 := by
    unfold localDensityReset
    fun_prop
  have hb ζ e
      i : |𝔭 localDensityReset r
        (𝕯 densityPacketAtom D e).1 (𝕯 densityPacketAtom D e).2 p
        𝔩 i| ≤ bd := by
    have he := 𝔭 densityPacketAtom_mem hab.le m r D e
    have hh := 𝔭 localDensityReset_mem_interval ha hab r hr _ he.1 _ he.2 p
      𝔩 i (hp i)
       fun l => 𝔗
    grind
  exact highPacketSignedMeasure_factor_integral _ ad bd m r D q C _
    𝔦
    𝔚
    c _ hG 𝔴 𝔵
    (fun ζ e => finite_density_product_abs_bound _ bd 𝔛 $ hb ζ e )
    Φ 𝔮 finePairResponseAtomBound 𝔮 finePairResponseAtomBound_le

𝗇 𝔢 𝗮
𝗇 𝔣 ∏ i ∈ S, p i
𝗇 𝔯 𝖠₁
𝗃 𝕬 𝔭 ἀ lam L T ha hab hT r m D q
𝗃 𝕰 fun ζ i l => ἀ
theorem higherBandFirstAction_count_expansion
    ad bd lam L T (ha : 𝔔) (hab : 𝔖) (hT : 𝔠)
    r m D q (hr : 𝔳) (hD : 𝔢) (hnD : 𝔯)
    C fine U (hU : ∀ i j, |𝔡| ≤ 2)
    (p : 𝔊) (hp : 𝔈)
    c Φ :
    𝔇 =
      𝕯 densityCountCoefficient n *
        ∑ S ∈ Finset.univ.powersetCard r, 𝔣 *
          𝗔
            (separatedSubsetMatrix 𝔒 r
              𝕰 𝔄
              𝔥 S) c Φ := by
  rw [𝕬 higherBandFirstAction_eq_packet hr C fine U hU p hp c Φ]
  have hm i l :
      Measurable 𝔱 :=
    𝔙
  simpa only [Finset.card_univ, Fintype.card_fin] using
    highSeparatedPacketAction_row 𝔒 ad bd ha hab
      m r D q hr hD Finset.univ (by simpa using hnD) p _ hm
      𝕰 𝔗 C _
      𝔦
      𝔚 c Φ

𝗇 𝔪 𝕬 higherBandFirstAction_count_expansion
𝗇 𝔎 𝔪 hr hD hnD C fine U hU p hp c Φ
𝗇 𝔤 (Finset.univ : 𝙍).powersetCard r
theorem higherBandFirstAction_zero_small_count
    ad bd lam L T (ha : 𝔔) (hab : 𝔖) (hT : 𝔠)
    r m D q (hr : 𝔳) (hD : 𝔢) (hnD : 𝔯) (hnr : n < r)
    C fine U (hU : ∀ i j, |𝔡| ≤ 2)
    (p : 𝔊) (hp : 𝔈)
    (c : 𝔅) Φ :
    𝔇 = 0 := by
  rw [𝔎]
  have he : 𝔤 = ∅ :=
    Finset.powersetCard_eq_empty.mpr $ by simpa using hnr
  grind

theorem higherBandFirstAction_zero_other_count
    ad bd lam L T (ha : 𝔔) (hab : 𝔖) (hT : 𝔠)
    r m D q (hr : 𝔳) (hD : 𝔢) (hnD : 𝔯)
    (hnm : n ≤ m) (hne : n ≠ r) C fine
    U (hU : ∀ i j, |𝔡| ≤ 2)
    (p : 𝔊) (hp : 𝔈)
    (c : 𝔅) Φ :
    𝔇 = 0 := by
  by_cases hnr : n < r
  · exact 𝕬 higherBandFirstAction_zero_small_count hr hD hnD
      hnr C fine U hU p hp c Φ
  rw [𝔎,
    𝔭 densityCountCoefficient_exact ha hab m r n hr  𝖡₃  hnm, if_neg hne, zero_mul]

𝗃 𝕭 densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam ἀ l $ U i ) S
𝗇 𝔓 𝕭 z
𝗇 𝔷 𝖹₂
theorem cardinal_density_subset_sym_eq lam
    (S : 𝙍) (z : CardinalSeparatedMark d S.card)
    U :
    𝔓 =
      cardinalSeparatedSymmetricFactor lam z 𝔷 := by
  let e :=
    ((Fintype.equivFin S).trans $ finCongr $ Fintype.card_coe S ).symm
  rw [densitySeparatedSym_eq_permutation_average S.card _ S e]
  congr 1
  apply Fintype.sum_equiv $ Equiv.inv $ Equiv.Perm $ Fin S.card
  intro τ
  have h := Equiv.prod_comp τ
     fun l => cardinalSeparatedFactor lam z l $ U (e $ τ.symm l ).val
  aesop

def higherBandActualMatrix (lam L T : ℝ) (fine : Bool)
    (U : 𝔑) : 𝙮 → 𝔅 :=
  if fine then globalCardinalBandMatrix lam L T U else 𝖯₁

𝗇 𝔜 higherBandActualMatrix lam L T fine 𝔷
theorem higherBand_subset_matrix_actual (lam : ℝ) (hlam : 𝖺)
    (L T : ℝ) (hL : 0 < L) (hT : 𝔠) (fine : Bool)
    S (hS : 2 ≤ S.card) (U : 𝔑)
    (hU : ∀ i j, |𝔡| ≤ 2) :
    separatedSubsetMatrix (higherBandCarrierMeasure d S.card L T fine) S.card
      (fun ζ i l => higherBandCarrierFactor d S.card lam fine ζ l $ U i )
      (higherBandCarrierAmplitude d S.card D lam fine) S =
      𝔜 := by
  have hb : ∀ l j, |𝔷 l j| ≤ 2 := fun l => hU _
  funext β β'
  cases fine
  · change ∫ z, 𝔓 *
        cardinalSeparatedAmplitude lam z β β' ∂cardinalSeparatedMeasure d S.card T = _
    simp_rw [cardinal_density_subset_sym_eq]
    exact (integrated_cardinal_symmetric_separated_exact lam hlam hT _ hb β β').symm
  · change ∫ z, 𝕭 z.2 *
        cardinalBandAmplitude lam z β β' ∂cardinalBandMeasure d S.card L T = _
    simp_rw [cardinal_density_subset_sym_eq]
    exact (integrated_cardinal_actual_band_separated_exact hS lam hlam hL hT _ hb β β').symm

theorem higherBandFirstAction_actual_count_expansion
    (ad bd lam L T : ℝ) (ha : 𝔔) (hab : 𝔖) (hlam : 𝖺)
    (hL : 0 < L) (hT : 𝔠) (r m D q : ℕ) (hr : 𝘠₁) (hD : 𝔢) (hnD : 𝔯)
    (C : ℝ) (fine : Bool) U (hU : ∀ i j, |𝔡| ≤ 2)
    (p : 𝔊) (hp : 𝔈)
    (c : 𝔅) Φ :
    𝔇 =
      𝕯 densityCountCoefficient n *
        ∑ S ∈ 𝔤, 𝔣 *
          𝗔
            𝔜 c Φ := by
  rw [𝔪  𝖡₃ 
    hD hnD C fine U hU p hp c Φ]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have he := (Finset.mem_powersetCard.mp hS).2
  have hh := higherBand_subset_matrix_actual (D := D) lam hlam L T hL hT fine S
     𝖡₃  U hU
  aesop

𝗇 𝔉 𝘞
𝗇 𝔏 𝗻
𝗇 𝔘 𝖶₁
𝗇 𝔨 ∏ i, 𝔭 localDensityReset 1 z eps p 𝔉 i
𝗇 𝔬 fun _ z eps => 𝔨
𝗃 𝕱 ἀ 𝔘 ad bd D 1 D q C 𝔏
def singletonFirstAction (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : 𝔊) (c : 𝔅)
    (Φ : 𝔲) : ℝ :=
  ∫ᵛ e, 𝔭 highPacketObservable D 1 D q C c
    𝔬 Φ e
    ∂<•𝕱 highPacketSignedMeasure

𝗇 𝔍 𝔭 singletonFirstAction D q C p c Φ
𝗇 𝔐 𝗱
set_option maxHeartbeats 120000 in
theorem singletonFirstAction_eq_packet
    (ad bd : ℝ) (ha : 𝔔) (hab : 𝔖) (D q : ℕ) (C : ℝ)
    (p : 𝔊) (hp : 𝔈)
    (c : 𝔅) (Φ : 𝔲) :
    𝔍 =
      𝕱 highSeparatedPacketAction c
        𝔬 Φ := by
  unfold singletonFirstAction
  have hb (e : HighDensityMarkIndex D 1 D) (i : Fin n) :
      |𝔭 localDensityReset 1 (𝔭 densityPacketAtom D 1 D e).1
        (𝔭 densityPacketAtom D 1 D e).2 p 𝔉 i| ≤ bd := by
    have he := 𝔭 densityPacketAtom_mem hab.le D 1 D e
    have hh := 𝔭 localDensityReset_mem_interval ha hab 1  𝖠₄  _ he.1 _ he.2 p
      𝔉 i (hp i) $ by intro _; norm_num
    rw [abs_of_nonneg $ ha.le.trans hh.1 ]
    exact hh.2
  exact highPacketSignedMeasure_factor_integral (Z := Unit) (ι := 𝙮)
    𝔘 ad bd D 1 D q C
    𝔏 𝔐 (integrable_const _)
    c (fun (_ : Unit) z eps => 𝔨)
    𝔐 𝔴 𝔵
    (fun _ e => finite_density_product_abs_bound _ bd 𝔛 $ hb e )
    Φ 𝔮 finePairResponseAtomBound 𝔮 finePairResponseAtomBound_le

𝗇 𝔞 𝔭 singletonFirstAction_eq_packet ha hab D q C p hp c Φ
𝗃 𝕲 ἀ Finset.univ ad bd ha hab D 1 D
theorem singletonFirstAction_zero_other_count
    ad bd (ha : 𝔔) (hab : 𝔖) D q (hD : 𝔢)
    (hnD : 𝔯) (hne : n ≠ 1) C
    (p : 𝔊) (hp : 𝔈)
    (c : 𝔅) Φ :
    𝔍 = 0 := by
  rw [𝔞]
  by_cases hn : n = 0
  · subst n
    unfold highSeparatedPacketAction
    simp_rw [densityPacketAction_mul_right,
      𝕲 density_packet_product_zero_of_small_count  𝖠₄  hD  𝖢₄   𝖢₄  p 𝔉, zero_mul]
    simp
  have hh := highSeparatedPacketAction_count_selector 𝔘 ad bd ha hab D 1 D q
     𝖠₄  hD Finset.univ (by simpa using hnD)
    (by simpa using hnD) (by simpa using 𝖡₃ ) p
    (fun _ => 𝔉) 𝔐
     𝖢₄  C 𝔏
    𝔐 (integrable_const _) c Φ
  simp_all

theorem densitySeparatedSym_one [DecidableEq α] r
    (S : Finset α) (hS : S.card = r) : densitySeparatedSym r (fun _ _ => 1 ) S = 1 := by
  let e :=
    ((Fintype.equivFin S).trans $ finCongr $ (Fintype.card_coe S).trans hS ).symm
  rw [densitySeparatedSym_eq_permutation_average r _ S e]
  simp only [Finset.prod_const_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  field_simp

𝗇 𝔰 𝗊
𝗇 𝔶 (Finset.univ : Finset $ Fin 1 )
theorem singletonFirstAction_count_one
    ad bd (ha : 𝔔) (hab : 𝔖) D q (hD : 𝔢) C
    (p : Fin 1 → ℝ) (hp : 𝔈)
    c Φ :
    𝔍 =
      𝔰 * 𝗔 (finePairUnitMatrix d D) c Φ := by
  rw [𝔞]
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right]
  have hh := 𝕲 density_packet_product_count_selector  𝖠₄  hD (by simpa using hD)
    (by simpa using hD) p 𝔉
  have hpow : (𝔶).powersetCard 1 = {Finset.univ} := by
    rfl
  simp only [hpow, Finset.sum_singleton,
    densitySeparatedSym_one 1 𝔶 𝖢₄ ] at hh
  simp_all

def completeSourceSignedFirstAction (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : 𝔑) (p : 𝔊)
    (c : 𝔅) (Φ : 𝔲) : ℝ :=
  𝔭 finePairThreeRowFirstAction ℓ N D M q C U p c Φ +
    𝔍 +
    ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
      𝔭 higherBandFirstAction lam ℓ 𝙽
        (higherBandFamilyTarget i.val) 𝚁 D q C i.val.2 U p c Φ

𝗇 𝔟 𝙬
/-- The raw complete-source numerator subtracts the global variance
derivative once, after adding every genuine row first action. -/
def completeSourceRawNumerator (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C a V η : ℝ) (U : 𝔑) (p g w : 𝔊)
    (c : 𝔅) (y : 𝙈) : ℝ :=
  𝔭 completeSourceSignedFirstAction lam ℓ N μ D M q C U p c
    (fun v => 𝖨 𝔟 v y) -
    𝙎 * 𝔰 * ∑ i, 𝖩 *
      𝖷 𝔟 c y i
