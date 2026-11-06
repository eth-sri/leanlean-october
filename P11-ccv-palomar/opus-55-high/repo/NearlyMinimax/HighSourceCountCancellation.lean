module

public import NearlyMinimax.HighSourceRawDecomposition
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Count-zero, count-one and count-two identities for the complete
source, including every selected higher-target coarse/fine row. -/
𝚫
𝚨
𝚩
𝚭
𝚬

𝗇 𝔈 𝙮 → ℝ
𝗇 𝔓 𝙔
𝗃 𝔗 ἀ d D M q ad bd C lam ℓ N μ
𝗃 𝔙 ἀ ad bd lam ℓ
def higherBandFamilyFirstAction (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : 𝙇) (p : 𝔓)
    (c : 𝔈) (Φ : 𝔈 → ℝ) : ℝ :=
  ∑ i : 𝔗 HigherBandFamilyIndex,
    𝔙 higherBandFirstAction 𝙽
      (higherBandFamilyTarget i.val) 𝚁 D q C i.val.2 U p c Φ

𝗇 𝔇 𝖳
𝗃 𝔏 𝔙 ἀ N μ D M q C
𝗇 𝔍 𝔏 higherBandFamilyFirstAction U p c Φ
𝗇 𝔐 𝖼
𝗇 𝔑 𝖽
𝗇 𝔔 𝗮
theorem higherBandFamilyFirstAction_zero_small_count
    ad bd lam ℓ N μ (ha : 𝔐) (hab : 𝔑)
    D M q (hD : 𝔔) (hnD : 𝖠₁) (hn : n ≤ 2) C
    U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p : 𝔓) (hp : 𝔇)
    (c : 𝔈) Φ :
    𝔍 = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hr := (𝔗 higherBandFamily_target_bounds i).1
  exact 𝔙 higherBandFirstAction_zero_small_count _ ha hab i.property.1
    _ _ D q  𝖡₃  hD hnD  𝖡₃  C i.val.2 U hU p hp c Φ

𝗇 𝔒 singletonFirstAction ad bd D q C p c
theorem completeSourceSignedFirstAction_eq_family
    ad bd lam ℓ N μ D M q C
    U (p : 𝔓)
    (c : 𝔈) Φ :
    𝔏 completeSourceSignedFirstAction U p c Φ =
      finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
        𝔒 Φ +
        𝔍 := rfl

𝗇 𝔄 𝔏 completeSourceRawNumerator a V η U p g w c y
𝗇 𝔉 𝔙 higherBandFamilyFirstAction_zero_small_count N μ ha hab D M q
𝗇 𝔊 fun i => Fin.elim0 i
𝗃 𝔘 ἀ ad bd ha hab D q
𝗇 𝔖 𝔘 singletonFirstAction_zero_other_count
theorem completeSourceRawNumerator_count_zero [NeZero d]
    ad bd lam ℓ N μ (ha : 𝔐) (hab : 𝔑)
    D M q (hD : 𝔔) C a V η
    U (p g w : Fin 0 → ℝ)
    (c : 𝔈) y :
    𝔄 = 0 := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    finePairThreeRowFirstAction_small_count  𝖡₃  ad bd ℓ N ha hab D M q hD C U p
      𝔊 c,
    𝔖 hD  𝖡₃   𝖡₃ 
      C p 𝔊 c,
    𝔉 hD
       𝖡₃   𝖡₃  C U 𝔊 p 𝔊 c]
  simp

𝗇 𝔅 𝙬
theorem singletonFirstAction_response_heat
    ad bd (ha : 𝔐) (hab : 𝔑) D q (hD : 𝔔) (hq : 𝗘)
    C a V η (hC : 𝚆) (U : Fin 1 → Covariate d) (p g w : Fin 1 → ℝ)
    (hp : 𝔇) c y :
    𝔒
      (fun v => 𝖨 𝔅 v y) =
      𝙎 * 𝗊 * ∑ i, 𝖩 *
        𝖷 𝔅 c y i := by
  rw [𝔘 singletonFirstAction_count_one hD C p hp c]
  have he := high_response_matrix_heat q hq C a V η (finePairUnitMatrix d D) hC
    (finePairUnitMatrix_symmetric d D) g w 𝔅 c y
    𝙃 $ by
      intro i l
      have hil : 𝚛₁ := Subsingleton.elim ..
      simp only [finePairUnitMatrix_kernel, hil, ite_true]
  grind

theorem completeSourceRawNumerator_count_one [NeZero d]
    ad bd lam ℓ N μ (ha : 𝔐) (hab : 𝔑)
    D M q (hD : 𝔔) (hq : 𝗘) C a V η (hC : 𝚆)
    U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p g w : Fin 1 → ℝ) (hp : 𝔇)
    (c : 𝔈) y :
    𝔄 = 0 := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    finePairThreeRowFirstAction_small_count  𝖡₃  ad bd ℓ N ha hab D M q hD C U p hp c,
    𝔉 hD
      hD  𝖡₃  C U hU p hp c,
    𝔘 singletonFirstAction_response_heat hD hq C a V η hC U p g w hp c y]
  ring

𝗇 𝔎 N * 𝙹
theorem completeSourceRawNumerator_count_two [NeZero d]
    ad bd lam ℓ N μ (ha : 𝔐) (hab : 𝔑) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    D M q (hD : 𝗕) (hM : 𝗜₁) (hq : 𝖯₂)
    C a V η (hC : 𝚆) U
    (hU : ∀ i j, |𝗒₂| ≤ 2) (hQ : 𝖾₁)
    (p g w : 𝖷₂) (hp : 𝔇)
    c y :
    𝔄 =
      𝙎 * w 0 * w 1 * p 0 * p 1 *
        ((1 + 𝔎) *
          Real.exp (-𝔎)) *
        ternaryMeanDerivative a (𝗡 𝔅 c 0) (y 0) *
        ternaryMeanDerivative a (𝗡 𝔅 c 1) (y 1) := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    𝔖  𝖡₃   𝖡₃   𝖡₃ 
      C p hp c,
    𝔉  𝖡₃ 
       𝖡₃   𝖡₃  C U hU p hp c]
  simp only [add_zero, Fin.prod_univ_two]
  exact finePairThreeRow_count_two_numerator hD ad bd ℓ N ha hab hℓ hℓN D M q
     𝖡₃  hM hq C a V η hC U hQ p hp g w c y
