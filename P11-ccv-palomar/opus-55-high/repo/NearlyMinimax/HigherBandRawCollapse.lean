module

public import NearlyMinimax.HigherBandFamilyCollapse
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact finite-target reindexing and full-response ordinary-fine-alias
identification for the genuine selected higher family. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 1400000
𝚬

𝗇 𝔅 𝙳
𝗇 𝔈 Fin 𝘐
𝗇 𝔉 𝗊₁
𝗇 𝔟 fun r => r<n
𝗇 𝔎 𝔟
𝗃 𝔢 higherBandTargetScale d ἀ N mu
𝗇 𝔐 𝔢 𝔅
𝗇 𝔔 𝔅 < n
𝗇 𝔞 ell < 𝔐
𝗇 𝔗 if 𝔔 then if 𝔞 then A 𝔅 else 0 else 0
theorem higherBand_alias_index_sum_eq d D n ell N mu (A : 𝙜) :
     ∑ j : 𝔈, 𝔗 =
      ∑ r ∈ (𝔉).filter 𝔎, A r := by
  classical
  have hi (j : 𝔈) :
      𝔗 =
      if 𝔔 ∧ 𝔞 then A 𝔅 else 0 := by
    grind
  simp_rw [hi]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij fun j _ => 𝔅
  · intro j hj
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      grind
    · exact ((Finset.mem_filter.mp hj).2).1
  · omega
  · intro r hr
    have hI := Finset.mem_filter.mp (Finset.mem_filter.mp hr).1
    have hrd := Finset.mem_range.mp hI.1
    let j : 𝔈 := ⟨r-3, 𝖡₃⟩
    have hj : 𝔅 = r := 𝖤₃
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, 𝖤₄⟩, hj⟩
  · simp

𝗇 𝔄 fun v => highResponseProduct a V eta g w 𝙬 v y
𝗇 𝔠 𝔢 r
𝗇 𝔓 fun r => 𝔠
𝗇 𝔇 ordinaryFineAliasFamilyRawAction ((𝗊₁).filter 𝔟) ad bd lam ell 𝔓 M q C a V eta U p g w c y
𝗇 𝔊 𝖳
𝗇 𝔏 𝙔
𝗃 𝔘 ἀ ad bd lam ell
𝗇 𝔙 𝙮 → ℝ
𝗇 𝔛 𝖼
𝗇 𝔜 𝖽
theorem higherBandFine_below_eq_alias_family
    ad bd lam ell N mu (ha : 𝔛) (hab : 𝔜) (hlam : 𝖺) (hell : 𝗲₁)
    D M q (hD : 𝗮) (hnD : 𝖠₁) C a V eta
    U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p g w : 𝔏) (hp : 𝔊)
    (c : 𝔙) y :
    (∑ j : 𝔈, if 𝔔 then
      𝔘 higherBandFineFirstAction N mu 𝔅 M D q C U p c
        𝔄 else 0) =
      𝔇 := by
  unfold higherBandFineFirstAction
  have he : (∑ j : 𝔈, if 𝔔 then
       if 𝔞 then
        𝔘 higherBandFirstAction 𝔐 𝔅 M D q C true U p c
          𝔄 else 0 else 0) =
      ∑ j : 𝔈, if 𝔔 then
         if 𝔞 then
          𝔘 ordinaryFineAliasRawAction 𝔐
            M 𝔅 q C a V eta U p g w c y else 0 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hn ha'
    · exact 𝔘 higherBandFirstAction_fine_eq_aliasRawAction _ ha hab hlam  𝖡₄ 
        (hell.trans ha'.le) 𝔅 M D q  𝖡₃  hD hnD C a V eta U hU p g w hp c y
    all_goals rfl
  rw [he]
  exact higherBand_alias_index_sum_eq d D n ell N mu
     fun r => 𝔘 ordinaryFineAliasRawAction 𝔠 M r q C a V eta U p g w c y

𝗇 𝔍 integratedCardinalMatrix lam 𝔢 n U
𝗇 𝔑 𝔘 higherBandFamilyFirstAction N mu D M q C U p c 𝔄
𝗇 𝔒 𝗊 * 𝗔 𝔍 c 𝔄
𝗇 𝔖 ∀ j : 𝔈, 𝔞 → 𝔅 ≤ M
𝗇 𝔚 ∀ j : 𝔈, 0 < 𝔐
𝗃 𝔡 𝔘 ἀ N mu ha hab hlam hell D M q
theorem higherBandFamilyFirstAction_matched_and_alias_raw
    ad bd lam ell N mu (ha : 𝔛) (hab : 𝔜) (hlam : 𝖺) (hell : 𝗲₁)
    D M q (hn : 𝖬₂) (hnD : 𝖠₁)
    (hnu : 𝔚)
    (hFine : 𝔖)
    C a V eta U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p g w : 𝔏) (hp : 𝔊)
    (c : 𝔙) y :
    𝔑 =
      𝔒 +
      𝔇 := by
  rw [𝔡 higherBandFamilyFirstAction_matched_and_fine_below hn hnD hnu hFine C U hU p hp c,
    𝔡 higherBandFine_below_eq_alias_family  𝖡₃  hnD C a V eta U hU p g w hp c y]

theorem ordinaryFineAliasFamilyRawAction_below_eq_zero
    ad bd lam ell N mu (ha : 𝔛) (hab : 𝔜)
    D M q (hnM : n ≤ M) C a V eta
    U (p g w : 𝔏) (c : 𝖲)
    y :
    𝔇 = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  have hfilter := Finset.mem_filter.mp hr
  have htarget := Finset.mem_filter.mp hfilter.1
  have hnr := hfilter.2
  unfold ordinaryFineAliasRawAction
  rw [densityCountCoefficient_exact ad bd ha hab M r n  𝖡₃  hnr.le hnM, if_neg 𝖡₃ , zero_mul]

theorem ordinaryFineAliasTargetSet_below_eq d D n M ell N mu (hMn : M < n)
    (hFine : 𝔖) :
    (𝔉).filter 𝔎 = 𝔉 := by
  apply Finset.filter_eq_self.mpr
  intro r hr
  have htarget := Finset.mem_filter.mp hr
  have hrd := Finset.mem_range.mp htarget.1
  let j : 𝔈 := ⟨r-3, 𝖡₃⟩
  have hj : 𝔅 = r := 𝖤₃
  have hm := hFine j 𝖤₄
  omega

/-- Before M the ordinary fine aliases cancel exactly. Beyond M every
active fine target is strictly below the observed count, and its actual
signed action is precisely the full alias family used by the energy theorem. -/
theorem higherBandFamilyFirstAction_matched_and_full_fine_alias
    ad bd lam ell N mu (ha : 𝔛) (hab : 𝔜) (hlam : 𝖺) (hell : 𝗲₁)
    D M q (hn : 𝖬₂) (hnD : 𝖠₁)
    (hnu : 𝔚)
    (hFine : 𝔖)
    C a V eta U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p g w : 𝔏) (hp : 𝔊)
    (c : 𝔙) y :
    𝔑 =
      𝔒 +
       if M<n then ordinaryFineAliasFamilyRawAction 𝔉
        ad bd lam ell 𝔓 M q C a V eta U p g w c y else 0 := by
  rw [𝔡 higherBandFamilyFirstAction_matched_and_alias_raw hn hnD
    hnu hFine C a V eta U hU p g w hp c y]
  by_cases hnM : M<n
  · rw [ite_eq_left hnM, ordinaryFineAliasTargetSet_below_eq d D n M ell N mu hnM hFine]
  · rw [ite_eq_right hnM, 𝔘 ordinaryFineAliasFamilyRawAction_below_eq_zero N mu ha hab D M q
      (le_of_not_gt hnM) C a V eta U p g w c y]
