module

public import NearlyMinimax.HighSourceRawDecomposition
public import NearlyMinimax.HigherBandOmissions
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual target-count evaluation and physical sum of the selected
higher signed rows. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

𝗇 𝔑 higherBandFamilyGuardDegree M i
𝗇 𝔒 higherBandFirstAction ad bd lam
𝗃 𝔖 higherBandFamilyUpper d ell N mu ἀ
𝗇 𝔄 𝔒 ell 𝔖 i (higherBandFamilyTarget i) 𝔑 D q C i.2 U p c Φ
𝗇 𝔅 Fin 𝘐
𝗇 𝔓 𝙮
𝗇 𝔇 𝔓 → ℝ
𝗇 𝔈 𝙇
𝗇 𝔎 𝙔
def higherBandPhysicalFirstAction (ad bd lam ell N mu : ℝ)
    (D M q : ℕ) (C : ℝ) (U : 𝔈) (p : 𝔎)
    (c : 𝔇) (Φ : 𝔇 → ℝ)
    (i : 𝔅 × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      𝔄 else 0
  else 𝔄

𝗇 𝔉 higherBandTargetScale d 𝙳 N mu
𝗃 𝔔 ἀ d D M q ad bd C lam ell N mu
theorem higherBandFamilyFirstAction_eq_physical ad bd lam ell N mu
    D M q C (hell : 𝗲₁)
    (hnu : ∀ j : 𝔅, 0 < 𝔉)
    (hFine : ∀ j : 𝔅, ell < 𝔉 → 𝙳 ≤ M)
    U (p : 𝔎)
    (c : 𝔇) Φ :
     ∑ i : 𝔔 HigherBandFamilyIndex,
      𝔒 ell 𝔖 i.val
        (higherBandFamilyTarget i.val) 𝚁 D q C i.val.2 U p c Φ =
      ∑ i : 𝔅 × Bool, higherBandPhysicalFirstAction ad bd lam ell N mu D M q C U p c Φ i := by
  let F := fun (i : 𝔅 × Bool)
      e =>
    highPacketObservable ad bd 𝔑 (higherBandFamilyTarget i) D q C c
      (fun ζ z eps => ∏ j, localDensityReset ad bd (higherBandFamilyTarget i) z eps p
        (fun j l => higherBandCarrierFactor d (higherBandFamilyTarget i) lam i.2 ζ l $ U j ) j) Φ e
  exact 𝔔 higherBandFamily_signedIntegral_sum_eq_physical hell hnu hFine F

𝗇 𝔏 integratedCardinalMatrix lam T
theorem integrated_cardinal_matrix_fin_cast (h : m = n) lam T
    U (β β' : 𝔓) :
    𝔏 (U ∘ finCongr h) β β' = 𝔏 U β β' := by
  subst n
  rfl

𝗇 𝔊 𝙍
𝗇 𝔐 spatialSubsetConfiguration Finset.univ U
theorem integrated_cardinal_matrix_full_subset lam T
    (U : 𝔈) (β β' : 𝔓) :
    𝔏 𝔐 β β' =
      𝔏 U β β' := by
  let S : 𝔊 := Finset.univ
  let h : S.card = n := 𝖨₄
  let e := (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm
  let v : S ≃ Fin n := ⟨Subtype.val, fun j => ⟨j, Finset.mem_univ j⟩ ,
     𝖤₃ , 𝖤₃ ⟩
  let τ := ((finCongr h).symm.trans e).trans v
  have hc : 𝖹₂ = (U ∘ τ) ∘ finCongr h := by
    rfl
  rw [hc, integrated_cardinal_matrix_fin_cast h]
  exact integrated_cardinal_matrix_perm τ lam T U β β'

𝗇 𝔍 higherBandActualMatrix lam L T fine
theorem higherBandActualMatrix_full_subset lam L T fine
    (U : 𝔈) :
    (𝔍 𝔐 : 𝔓 → _ → ℝ) =
      𝔍 U := by
  funext β β'
  cases fine <;> simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
    globalCardinalBandMatrix, integrated_cardinal_matrix_full_subset]

theorem higherBandFirstAction_target_count ad bd lam L T
    (ha : 𝖼) (hab : 𝖽) (hlam : 𝖺) (hL : 0 < L) (hT : 𝖹)
    m D q (hn : 𝗏) (hD : 𝗮) (hnD : 𝖠₁) (hnm : n ≤ m)
    C fine U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p : 𝔎) (hp : 𝖳)
    (c : 𝔇) Φ :
    𝔒 L T n m D q C fine U p c Φ =
      𝗊 * 𝗔 (𝔍 U) c Φ := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT n m D q hn hD hnD
    C fine U hU p hp c Φ]
  rw [densityCountCoefficient_exact ad bd ha hab m n n  𝖡₃  le_rfl hnm]
  have hS : (Finset.univ : 𝔊).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : 𝔊)
  simp only [ite_true, hS, Finset.sum_singleton, one_mul, higherBandActualMatrix_full_subset]
