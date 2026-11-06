module

public import NearlyMinimax.HighSourceHigherGeometry
public import NearlyMinimax.HighCompleteSourceMarkedTail
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! A deterministic measurable integrable full-count spatial envelope for
complete source scores, including empty/singleton cancellation, the genuine
pair defect, matched higher counts, and the exterior-degree crude bound. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

 set_option hygiene false
𝗇 𝔅 n+3
𝗇 𝔇 bD-𝖧⁻¹
𝗇 𝔈 (Bl+1)^2
𝗇 𝔉 𝚎₁^𝔅*𝗸*𝔈
𝗇 𝔊 𝙇
def completeSourceGeometryEnvelope (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) : (n : ℕ) → 𝔊 → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, U => finePairCountTwoGeometryEnvelope 𝔇 a rho eta N U
  | 𝔅, U => if 𝔅 ≤ D then
      𝘭
    else 𝔉

 set_option hygiene false
𝗇 𝔄 𝚀₂ Bl
theorem completeSourceGeometryEnvelope_nonneg D M R q
    aD bD c0 ell N mu C a rho eta Chi Bl n (U : 𝔊) :
    0 ≤ 𝔄 n U := by
  rcases n with _|_|_|n
  · rfl
  · rfl
  · exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U
  · try simp only [completeSourceGeometryEnvelope]
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_nonneg ..
    · positivity

 theorem completeSourceGeometryEnvelope_integrable [NeZero d] (hd : 𝘚)
    D M R q aD bD c0 ell N mu C a rho eta Chi Bl
    (hell : 𝗲₁) (hN : ell ≤ N) n :
    Integrable (𝔄 n)
      𝖮₁ := by
  rcases n with _|_|_|n
  · simp
  · exact integrable_zero ..
  · exact (finePairCountTwoGeometryEnvelope_integrable_and_le  𝖡₃  _ _ _ _
      $ lt_of_lt_of_le zero_lt_one $ hell.trans hN ).1
  · change Integrable (fun U => if 𝔅 ≤ D then
      completeSourceHigherGeometryEnvelope aD bD c0 ell N mu M R q C a rho eta U
      else 𝔉) $ fullSpatialPatchDesign d 𝔅
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_integrable hd  𝖡₃  _ _ _ _ _ _ _ _ _ _ _ _ _ hell hN
    fun_prop

 theorem completeSourceGeometryEnvelope_pair_integral_le D M R q
    aD bD c0 ell N mu C a rho eta Chi Bl (hd : 𝗆) (hN : 𝘹) :
     ∫ U, 𝔄 2 U
      ∂𝗿₂ ≤ 9*finePairCountTwoSpatialBudget d 𝔇 a rho eta N :=
    (finePairCountTwoGeometryEnvelope_integrable_and_le hd _ _ _ _ hN).2

 theorem completeSourceGeometryEnvelope_exterior_integral D M R q n
    aD bD c0 ell N mu C a rho eta Chi Bl (hn : D < 𝔅) :
     ∫ U, 𝔄 𝔅 U
      ∂fullSpatialPatchDesign d 𝔅 =
      (3*𝖥*Chi^2)^𝔅*𝗸*𝔈 := by
  simp only [completeSourceGeometryEnvelope, if_neg $ not_le.mpr hn , integral_const,
    fullSpatialPatchDesign_real_univ]
  ring

 theorem fineFieldGeometryEnvelope_count_three ad bd T0 N
    M q C a rho eta (U : Fin 3 → Covariate d) :
    fineFieldGeometryEnvelope ad bd T0 N M q C a rho eta U = 0 := by
  have hs : ((Finset.univ : Finset $ Fin 3 ).powerset).filter
      (fun S => 4 ≤ S.card ∧ Even S.card) = ∅ := by
    rfl
  unfold fineFieldGeometryEnvelope
  grind
