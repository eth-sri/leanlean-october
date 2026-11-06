module

public import NearlyMinimax.HighMarkedDesignFactorial
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Borel complete-generator numerator arrays from the primitive genuine
mark law and legal Borel density/coefficient resets. This applies to the
entire source row union, with its one common heat correction. -/
𝚯
𝚪
𝚨
𝚩
set_option maxHeartbeats 900000

section
𝛣

𝗇 𝔅 𝘜₁
theorem highMarkedResponseMass_measurable a V η (g w : 𝘬)
    (hg : Measurable g) (hw : Measurable w) φ
    (hφ : 𝔅) (c : 𝙛) y :
    Measurable fun x => highMarkedResponseMass a V η g w φ c x y := by
  apply ternaryMass_measurable_comp
  fun_prop

𝗇 𝔄 E × (Fin r → α)
𝗇 𝔇 g ∘ x
𝗇 𝔈 w ∘ x
𝗇 𝔉 φ ∘ x
𝗃 𝔊 ἀ ∘ z.2
theorem highMarkedSampleNumerator_measurable (r : ℕ) (π : Measure E) [SFinite π]
    activation (hAct : Measurable activation) a V η
    p (hp : Measurable p) pReset
    (hpReset : Measurable $ Function.uncurry pReset ) cReset
    (hcReset : 𝘝₁)
    (g w : 𝘬) (hg : Measurable g) (hw : Measurable w)
    φ (hφ : 𝔅)
    (c : 𝙛) y :
    Measurable fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y := by
  have hReset i : Measurable fun z : 𝔄 => pReset z.1 $ z.2 i :=
    hpReset.comp $ measurable_fst.prodMk $ 𝘜 measurable_snd
  have hreg i : Measurable fun z : 𝔄 =>
      coefficientRegression η 𝔊 g 𝔊 w 𝔊 φ (cReset z.1) i := by
    unfold coefficientRegression
    fun_prop
  have hMarked : Measurable fun z : 𝔄 =>
      activation z.1 * (∏ i, pReset z.1 (z.2 i)) *
        highResponseProduct a V η 𝔊 g 𝔊 w 𝔊 φ (cReset z.1) y :=
    ((hAct.comp measurable_fst).mul $ Finset.measurable_prod _ fun i _ => hReset i ).mul $ Finset.measurable_prod _ fun i _ => ternaryMass_measurable_comp a V _ (hreg i) $ y i
  have hAction : Measurable fun x =>
      highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset
        𝔇 𝔈 𝔉 y :=
    hMarked.stronglyMeasurable.integral_prod_left'.measurable
  have hq i : Measurable fun x =>
      ternaryMass a (coefficientRegression η 𝔇 𝔈 𝔉 c i) V $ y i :=
    (𝗉₂ c $ y i ).comp $ measurable_pi_apply i
  have hvar i : Measurable fun x =>
      highResponseVarianceTerm a V η 𝔇 𝔈 𝔉 c y i := by
    unfold highResponseVarianceTerm
    fun_prop
  exact hAction.sub $ (measurable_const.mul
    $ Finset.measurable_prod _ fun i _ => hp.comp $ measurable_pi_apply i ).mul
      $ Finset.measurable_sum _ fun i _ =>
        ((hw.comp $ measurable_pi_apply i ).pow_const 2).mul $ hvar i
