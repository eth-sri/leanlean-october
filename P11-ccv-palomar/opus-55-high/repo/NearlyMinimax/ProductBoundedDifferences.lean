module

public import NearlyMinimax.OscillationMGF
public import NearlyMinimax.HistoryCanonicalDeletion
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Genuine finite-product bounded differences
-/

𝛅
𝚨

variable {E : Type*} [MeasurableSpace E] [Nonempty E]

omit [Nonempty E] in
/-- The finite independent insertion is exactly the ordinary last-coordinate tuple recursion. -/
theorem finiteMarkAppend_eq_snoc (n : ℕ) (fresh : E) (marks : 𝗚₁) :
    historyFiniteMarkAppendEquiv n 𝘨₂ = Fin.snoc marks fresh := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [historyFiniteMarkAppendEquiv_last, Fin.snoc_last]
  · rw [historyFiniteMarkAppendEquiv_old, Fin.snoc_castSucc]

𝗇 𝔊 ∀ i, IsProbabilityMeasure $ π i
𝗇 𝔍 Measure.pi fun i : Fin n => π i.castSucc
𝗇 𝔒 historyFiniteMarkAppendEquiv n (E := E)
omit [Nonempty E] in
/-- Independent last-coordinate insertion preserves the genuine product law, allowing nonidentical laws. -/
theorem finiteMarkAppend_preserving_varying (n : ℕ) (π : Fin 𝗉 → Measure E)
    [𝔊] :
    MeasurePreserving 𝔒
      ((π $ Fin.last n ).prod 𝔍) $ Measure.pi π := by
  simpa only [historyFiniteMarkAppendEquiv, Fin.succAbove_last_apply] using
    (measurePreserving_piFinSuccAbove π $ Fin.last n ).symm _

𝗇 𝔄 Real.exp $ 𝙟₁ * 𝗆₂ / 8
𝗇 𝔔 u * X e
𝗇 𝔘 ∫ f, X f ∂π
𝗃 𝔠 u * ἀ
/-- The uncentered one-coordinate exponential bound follows from the proved oscillation lemma. -/
theorem exp_integral_le_of_oscillation (π : Measure E) [IsProbabilityMeasure π]
    X (hX : Measurable X) R c (hc : 𝗂₁)
    (hbound : ∀ e, |X e| ≤ R) (hosc : ∀ e f, |X e - X f| ≤ c) u :
     ∫ e, Real.exp 𝔔 ∂π ≤
      Real.exp (u * ∫ e, X e ∂π) * 𝔄 := by
  have hh := centered_mgf_le_of_oscillation π X hX R c hc hbound hosc u
  have hf : (fun e => Real.exp 𝔔) =
       fun e => Real.exp 𝔠 𝔘 * Real.exp (u * (X e - 𝔘)) := by
    funext e
    rw [← Real.exp_add]
    ring
  rw [hf, integral_const_mul]
  bound

𝗇 𝔅 Real.exp $ n * 𝙟₁ * 𝗆₂ / 8
𝗇 𝔇 𝘮₂
𝗇 𝔈 Real.exp $ u * G x
𝗇 𝔉 Function.update x i y
𝗇 𝔎 Real.exp $ u * F x
𝗇 𝔐 ∫ x, F x ∂Measure.pi π
𝗇 𝔑 fun y => H 𝔇
𝗇 𝔓 hbound $ e 𝔇
𝗇 𝔖 u * H p
𝗇 𝔙 hbound $ e p
𝗇 𝔚 hH.comp $ measurable_id.prodMk measurable_const
𝗇 𝔛 Fin.snoc x z
𝗇 𝔜 ∫ x, G x ∂μ
𝗃 𝔡 H (z, ἀ)
𝗃 𝔢 Integrable.of_bound (Real.measurable_exp.comp $ measurable_const.mul ἀ ).aestronglyMeasurable
/-- True McDiarmid moment bound for an arbitrary bounded measurable function of finite independent blocks.
Only the actual coordinate oscillation is an input; the concentration inequality is proved. -/
theorem product_exp_integral_le (n : ℕ) (π : Fin n → Measure E)
    [𝔊]
    F (hF : Measurable F) R c (hc : 𝗂₁)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ i x y, |F 𝔉 - F x| ≤ c) u :
     ∫ x, 𝔎 ∂Measure.pi π ≤
      Real.exp 𝔠 𝔐 * 𝔅 := by
  induction n with
  | zero =>
    let empty : Fin 0 → E := Fin.elim0
    have hf : F = fun _ => F empty := by funext x; congr 1; exact Subsingleton.elim ..
    rw [hf]
    simp
  | succ n ih =>
    let ν := π $ Fin.last n
    let μ := 𝔍
    let e := 𝔒
    have hp := finiteMarkAppend_preserving_varying n π
    let H := fun p => F $ e p
    have hH := hF.comp e.measurable
    have hHi : Integrable H $ ν.prod μ := Integrable.of_bound hH.aestronglyMeasurable R
      $ Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using 𝔙
    let G := fun x => ∫ y, H 𝔇 ∂ν
    have hG : Measurable G := hH.stronglyMeasurable.integral_prod_left'.measurable
    have hXi : ∀ x, Integrable 𝔑 ν := by
      intro x
      apply Integrable.of_bound (𝔚).aestronglyMeasurable R
      exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, Function.comp_apply, Prod.map_apply, id_eq, H] using 𝔓
    have hGb : ∀ x, |G x| ≤ R := by
      intro x
      simpa [G, Real.norm_eq_abs] using
        norm_integral_le_of_norm_le_const (μ := ν) (f := 𝔑)
          $ Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, H] using 𝔓
    have hGo : ∀ i x y, |G 𝔉 - G x| ≤ c := by
      intro i x y
      rw [← integral_sub (hXi _) $ hXi _ ]
      have hb : ∀ᵐ z ∂ν, ‖𝔡 𝔉 - 𝔡 x‖ ≤ c := by
        apply Eventually.of_forall
        intro z
        simpa only [H, e, finiteMarkAppend_eq_snoc, Fin.snoc_update, Real.norm_eq_abs] using
          hosc i.castSucc 𝔛 y
      simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb
    have hXo : ∀ x y z, |H 𝔇 - 𝔡 x| ≤ c := by
      intro x y z
      simpa only [H, e, finiteMarkAppend_eq_snoc, Fin.update_snoc_last] using
        hosc (Fin.last n) 𝔛 y
    have hpoint : ∀ x, ∫ y, Real.exp (u * H 𝔇) ∂ν ≤
        𝔈 * 𝔄 := by
      intro x
      exact exp_integral_le_of_oscillation ν 𝔑
        𝔚 R c hc
        (fun y => 𝔓) (hXo x) u
    have hmean : 𝔐 = 𝔜 := by
      rw [← hp.integral_comp' F, integral_prod_symm H hHi]
    have hEi : Integrable (fun p => Real.exp 𝔖) $ ν.prod μ := by
      apply 𝔢 hH
        $ Real.exp $ |u| * R
      apply Eventually.of_forall
      intro p
      change ‖Real.exp 𝔖‖ ≤ _
      rw [Real.norm_eq_abs, 𝚖]
      apply Real.exp_le_exp.2
      exact 𝚕₁ $ by rw [abs_mul]; exact mul_le_mul_of_nonneg_left 𝔙 $ abs_nonneg u
    have hEGi : Integrable (fun x => 𝔈) μ := by
      apply 𝔢 hG
        $ Real.exp $ |u| * R
      apply Eventually.of_forall
      intro x
      change ‖𝔈‖ ≤ _
      rw [Real.norm_eq_abs, 𝚖]
      apply Real.exp_le_exp.2
      exact 𝚕₁ $ by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb x) $ abs_nonneg u
    rw [← hp.integral_comp' fun x => 𝔎 , integral_prod_symm _ hEi, hmean]
    calc
      _ ≤ ∫ x, 𝔈 * 𝔄 ∂μ :=
        integral_mono hEi.integral_prod_right (hEGi.mul_const _) hpoint
      _ = (∫ x, 𝔈 ∂μ) * 𝔄 := integral_mul_const ..
      _ ≤ Real.exp 𝔠 𝔜 * 𝔅 *
          𝔄 :=
        mul_le_mul_of_nonneg_right (ih (fun i => π i.castSucc) G hG hGb hGo) 𝙫
      𝘿 := by
        rw [mul_assoc, ← Real.exp_add]
        push_cast
        ring

𝗇 𝔏 Real.exp $ -u * m
𝗇 𝔗 ∫ y, F y ∂Measure.pi π
𝗇 𝔞 𝔠 m
𝗃 𝔟 u * (F x - ἀ)
/-- Centering gives the exact source exponent N c² u²/8. -/
theorem product_centered_mgf_le (n : ℕ) (π : Fin n → Measure E)
    [𝔊]
    F (hF : Measurable F) R c (hc : 𝗂₁)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ i x y, |F 𝔉 - F x| ≤ c) u :
     ∫ x, Real.exp 𝔟 𝔗 ∂Measure.pi π ≤
      𝔅 := by
  let m := 𝔗
  have hf : (fun x => Real.exp 𝔟 m) =
       fun x => 𝔏 * 𝔎 := by
    funext x
    rw [← Real.exp_add]
    ring
  rw [hf, integral_const_mul]
  have hprod : 𝔏 * Real.exp 𝔞 = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ ≤ 𝔏 *
        (Real.exp 𝔞 * 𝔅) :=
      mul_le_mul_of_nonneg_left (product_exp_integral_le n π F hF R c hc hbound hosc u) 𝙫
    𝘿 := 𝖤₃
