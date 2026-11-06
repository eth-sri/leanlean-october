module

public import NearlyMinimax.FinePairUnionMassAnnihilation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Response-coordinate elimination for arbitrary finite complete-row
unions. The structural assumptions concern the uncentered primitive row
packet and its density-mark projection, and are discharged by actual
finite response rules in the concrete source family. -/
𝚸
𝚪
𝚨
𝚩
𝚭
𝚬

𝗃 𝔓 ἀ d k
𝗇 𝔄 historyMarkedAppend (fun i j => j ∈ 𝔓 highNeighborLabels i) (fun {_ _} h => 𝔓 highNeighborLabels_symmetric _ _ h) j
𝗇 𝔊 project i e
𝗇 𝔅 lift i 𝔊
𝗇 𝔐 𝗋₁
𝗇 𝔇 ∫ e, R.rowActivation i e * Fobs 𝔐 ∂ R.rowLaw i
𝗇 𝔈 S.indicator fun _ => 𝙠
𝗃 𝔒 highUnionSourceMass C R $ 𝔄 (h,ἀ)
𝗇 𝔉 𝔒 e
𝗇 𝔍 (highUnionSourceState C R _).1 x
𝗃 𝔔 ἀ R $ highCenterMix C
𝗇 𝔎 𝔔 highUnionActivation e
𝗇 𝔏 R.rowSlope j i
𝗃 𝔑 ∫ e, R.rowActivation i e * ἀ 𝔊 ∂ R.rowLaw i
/-- Response-independent raw densities and actual uncentered response
cancellation imply canonical-history mass indicator cancellation for any
finite tagged row union. -/
theorem highUnionSourceMass_append_indicator_zero_of_density_projection
    [NeZero k] [LinearOrder 𝔓 HighWindowLabels]
    [Fintype I] [𝙪]
    [𝖭] (C : ModelConstants d)
    (R : 𝔓 HighUnionRowData F I E) (G : 𝗗)
    (hpos : 𝚣)
    (D : 𝗀) [∀ i, MeasurableSpace $ D i ]
    (project : (i : I) → E i → D i) (lift : (i : I) → D i → E i)
    (hlift : ∀ i, Measurable $ lift i )
    (hSlope : ∀ j i e x, 𝔏 e x = 𝔏 𝔅 x)
    (hIntercept : ∀ i e, 𝘅₂ = R.rowIntercept i 𝔅)
    (hRowZero : ∀ i, ∀ H : D i → ℝ, Measurable H → ∀ L : ℝ,
      (∀ z, ‖H z‖ ≤ L) → 𝔑 H = 0)
    (j : 𝔓 HighWindowLabels)
    h
    (S : Set ℝ) (hS : MeasurableSet S) :
     ∫ e, S.indicator (fun _ : ℝ => 𝙠)
      𝔉 *
      𝔎 ∂𝔔 highUnionLaw = 0 := by
  letI : 𝗄₁ := highUnionMark_standardBorel
  let Fobs := fun e => 𝔈
    𝔉
  have hF : Measurable Fobs := (measurable_const.indicator hS).comp
    $ (highUnionSourceMass_measurable C R G).comp
      $ (historyMarkedAppend_measurable _ _ j).comp $ measurable_const.prodMk measurable_id
  have hFbound e : ‖Fobs e‖ ≤ 1 :=
    (norm_indicator_le_norm_self 𝙃 _).trans_eq 𝖢₄
  have hmass (i : I) (e : E i) :
      𝔒 𝔐 =
      highUnionSourceMass C R (𝔄
          (h,Sum.inl ⟨i,𝔅⟩)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    change 𝔍 = 𝔍
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if x ∈ 𝔓 highTorusPatch j then 𝔏 e x * _ + 𝘅₂ else _) =
       if x ∈ 𝔓 highTorusPatch j then 𝔏 𝔅 x * _ +
        R.rowIntercept i 𝔅 else _
    rw [hSlope j i e x,hIntercept i e]
  have hrow (i : I) : 𝔇 = 0 := by
    let Hi := fun z => Fobs $ Sum.inl ⟨i,lift i z⟩
    have hHi := hF.comp
      𝙳₂
    have hf (e : E i) :=
      congrArg 𝔈 $ hmass i e
    calc
      _ = 𝔑 Hi :=
        integral_congr_ae $ Filter.Eventually.of_forall fun e => congrArg _ $ hf e
      _ = 0 := hRowZero i Hi hHi 1 fun z => hFbound _
  calc
    _ = ∫ e, 𝔎 * Fobs e ∂𝔔 highUnionLaw :=
      integral_congr_ae $ Filter.Eventually.of_forall fun e => mul_comm ..
    _ = ∑ i, 𝔇 :=
      highUnionSource_bounded_action C R G hpos Fobs hF 1 hFbound
    _ = 0 := by simp only [hrow,Finset.sum_const_zero]
