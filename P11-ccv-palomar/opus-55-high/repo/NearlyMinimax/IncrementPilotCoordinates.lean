module

public import NearlyMinimax.DyadicPilotPointwise
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! One fixed finite original-observation feature vector realizes every
anchor-dependent current/parent pilot input as a continuous linear image.
The deterministic root parent is realized by an explicit constant coordinate. -/

open MeasureTheory ProbabilityTheory Matrix
𝚼
𝚨
𝚭
𝚩

abbrev DyadicGlobalDimension (d ℓ j : ℕ) :=
  Fintype.card $ PilotBasisIndex (Fintype.card $ DyadicPilotLabelIndex d j ) d 𝗭₂

𝗇 𝔊 𝘮
𝗃 𝔦 ἀ d ℓ
𝗇 𝔎 Fin $ 𝔦 DyadicGlobalDimension j
𝗇 𝔛 𝔦 DyadicGlobalDimension 𝔊
abbrev IncrementGlobalIndex (d ℓ j : ℕ) :=
  Unit ⊕ 𝔎 ⊕ Fin 𝔛

𝗇 𝔅 𝔦 IncrementGlobalIndex j
𝗇 𝔜 pilotRawVector (ℓ := 𝗭₂)
𝗃 𝔧 Sum.inr $ ἀ i
def incrementGlobalFeature (j : ℕ) (a : 𝔅)
    (z : Observation d) : ℝ :=
  match a with
  | Sum.inl _ => 1
  | 𝔧 Sum.inl => 𝔜 (dyadicPilotLabel j) z i
  | 𝔧 Sum.inr => 𝔜 (dyadicPilotLabel 𝔊) z i

𝗇 𝔄 Fin (Fintype.card $ 𝔦 IncrementGlobalIndex j ) → ℝ
𝗇 𝔓 (Fintype.equivFin 𝔅).symm a
def incrementGlobalVector (j : ℕ) (z : Observation d) :
    𝔄 :=
  fun a => incrementGlobalFeature j 𝔓 z

𝗃 𝔗 ἀ (ℓ := ℓ) j
𝗇 𝔖 𝔗 incrementGlobalVector
𝗇 𝔔 𝔖
def incrementGlobalMean (θ : RegressionParameter d) (j : ℕ) :
    𝔄 :=
  fun a => ∫ z, 𝔔 z a ∂observationLaw θ

𝗇 𝔟 incrementGlobalFeature j a
theorem incrementGlobalFeature_measurable j
    (a : 𝔅) : Measurable 𝔟 := by
  cases a with
  | inl _ => exact measurable_const
  | inr a =>
    cases a <;> exact pilotBasisFeature_measurable _ (dyadicPilotLabel_measurable _) _

𝗃 𝔤 ἀ (d := d) (ℓ := ℓ) j
theorem incrementGlobalVector_measurable j :
    Measurable 𝔤 incrementGlobalVector :=
  measurable_pi_iff.mpr fun _ => incrementGlobalFeature_measurable j _

𝗇 𝔠 𝙱
theorem incrementGlobalFeature_memLp_two C
    θ (hθ : 𝙟) j
    (a : 𝔅) : MemLp 𝔟 2 $ observationLaw θ := by
  let := 𝔠
  cases a with
  | inl _ => exact memLp_const _
  | inr a =>
    cases a <;> exact pilotBasisFeature_memLp_two C θ hθ _ (dyadicPilotLabel_measurable _) _

𝗃 𝔘 fun i => ContinuousLinearMap.proj $ (Fintype.equivFin 𝔅) 𝔧 ἀ
𝗇 𝔡 𝔎 → ℝ
𝗃 𝔥 𝔄 →L[ℝ] ἀ
def incrementGlobalCurrent (j : ℕ) :
    𝔥 𝔡 :=
  ContinuousLinearMap.pi 𝔘 Sum.inl

def incrementGlobalParent (j : ℕ) :
    𝔄 →L[ℝ]
       Fin 𝔛 → ℝ :=
  ContinuousLinearMap.pi 𝔘 Sum.inr

𝗇 𝔑 𝔥 ℝ
def incrementGlobalOne (j : ℕ) :
    𝔑 :=
  ContinuousLinearMap.proj $ Fintype.equivFin 𝔅 $ Sum.inl ()

𝗇 𝔍 incrementGlobalVector j z
𝗇 𝔞 pilotRawVector (dyadicPilotLabel j) z
@[simp] theorem incrementGlobalCurrent_raw j (z : Observation d) :
    𝔗 incrementGlobalCurrent 𝔍 =
      𝔞 := by
  funext i
  simp [incrementGlobalCurrent, incrementGlobalVector, incrementGlobalFeature]

@[simp] theorem incrementGlobalParent_raw j (z : Observation d) :
    𝔗 incrementGlobalParent 𝔍 =
      pilotRawVector (dyadicPilotLabel 𝔊) z := by
  funext i
  simp [incrementGlobalParent, incrementGlobalVector, incrementGlobalFeature]

@[simp] theorem incrementGlobalOne_raw j (z : Observation d) :
    𝔗 incrementGlobalOne 𝔍 = 1 := by
  simp [incrementGlobalOne, incrementGlobalVector, incrementGlobalFeature]

𝗃 𝔣 ἀ j x
def preconditionedPilotCoordinate (j : ℕ) (x : Covariate d)
    (a : 𝔦 LocalPilotIndex) : 𝔡 →L[ℝ] ℝ :=
  ∑ β : 𝔦 AnchoredIndex, 𝗵₁ (localPilotRow a) β •
    𝔣 dyadicPilotCoordinate (localPilotReplaceRow a β)

@[simp] theorem preconditionedPilotCoordinate_raw j x
    (a : 𝔦 LocalPilotIndex) z :
    𝔣 preconditionedPilotCoordinate a 𝔞 =
      𝔣 preconditionedPilotFeature a z := by
  simp [preconditionedPilotCoordinate, preconditionedPilotFeature, dyadicPilotCoordinate_raw_apply]

𝗇 𝔈 incrementVariables 𝔦 anchoredDimension
𝗇 𝔉 𝘳₁
def incrementPilotFreeCoordinate (j : ℕ) (x : Covariate d)
    (a : 𝔈) :
    𝔑 :=
  match a with
  | Sum.inl $ Sum.inl it =>
    (𝔣 preconditionedPilotCoordinate $ Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2) ).comp
      $ incrementGlobalCurrent j
  | Sum.inl $ Sum.inr it =>
    if 𝘠 then if it.2.1 = it.2.2 then incrementGlobalOne j else 0 else
      (preconditionedPilotCoordinate 𝔊 x $ Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2) ).comp
        $ incrementGlobalParent j
  | Sum.inr pri =>
    if pri.1 && j == 0 then 0 else
      if pri.1 then
        (preconditionedPilotCoordinate 𝔊 x
          𝔉).comp $ incrementGlobalParent j
      else
        (𝔣 preconditionedPilotCoordinate
          𝔉).comp $ incrementGlobalCurrent j

𝗇 𝔒 Fin (Fintype.card 𝔈) → ℝ
def incrementPilotCoordinate (j : ℕ) (x : Covariate d) :
    𝔥 𝔒 :=
  ContinuousLinearMap.pi fun a => 𝔣 incrementPilotFreeCoordinate
    $ (Fintype.equivFin 𝔈).symm a

theorem incrementPilotFreeCoordinate_raw j x
    (a : 𝔈) z :
    𝔣 incrementPilotFreeCoordinate a 𝔍 = 𝔣 dyadicIncrementFeature a z := by
  cases a with
  | inl a =>
    cases a with
    | inl a =>
      simp [incrementPilotFreeCoordinate, dyadicIncrementFeature]
    | inr a =>
      by_cases hj : 𝘠
      · by_cases hit : a.2.1 = a.2.2 <;> simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hit]
      · simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    cases parent <;> cases response <;> by_cases hj : 𝘠
    all_goals simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]

@[simp] theorem incrementPilotCoordinate_raw j x
    (z : Observation d) :
    𝔣 incrementPilotCoordinate 𝔍 = 𝔗 dyadicIncrementRawVector x z := by
  funext a
  exact 𝔣 incrementPilotFreeCoordinate_raw _ z

𝗇 𝔢 𝚆₁
/-- Actual original-law population integration commutes with the exact
global-coordinate map. This is the common mean needed by field covariance. -/
theorem incrementPilotCoordinate_mean C
    θ (hθ : 𝙟) j (x : Covariate d) :
    𝔗 incrementPilotCoordinate x 𝔢 = dyadicIncrementRawMean θ j x := by
  let := 𝔠
  have hlp := KernelMomentBounds.vector_memLp_two 𝔔
    (incrementGlobalVector_measurable j) fun a => incrementGlobalFeature_memLp_two C θ hθ j _
  have hi := hlp.integrable 𝖠₄
  have hm : ∫ z, 𝔔 z ∂observationLaw θ = 𝔢 := by
    funext a
    exact ((ContinuousLinearMap.proj a :
      𝔑).integral_comp_comm hi).symm
  rw [← hm, ← (𝔣 incrementPilotCoordinate).integral_comp_comm hi]
  funext a
  simpa only [ContinuousLinearMap.proj_apply, incrementPilotCoordinate_raw,
    dyadicIncrementRawMean] using ((ContinuousLinearMap.proj a :
    𝔒 →L[ℝ] ℝ).integral_comp_comm
    $ (𝔣 incrementPilotCoordinate).integrable_comp hi ).symm

𝗇 𝔇 𝗷
𝗇 𝔏 𝔖 (z i) a
𝗇 𝔐 𝔖 $ z i
𝗇 𝔙 𝙌
𝗇 𝔚 fun z => z i
theorem incrementGlobalVector_sample_facts C
    (θ : RegressionParameter d) (hθ : 𝙟) j :
    iIndepFun (fun i (z : 𝔙) => 𝔐) 𝔇 ∧
    (∀ i , Measurable fun z : 𝔙 => 𝔐 ) ∧
    (∀ i t , IdentDistrib
      (fun z => 𝗤₁)
      (fun z => 𝔔 $ z t ) 𝔇 𝔇) ∧
    (∀ i a, MemLp (fun z => 𝔏)
      2 𝔇) ∧
     ∀ i a, ∫ z : 𝔙, 𝔏 ∂𝔇 =
      𝔢 a := by
  let := 𝔠
  have hm := 𝔤 incrementGlobalVector_measurable
  have hp i : MeasurePreserving 𝔚
      𝔇 $ observationLaw θ := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi fun _ => hm.aemeasurable ,
    𝘋₂, ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib 𝔚
        (fun z => z t) 𝔇 𝔇 :=
      𝘏₁
    exact ht.comp hm
  · intro i a
    exact (incrementGlobalFeature_memLp_two C θ hθ j _).comp_measurePreserving $ hp i
  · intro i a
    exact integral_comp_eval
       (incrementGlobalFeature_measurable j
        𝔓).aestronglyMeasurable
