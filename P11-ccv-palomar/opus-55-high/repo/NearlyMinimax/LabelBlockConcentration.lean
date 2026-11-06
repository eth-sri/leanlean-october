module

public import NearlyMinimax.LabelBlockMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Genuine label-block concentration for actual finite history marks
-/

𝛅
𝚨

variable {J E : Type*} [Fintype J] [MeasurableSpace E] [Nonempty E]

𝗇 𝔅 fun i => π $ f i
𝗇 𝔐 ∫ y, F y ∂Measure.pi π
𝗇 𝔇 u * (F x - 𝔐)
𝗇 𝔈 Fintype.card J * 𝙟₁ * 𝗆₂ / 8
𝗇 𝔉 Function.update x i y
𝗃 𝔑 fun _ => ἀ
/-- The genuine bounded-differences bound is independent of the chosen finite enumeration. -/
theorem fintype_product_centered_mgf_le [DecidableEq J] (π : J → Measure E)
    [∀ j, IsProbabilityMeasure $ π j ]
    F (hF : Measurable F) R c (hc : 𝗂₁)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ j x y, |F (Function.update x j y) - F x| ≤ c) u :
     ∫ x, Real.exp 𝔇 ∂Measure.pi π ≤
      Real.exp 𝔈 := by
  classical
  let f := (Fintype.equivFin J).symm
  let e := MeasurableEquiv.piCongrLeft 𝔑 E f
  have hp :=
    measurePreserving_piCongrLeft π f
  have he : ∀ x i y,
      e 𝔉 = Function.update (e x) (f i) y := by
    intro x i y
    funext j
    obtain ⟨k, rfl⟩ := f.surjective j
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    by_cases hk : k = i
    · subst k
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne fun h => hk $ f.injective h ]
      exact (MeasurableEquiv.piCongrLeft_apply_apply f (β := 𝔑 E) x k).symm
  let G := F ∘ e
  have hGo : ∀ i x y, |G 𝔉 - G x| ≤ c := by
    grind
  have hh := product_centered_mgf_le (Fintype.card J) 𝔅 G
    (hF.comp e.measurable) R c hc (fun x => hbound $ e x ) hGo u
  have hm : ∫ x, G x ∂Measure.pi 𝔅 = ∫ x, F x ∂Measure.pi π :=
    hp.integral_comp' F
  rw [hm] at hh
  change ∫ x, Real.exp (u * (F (e x) - 𝔐))
    ∂Measure.pi 𝔅 ≤ _ at hh
  rw [hp.integral_comp' fun x => Real.exp 𝔇 ] at hh
  exact hh

𝗇 𝔄 Real.exp $ u * (F marks - ∫ marks', F marks' ∂ν)
𝗇 𝔊 𝔑 π
𝗇 𝔍 Function.update blocks j new
𝗇 𝔎 labelBlockReconstruct labels blocks
𝗇 𝔏 ∫ marks, F marks ∂ν
/-- Actual independent occurrence marks concentrate in the number of labels, not occurrences.
Replacing all occurrences of one label is the only oscillation hypothesis. -/
theorem label_block_centered_mgf_le [Fintype I] [DecidableEq J]
    (labels : I → J) (π : Measure E) [IsProbabilityMeasure π]
    F (hF : Measurable F) R c (hc : 𝗂₁)
    (hbound : ∀ marks, |F marks| ≤ R)
    (hosc : ∀ j marks marks', (∀ i, labels i ≠ j → 𝘢₂) → |F marks - F marks'| ≤ c)
    u :
     ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂Measure.pi 𝔊))
      ∂Measure.pi 𝔊 ≤ Real.exp 𝔈 := by
  let ν := Measure.pi fun _ : I => π
  let μ := Measure.pi fun _ : J => ν
  let G := F ∘ labelBlockReconstruct labels
  have hp := labelBlockReconstruct_preserving labels π
  have ho : ∀ j blocks new, |G 𝔍 - G blocks| ≤ c := by
    intro j blocks new
    apply hosc j (labelBlockReconstruct labels 𝔍) 𝔎
    intro i hi
    exact labelBlockReconstruct_update_other labels blocks j new i hi
  have hh := fintype_product_centered_mgf_le 𝔑 ν G (hF.comp $ labelBlockReconstruct_measurable labels ) R c hc
    (fun blocks => hbound 𝔎) ho u
  have hm : ∫ blocks, G blocks ∂μ = 𝔏 := (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
      $ congrArg (fun m => ∫ marks, F marks ∂m) hp.map_eq
  rw [hm] at hh
  have hi : ∫ blocks, Real.exp (u * (G blocks - 𝔏)) ∂μ =
      ∫ marks, 𝔄 ∂ν := by
    have hmeas : Measurable fun marks => 𝔄 :=
      Real.measurable_exp.comp $ measurable_const.mul $ hF.sub measurable_const
    exact (integral_map hp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm.trans
      $ congrArg (fun m => ∫ marks, 𝔄 ∂m) hp.map_eq
  rw [hi] at hh
  exact hh
