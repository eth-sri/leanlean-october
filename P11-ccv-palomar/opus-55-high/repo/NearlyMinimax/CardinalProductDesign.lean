module

public import NearlyMinimax.CardinalBandL2
public import NearlyMinimax.CardinalIntegratedContinuity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine head splitting of finite product designs. -/
𝚫
𝚪
𝚨
𝚩
𝚽

𝗇 𝔇 Covariate d × 𝗖₁
𝗇 𝔈 𝙇
𝗃 𝔍 ἀ i z.1 z.2
def cardinalHeadSplit (i : Fin n) :
    𝔈 ≃ᵐ 𝔇 where
  toFun U := (U i, fun j => U j.val)
  invFun z := 𝔍 anchoredPatchConfiguration
  left_inv U := by
    funext j
    change (if h : 𝖰₁ then U j else U i) = U j
    split_ifs with h
    · rfl
    · exact congrArg U (not_ne_iff.mp h).symm
  right_inv z := by
    apply Prod.ext
    · exact 𝔍 anchored_configuration_same
    · funext j
      exact 𝔍 anchored_configuration_other j
  measurable_toFun := (measurable_pi_apply i).prodMk
    $ Measurable.of_eval fun j => measurable_pi_apply j.val
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    change Measurable fun z : 𝔇 =>
      if h : 𝖰₁ then z.2 𝗷₂ else z.1
    split_ifs <;> fun_prop

𝗇 𝔄 𝘫
𝗇 𝔅 {j : Fin n // j = i}
𝗇 𝔊 fun j => j = i
theorem cardinalHeadSplit_measurePreserving (i : Fin n)
    (μ : 𝘹₁) [SigmaFinite μ] :
    MeasurePreserving (cardinalHeadSplit i) (Measure.pi 𝔄)
      $ μ.prod $ Measure.pi 𝔄 := by
  letI : Unique 𝔅 :=
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd 𝔄 𝔊
  have heq : @Measure.pi 𝔅 (fun _ => Covariate d)
      (Subtype.fintype 𝔊) (fun _ => inferInstance) 𝔄 =
      Measure.pi 𝔄 := by
    congr 1
    exact Subsingleton.elim ..
  rw [heq] at hs
  have hh := (measurePreserving_funUnique μ 𝔅).prod
    $ MeasurePreserving.id $ Measure.pi fun _ : SpatialScaleIndex i => μ
  exact hh.comp hs

𝗇 𝔉 𝖪
def fullSpatialPatchDesign (d n : ℕ) : Measure 𝔈 :=
  Measure.pi fun _ : Fin n => 𝔉

instance fullSpatialPatchDesign_finite (d n : ℕ) : IsFiniteMeasure 𝖮₁ := by
  unfold fullSpatialPatchDesign
  infer_instance

theorem fullSpatialPatchDesign_split i
    (f : 𝔈 → ℝ) :
     ∫ U, f U ∂𝖮₁ =
      ∫ z : 𝔇,
        f 𝔍 anchoredPatchConfiguration
        ∂(𝔉).prod 𝘓₁ := (((cardinalHeadSplit_measurePreserving i 𝔉).symm).integral_comp' f).symm
