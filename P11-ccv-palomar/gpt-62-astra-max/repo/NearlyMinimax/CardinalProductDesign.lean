module

public import NearlyMinimax.CardinalBandL2
public import NearlyMinimax.CardinalIntegratedContinuity


@[expose] public section

/-! Genuine head splitting of finite product designs. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {d n : ℕ} (i : Fin n)

def cardinalHeadSplit :
    (DesignSample d n) ≃ᵐ Covariate d × (SpatialScaleIndex i → Covariate d) where
  toFun U := (U i, fun j => U j.val)
  invFun z := anchoredPatchConfiguration z.1 z.2
  left_inv U := by
    funext j
    change (if h : j ≠ i then U j else U i) = U j
    split_ifs with h
    · rfl
    · exact congrArg U (not_ne_iff.mp h).symm
  right_inv z := by
    apply Prod.ext
    · exact anchored_configuration_same z.1 z.2
    · funext j
      exact anchored_configuration_other z.1 z.2 j
  measurable_toFun := (measurable_pi_apply i).prodMk
    (Measurable.of_eval (fun j => measurable_pi_apply j.val))
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    change Measurable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      if h : j ≠ i then z.2 ⟨j, h⟩ else z.1)
    split_ifs <;> fun_prop

theorem cardinalHeadSplit_measurePreserving
    (μ : Measure (Covariate d)) [SigmaFinite μ] :
    MeasurePreserving (cardinalHeadSplit i) (Measure.pi (fun _ => μ))
      (μ.prod (Measure.pi (fun _ => μ))) := by
  letI : Unique {j : Fin n // j = i} :=
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ => μ) (fun j => j = i)
  have heq : (@Measure.pi {j : Fin n // j = i} (fun _ => Covariate d)
      (Subtype.fintype _) (fun _ => inferInstance) (fun _ => μ)) =
      Measure.pi (fun _ => μ) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [heq] at hs
  have hh := (measurePreserving_funUnique μ {j : Fin n // j = i}).prod
    (MeasurePreserving.id (Measure.pi (fun _ : SpatialScaleIndex i => μ)))
  exact hh.comp hs

def fullSpatialPatchDesign (d n : ℕ) : Measure (DesignSample d n) :=
  Measure.pi (fun _ => volume.restrict (spatialPatchBox d))

instance fullSpatialPatchDesign_finite (d n : ℕ) : IsFiniteMeasure (fullSpatialPatchDesign d n) := by
  unfold fullSpatialPatchDesign
  infer_instance

theorem fullSpatialPatchDesign_split
    (f : (DesignSample d n) → ℝ) :
    (∫ U, f U ∂fullSpatialPatchDesign d n) =
      ∫ z,
        f (anchoredPatchConfiguration z.1 z.2)
        ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d) := (((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm).integral_comp' f).symm

end NearlyMinimax
