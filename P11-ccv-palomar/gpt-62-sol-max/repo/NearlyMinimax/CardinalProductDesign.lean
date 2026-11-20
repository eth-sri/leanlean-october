module

public import NearlyMinimax.CardinalBandL2
public import NearlyMinimax.CardinalIntegratedContinuity
public import NearlyMinimax.ExponentialSpatialKernels


@[expose] public section

/-! Genuine head splitting of finite product designs. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def cardinalHeadSplit {d n : ℕ} (i : Fin n) :
    (Fin n → Covariate d) ≃ᵐ Covariate d × (SpatialScaleIndex i → Covariate d) where
  toFun U := (U i, fun j => U j.val)
  invFun z := anchoredPatchConfiguration i z.1 z.2
  left_inv U := by
    funext j
    change (if h : j ≠ i then U j else U i) = U j
    simp_all
  right_inv z := by
    apply Prod.ext
    · apply anchored_configuration_same <;> assumption
    · funext j
      apply anchored_configuration_other <;> assumption
  measurable_toFun := (measurable_pi_apply i).prodMk
    (Measurable.of_eval (fun j => measurable_pi_apply j.val))
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    change Measurable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      if h : j ≠ i then z.2 ⟨j, h⟩ else z.1)
    split_ifs <;> fun_prop

theorem cardinalHeadSplit_measurePreserving {d n : ℕ} (i : Fin n)
    (μ : Measure (Covariate d)) [SigmaFinite μ] :
    MeasurePreserving (cardinalHeadSplit i) (Measure.pi (fun _ : Fin n => μ))
      (μ.prod (Measure.pi (fun _ : SpatialScaleIndex i => μ))) := by
  letI : Unique {j : Fin n // j = i} :=
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (fun j => j = i)
  have heq : (@Measure.pi {j : Fin n // j = i} (fun _ => Covariate d)
      (Subtype.fintype (fun j => j = i)) (fun _ => inferInstance) (fun _ => μ)) =
      Measure.pi (fun _ : {j : Fin n // j = i} => μ) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [heq] at hs
  have hh := (measurePreserving_funUnique μ {j : Fin n // j = i}).prod
    (MeasurePreserving.id (Measure.pi (fun _ : SpatialScaleIndex i => μ)))
  exact hh.comp hs

def fullSpatialPatchDesign (d n : ℕ) : Measure (Fin n → Covariate d) :=
  Measure.pi (fun _ : Fin n => volume.restrict (spatialPatchBox d))

instance fullSpatialPatchDesign_finite (d n : ℕ) : IsFiniteMeasure (fullSpatialPatchDesign d n) := by
  unfold fullSpatialPatchDesign
  infer_instance

/-- A uniform anchored integral bound extends to the full product design. -/
theorem fullSpatialPatchDesign_fiber_integral_le {d n : ℕ} (i : Fin n)
    {f : (Fin n → Covariate d) → ℝ} {B : ℝ}
    (hf : Integrable (fun z => f (anchoredPatchConfiguration i z.1 z.2))
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)))
    (hB : ∀ x ∈ spatialPatchBox d,
      (∫ y, f (anchoredPatchConfiguration i x y) ∂spatialPatchDesignMeasure i d) ≤ B) :
    (∫ U, f U ∂fullSpatialPatchDesign d n) ≤ (2 : ℝ)^d * B := by
  calc
    _ = ∫ z, f (anchoredPatchConfiguration i z.1 z.2)
        ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d) :=
      (((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm).integral_comp' f).symm
    _ ≤ _ := by
      rw [integral_prod _ hf]
      refine (integral_mono_ae hf.integral_prod_left (integrable_const B)
        ((ae_restrict_mem measurableSet_Icc).mono hB)).trans_eq ?_
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      exact congrArg (· * B) (spatialPatchBox_real_volume d)

/-- Transfer the moments of a pair kernel to the actual two-coordinate design. -/
theorem fullSpatialPatchDesign_pair_moments {d : ℕ} {f : CovariatePair d → ℝ} {B : ℝ}
    (hf : Integrable f ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))))
    (h : (∫ z, f z ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤ B) :
    Integrable (fun U : Fin 2 → Covariate d => f (U 0, U 1)) (fullSpatialPatchDesign d 2) ∧
    (∫ U : Fin 2 → Covariate d, f (U 0, U 1) ∂fullSpatialPatchDesign d 2) ≤ B := by
  have hp := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  exact ⟨hp.integrable_comp_of_integrable hf,
    (hp.integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding f).trans_le h⟩

end NearlyMinimax
