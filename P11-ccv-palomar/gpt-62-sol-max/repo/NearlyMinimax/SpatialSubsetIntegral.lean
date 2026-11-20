module

public import NearlyMinimax.CardinalProductDesign
public import NearlyMinimax.ExponentialSpatialKernels


@[expose] public section

/-! Exact finite-product marginalization and subset kernel lifting on Q^k. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E)

section
variable [IsFiniteMeasure μ] (s : Finset I)

private theorem finite_pi_split :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => E) (· ∈ s))
      (Measure.pi (fun _ : I => μ))
      ((Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : {i : I // i ∉ s} => μ))) := by
  convert measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) (· ∈ s) using 2 <;>
    congr 1 <;> exact Subsingleton.elim _ _

theorem finite_pi_subset_integral (f : (s → E) → ℝ) :
    (∫ U : I → E, f (fun j : s => U j.val) ∂Measure.pi (fun _ : I => μ)) =
      μ.real univ ^ (Fintype.card I - s.card) * ∫ V, f V ∂Measure.pi (fun _ : s => μ) := by
  refine ((finite_pi_split μ s).integral_comp' (fun z => f z.1)).trans ?_
  rw [integral_fun_fst]
  simp [measureReal_def, Measure.pi_univ, Fintype.card_subtype_compl, ENNReal.toReal_pow]

theorem finite_pi_subset_integrable (f : (s → E) → ℝ) (hf : Integrable f (Measure.pi (fun _ : s => μ))) :
    Integrable (fun U : I → E => f (fun j : s => U j.val)) (Measure.pi (fun _ : I => μ)) :=
  (finite_pi_split μ s).integrable_comp_of_integrable (hf.comp_fst _)

end

end

theorem spatial_subset_square_integral {d k : ℕ} (s : Finset (Fin k))
    (f : (s → Covariate d) → ℝ) :
    (∫ U : Fin k → Covariate d, f (fun j : s => U j.val) ^ 2 ∂fullSpatialPatchDesign d k) =
      (2 : ℝ) ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂Measure.pi (fun _ : s => volume.restrict (spatialPatchBox d)) := by
  rw [fullSpatialPatchDesign, finite_pi_subset_integral
    (volume.restrict (spatialPatchBox d)) s (fun V => f V ^ 2)]
  simp only [measureReal_def, Measure.restrict_apply_univ, Fintype.card_fin]
  change (volume.real (spatialPatchBox d)) ^ (k - s.card) * _ = _
  rw [spatialPatchBox_real_volume, ← pow_mul]

def spatialSubsetEquiv {k : ℕ} (s : Finset (Fin k)) : s ≃ Fin s.card :=
  (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))

def spatialSubsetConfiguration {d k : ℕ} (s : Finset (Fin k))
    (U : Fin k → Covariate d) : Fin s.card → Covariate d :=
  fun j => U ((spatialSubsetEquiv s).symm j).val

theorem spatialSubsetConfiguration_measurable {d k : ℕ} (s : Finset (Fin k)) :
    Measurable (spatialSubsetConfiguration (d := d) s) := by
  solve_by_elim [Measurable.of_eval, measurable_pi_apply]

section Reindex
variable {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (e : I ≃ J)

private theorem piCongrLeft_apply (U : I → E) :
    (MeasurableEquiv.piCongrLeft (fun _ : J => E) e) U = fun j => U (e.symm j) := by
  funext j
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]

section
variable (f : (J → E) → ℝ)

theorem finite_pi_reindex_integral :
    (∫ U : I → E, f (fun j => U (e.symm j)) ∂Measure.pi (fun _ : I => μ)) =
      ∫ V, f V ∂Measure.pi (fun _ : J => μ) := by
  simpa only [piCongrLeft_apply] using (measurePreserving_piCongrLeft (fun _ : J => μ) e).integral_comp' f

theorem finite_pi_reindex_integrable
    (hf : Integrable f (Measure.pi (fun _ : J => μ))) :
    Integrable (fun U : I → E => f (fun j => U (e.symm j))) (Measure.pi (fun _ : I => μ)) := by
  simpa only [Function.comp_def, piCongrLeft_apply] using
    (measurePreserving_piCongrLeft (fun _ : J => μ) e).integrable_comp_of_integrable hf

end

end Reindex

theorem spatial_subset_square_integral_enumerated {d k : ℕ} (s : Finset (Fin k))
    (f : (Fin s.card → Covariate d) → ℝ) :
    (∫ U : Fin k → Covariate d, f (spatialSubsetConfiguration s U) ^ 2
      ∂fullSpatialPatchDesign d k) = (2 : ℝ) ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂fullSpatialPatchDesign d s.card := by
  rw [show (fun U : Fin k → Covariate d => f (spatialSubsetConfiguration s U) ^ 2) =
    (fun U => f (fun j => U ((spatialSubsetEquiv s).symm j).val) ^ 2) from rfl,
    spatial_subset_square_integral s (fun V => f (fun j => V ((spatialSubsetEquiv s).symm j))),
    finite_pi_reindex_integral _ (spatialSubsetEquiv s) (fun V => f V ^ 2)]
  rfl

end NearlyMinimax
