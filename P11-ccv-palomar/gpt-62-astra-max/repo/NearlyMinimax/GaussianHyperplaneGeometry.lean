module

public import NearlyMinimax.GaussianAffineRepresentation
public import NearlyMinimax.PoissonCellField


@[expose] public section

/-! Borel halfspaces and their actual Gaussian--Lebesgue separating measure.
The finite slab contains every hyperplane meeting the local unit cube. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def hyperplaneRadius {d : ℕ} (Z : Covariate d) : ℝ := ∑ r, |Z r|

section
variable (d : ℕ)

def hyperplaneCube : Set (Covariate d) := {u | ∀ r, |u r| ≤ 1}

def hyperplaneSlab : Set (Covariate d × ℝ) :=
  {h | |h.2| ≤ hyperplaneRadius h.1}

def gaussianHyperplaneIntensity : Measure (Covariate d × ℝ) :=
  ((standardGaussianPi d).prod volume).restrict (hyperplaneSlab d)

end

section
variable {d : ℕ} (Z u v : Covariate d)

def hyperplaneHalfspace (h : Covariate d × ℝ) (u : Covariate d) : Fin 2 :=
  if gaussianPhase u h.1 ≤ h.2 then 0 else 1

theorem hyperplaneRadius_continuous : Continuous (hyperplaneRadius (d := d)) := by
  unfold hyperplaneRadius
  fun_prop

theorem hyperplaneSlab_measurable (d : ℕ) : MeasurableSet (hyperplaneSlab d) :=
  measurableSet_le measurable_snd.abs (hyperplaneRadius_continuous.measurable.comp measurable_fst)

theorem hyperplaneHalfspace_measurable :
    Measurable (Function.uncurry (hyperplaneHalfspace (d := d))) := Measurable.ite (measurableSet_le (by
    unfold gaussianPhase
    fun_prop) measurable_fst.snd) measurable_const measurable_const

theorem hyperplane_phase_bound (hu : u ∈ hyperplaneCube d) :
    |gaussianPhase u Z| ≤ hyperplaneRadius Z := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r _
  simpa using mul_le_mul_of_nonneg_right (hu r) (abs_nonneg (Z r))

def hyperplaneSeparationSet : Set (Covariate d × ℝ) :=
  {h | hyperplaneHalfspace h u ≠ hyperplaneHalfspace h v}

theorem hyperplaneSeparationSet_measurable :
    MeasurableSet (hyperplaneSeparationSet u v) := (measurableSet_eq_fun
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))).compl

theorem hyperplane_separation_slice :
    (fun b => (Z, b)) ⁻¹' hyperplaneSeparationSet u v =
      Ico (min (gaussianPhase u Z) (gaussianPhase v Z))
        (max (gaussianPhase u Z) (gaussianPhase v Z)) := by
  ext b
  unfold hyperplaneSeparationSet hyperplaneHalfspace
  grind

theorem hyperplane_separation_slice_volume :
    volume ((fun b => (Z, b)) ⁻¹' hyperplaneSeparationSet u v) =
      ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| := by
  rw [hyperplane_separation_slice, Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]

end

section
variable {d : ℕ} {u v : Covariate d} (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d)
include hu hv

theorem hyperplane_separation_subset_slab :
    hyperplaneSeparationSet u v ⊆ hyperplaneSlab d := by
  intro h hh
  have hs  := (Set.ext_iff.mp (hyperplane_separation_slice ..) h.2).mp hh
  have hu' := abs_le.mp (hyperplane_phase_bound h.1 u hu)
  have hv' := abs_le.mp (hyperplane_phase_bound h.1 v hv)
  exact abs_le.mpr ⟨(le_min hu'.1 hv'.1).trans hs.1,
    hs.2.le.trans (by bound)⟩

end

theorem hyperplane_slab_slice {d : ℕ} (Z : Covariate d) :
    (fun b => (Z, b)) ⁻¹' hyperplaneSlab d =
      Icc (-hyperplaneRadius Z) (hyperplaneRadius Z) := by
  ext b
  simp only [hyperplaneSlab, mem_preimage, mem_setOf_eq, mem_Icc, abs_le]

section
variable (d : ℕ)

theorem gaussianHyperplaneIntensity_univ :
    gaussianHyperplaneIntensity d univ =
      ∫⁻ Z, ENNReal.ofReal (2 * hyperplaneRadius Z) ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.prod_apply (hyperplaneSlab_measurable d)]
  simp_rw [hyperplane_slab_slice, Real.volume_Icc]
  ring

theorem hyperplane_coordinate_integrable {d : ℕ} (r : Fin d) :
    Integrable (fun Z => Z r) (standardGaussianPi d) := integrable_comp_eval (f := id)
    ((memLp_id_gaussianReal 1).integrable (by norm_num))

theorem hyperplaneRadius_integrable :
    Integrable (hyperplaneRadius) (standardGaussianPi d) := integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)

def hyperplaneNormalizingConstant : ℝ :=
  ∫ Z, 2 * hyperplaneRadius Z ∂standardGaussianPi d

theorem hyperplaneNormalizingConstant_eq :
    hyperplaneNormalizingConstant d =
      2 * d * (∫ z, |z| ∂standardGaussianLine) := by
  rw [hyperplaneNormalizingConstant, integral_const_mul]
  unfold hyperplaneRadius
  rw [integral_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)]
  have hi (r : Fin d)  := integral_comp_eval (μ := fun _ => standardGaussianLine)
      (f := fun z => |z|) (i := r) (by fun_prop)
  simp_rw [hi]
  simp
  ring

theorem gaussianHyperplaneIntensity_univ_ofReal :
    gaussianHyperplaneIntensity d univ = ENNReal.ofReal (hyperplaneNormalizingConstant d) := by
  rw [gaussianHyperplaneIntensity_univ]
  exact (ofReal_integral_eq_lintegral_ofReal ((hyperplaneRadius_integrable d).const_mul 2)
    (Filter.Eventually.of_forall (fun Z => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))))).symm

end

variable {d : ℕ}

theorem hyperplanePhase_integrable (u : Covariate d) :
    Integrable (gaussianPhase u) (standardGaussianPi d) := integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).const_mul (u r))

theorem gaussianHyperplaneIntensity_separation_ofReal {u v : Covariate d}
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ENNReal.ofReal (∫ Z, |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d) := by
  rw [((by rw [gaussianHyperplaneIntensity, Measure.restrict_apply (hyperplaneSeparationSet_measurable u v), inter_eq_left.mpr (hyperplane_separation_subset_slab hu hv), Measure.prod_apply (hyperplaneSeparationSet_measurable u v)]; simp_rw [hyperplane_separation_slice_volume] : (gaussianHyperplaneIntensity d) (hyperplaneSeparationSet u v) = ∫⁻ (Z : Covariate d), ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d))]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((hyperplanePhase_integrable u).sub (hyperplanePhase_integrable v)).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm

end NearlyMinimax
