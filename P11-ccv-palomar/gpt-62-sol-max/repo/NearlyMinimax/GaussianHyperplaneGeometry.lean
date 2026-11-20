module

public import NearlyMinimax.FiniteBounds

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

def hyperplaneCube (d : ℕ) : Set (Covariate d) := {u | ∀ r, |u r| ≤ 1}

def hyperplaneSlab (d : ℕ) : Set (Covariate d × ℝ) :=
  {h | |h.2| ≤ hyperplaneRadius h.1}

def gaussianHyperplaneIntensity (d : ℕ) : Measure (Covariate d × ℝ) :=
  ((standardGaussianPi d).prod volume).restrict (hyperplaneSlab d)

def hyperplaneHalfspace {d : ℕ} (h : Covariate d × ℝ) (u : Covariate d) : Fin 2 :=
  if gaussianPhase u h.1 ≤ h.2 then 0 else 1

section
variable {d : ℕ}

theorem hyperplaneRadius_nonneg (Z : Covariate d) : 0 ≤ hyperplaneRadius Z :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem hyperplaneRadius_continuous : Continuous (hyperplaneRadius (d := d)) := by
  unfold hyperplaneRadius
  fun_prop

end

theorem hyperplaneSlab_measurable (d : ℕ) : MeasurableSet (hyperplaneSlab d) :=
  measurableSet_le (measurable_snd.abs) (hyperplaneRadius_continuous.measurable.comp measurable_fst)

section
variable {d : ℕ}

theorem hyperplaneHalfspace_measurable :
    Measurable (Function.uncurry (hyperplaneHalfspace (d := d))) := by
  have hp : Measurable (fun z : (Covariate d × ℝ) × Covariate d =>
      gaussianPhase z.2 z.1.1) := by
    unfold gaussianPhase
    fun_prop
  exact Measurable.ite (measurableSet_le hp measurable_fst.snd) measurable_const measurable_const

theorem hyperplane_phase_bound (Z u : Covariate d) (hu : u ∈ hyperplaneCube d) :
    |gaussianPhase u Z| ≤ hyperplaneRadius Z := by
  unfold gaussianPhase hyperplaneRadius
  simpa only [mul_comm, mul_one, one_mul] using abs_weighted_sum_le (s := Finset.univ) (w := Z)
    (f := u) (B := 1) (fun i _ => hu i)

end

def hyperplaneSeparationSet {d : ℕ} (u v : Covariate d) : Set (Covariate d × ℝ) :=
  {h | hyperplaneHalfspace h u ≠ hyperplaneHalfspace h v}

section
variable {d : ℕ}

theorem hyperplaneSeparationSet_measurable (u v : Covariate d) :
    MeasurableSet (hyperplaneSeparationSet u v) := by
  exact (measurableSet_eq_fun
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))).compl

section
variable (Z u v : Covariate d)

theorem hyperplane_separation_slice :
    (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v =
      Ico (min (gaussianPhase u Z) (gaussianPhase v Z))
        (max (gaussianPhase u Z) (gaussianPhase v Z)) := by
  ext b
  unfold hyperplaneSeparationSet hyperplaneHalfspace
  simp only [mem_preimage, mem_setOf_eq, mem_Ico]
  grind

theorem hyperplane_separation_slice_volume :
    volume ((fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v) =
      ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| := by
  simp [hyperplane_separation_slice, Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]

end

section
variable (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d)
include hu hv

theorem hyperplane_separation_subset_slab :
    hyperplaneSeparationSet u v ⊆ hyperplaneSlab d := by
  intro h hh
  have hs := (Set.ext_iff.mp (hyperplane_separation_slice h.1 u v) h.2).mp hh
  have hu' := abs_le.mp (hyperplane_phase_bound h.1 u hu)
  have hv' := abs_le.mp (hyperplane_phase_bound h.1 v hv)
  exact abs_le.mpr ⟨(le_min hu'.1 hv'.1).trans hs.1,
    hs.2.le.trans (max_le hu'.2 hv'.2)⟩

theorem gaussianHyperplaneIntensity_separation :
    gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ∫⁻ Z, ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply
    (hyperplaneSeparationSet_measurable u v),
    inter_eq_left.mpr (hyperplane_separation_subset_slab u v hu hv),
    Measure.prod_apply (hyperplaneSeparationSet_measurable u v)]
  simp_rw [hyperplane_separation_slice_volume]

end

theorem hyperplane_slab_slice (Z : Covariate d) :
    (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSlab d =
      Icc (-hyperplaneRadius Z) (hyperplaneRadius Z) := by
  ext b
  simp only [hyperplaneSlab, mem_preimage, mem_setOf_eq, mem_Icc, abs_le]

end

theorem gaussianHyperplaneIntensity_univ (d : ℕ) :
    gaussianHyperplaneIntensity d univ =
      ∫⁻ Z, ENNReal.ofReal (2 * hyperplaneRadius Z) ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.prod_apply (hyperplaneSlab_measurable d)]
  grind [hyperplane_slab_slice, Real.volume_Icc]

theorem hyperplane_coordinate_integrable {d : ℕ} (r : Fin d) :
    Integrable (fun Z : Covariate d => Z r) (standardGaussianPi d) := by
  exact integrable_comp_eval (μ := fun _ : Fin d => standardGaussianLine) (i := r) (f := id)
    ((memLp_id_gaussianReal (μ := 0) (v := 1) (1 : ℝ≥0)).integrable (by norm_num))

theorem hyperplaneRadius_integrable (d : ℕ) :
    Integrable (hyperplaneRadius (d := d)) (standardGaussianPi d) := integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)

def hyperplaneNormalizingConstant (d : ℕ) : ℝ :=
  ∫ Z, 2 * hyperplaneRadius Z ∂standardGaussianPi d

section
variable (d : ℕ)

theorem hyperplaneNormalizingConstant_eq :
    hyperplaneNormalizingConstant d =
      2 * d * (∫ z : ℝ, |z| ∂standardGaussianLine) := by
  rw [hyperplaneNormalizingConstant, integral_const_mul]
  unfold hyperplaneRadius
  rw [integral_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)]
  have hi (r : Fin d) : (∫ Z : Covariate d, |Z r| ∂standardGaussianPi d) =
      ∫ z : ℝ, |z| ∂standardGaussianLine := by
    apply integral_comp_eval <;> fun_prop
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem gaussianHyperplaneIntensity_univ_ofReal :
    gaussianHyperplaneIntensity d univ = ENNReal.ofReal (hyperplaneNormalizingConstant d) := by
  rw [gaussianHyperplaneIntensity_univ]
  exact (ofReal_integral_eq_lintegral_ofReal ((hyperplaneRadius_integrable d).const_mul 2)
    (Filter.Eventually.of_forall (fun Z => mul_nonneg (by norm_num) (hyperplaneRadius_nonneg Z)))).symm

end

section
variable {d : ℕ}

theorem hyperplanePhase_integrable (u : Covariate d) :
    Integrable (gaussianPhase u) (standardGaussianPi d) := integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).const_mul (u r))

theorem gaussianHyperplaneIntensity_separation_ofReal (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ENNReal.ofReal (∫ Z, |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d) := by
  rw [gaussianHyperplaneIntensity_separation u v hu hv]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((hyperplanePhase_integrable u).sub (hyperplanePhase_integrable v)).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm

end

end NearlyMinimax
