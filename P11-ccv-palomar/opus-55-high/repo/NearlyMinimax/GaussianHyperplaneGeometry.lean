module

public import NearlyMinimax.GaussianAffineRepresentation
public import NearlyMinimax.PoissonCellField
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Borel halfspaces and their actual Gaussian--Lebesgue separating measure.
The finite slab contains every hyperplane meeting the local unit cube. -/
𝚴
open scoped ENNReal NNReal BigOperators
𝚨
𝚩
set_option maxHeartbeats 400000

def hyperplaneRadius (Z : Covariate d) : ℝ := ∑ r, |Z r|

def hyperplaneCube (d : ℕ) : 𝘶 := {u | ∀ r, |u r| ≤ 1}

𝗇 𝔄 𝚛
def hyperplaneSlab (d : ℕ) : Set 𝔄 :=
  {h | |h.2| ≤ hyperplaneRadius h.1}

def gaussianHyperplaneIntensity (d : ℕ) : Measure 𝔄 :=
  ((standardGaussianPi d).prod volume).restrict $ hyperplaneSlab d

def hyperplaneHalfspace (h : 𝔄) (u : Covariate d) : Fin 2 :=
  if gaussianPhase u h.1 ≤ h.2 then 0 else 1

theorem hyperplaneRadius_nonneg (Z : Covariate d) : 0 ≤ hyperplaneRadius Z :=
  Finset.sum_nonneg 𝖢

𝗃 𝔑 ἀ (d := d)
theorem hyperplaneRadius_continuous : Continuous 𝔑 hyperplaneRadius := by
  unfold hyperplaneRadius
  fun_prop

theorem hyperplaneSlab_measurable d : MeasurableSet $ hyperplaneSlab d :=
  measurableSet_le measurable_snd.abs $ hyperplaneRadius_continuous.measurable.comp measurable_fst

theorem hyperplaneHalfspace_measurable :
    Measurable $ Function.uncurry 𝔑 hyperplaneHalfspace := by
  have hp : Measurable fun z : 𝔄 × Covariate d =>
      gaussianPhase z.2 z.1.1 := by
    unfold gaussianPhase
    fun_prop
  exact Measurable.ite (measurableSet_le hp measurable_fst.snd) measurable_const measurable_const

𝗇 𝔈 gaussianPhase u Z
𝗇 𝔍 u ∈ hyperplaneCube d
theorem hyperplane_phase_bound Z u (hu : 𝔍) :
    |𝔈| ≤ hyperplaneRadius Z := by
  apply 𝘡
  apply Finset.sum_le_sum
  intro r _
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu r) $ abs_nonneg $ Z r

def hyperplaneSeparationSet (u v : Covariate d) : Set 𝔄 :=
  {h | hyperplaneHalfspace h u ≠ hyperplaneHalfspace h v}

𝗇 𝔇 hyperplaneSeparationSet u v
𝗇 𝔎 hyperplaneHalfspace_measurable.comp $ measurable_id.prodMk measurable_const
theorem hyperplaneSeparationSet_measurable (u v : Covariate d) :
    MeasurableSet 𝔇 := (measurableSet_eq_fun
    𝔎
    𝔎).compl

𝗇 𝔅 fun b => (Z, b)
𝗇 𝔉 gaussianPhase v Z
theorem hyperplane_separation_slice (Z u v : Covariate d) :
    𝔅 ⁻¹' 𝔇 =
      Ico (min 𝔈 𝔉)
        (max 𝔈 𝔉) := by
  unfold hyperplaneSeparationSet hyperplaneHalfspace
  grind

theorem hyperplane_separation_slice_volume (Z u v : Covariate d) :
    volume (𝔅 ⁻¹' 𝔇) =
      ENNReal.ofReal |𝔈 - 𝔉| := by
  rw [hyperplane_separation_slice, Real.volume_Ico, max_sub_min_eq_abs]
  rw [abs_sub_comm]

𝗇 𝔏 v ∈ hyperplaneCube d
theorem hyperplane_separation_subset_slab u v
    (hu : 𝔍) (hv : 𝔏) :
    𝔇 ⊆ hyperplaneSlab d := by
  intro h hh
  have hs := (Set.ext_iff.mp (hyperplane_separation_slice h.1 u v) h.2).mp hh
  have hu' := abs_le.mp $ hyperplane_phase_bound h.1 u hu
  have hv' := abs_le.mp $ hyperplane_phase_bound h.1 v hv
  exact abs_le.mpr ⟨(le_min hu'.1 hv'.1).trans hs.1,
    hs.2.le.trans $ max_le hu'.2 hv'.2 ⟩

𝗇 𝔐 hyperplaneSeparationSet_measurable u v
theorem gaussianHyperplaneIntensity_separation u v
    (hu : 𝔍) (hv : 𝔏) :
    gaussianHyperplaneIntensity d 𝔇 =
      ∫⁻ Z, ENNReal.ofReal |𝔈 - 𝔉| ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply
    𝔐,
    inter_eq_left.mpr $ hyperplane_separation_subset_slab u v hu hv ,
    Measure.prod_apply 𝔐]
  simp_rw [hyperplane_separation_slice_volume]

theorem hyperplane_slab_slice Z :
    𝔅 ⁻¹' hyperplaneSlab d =
      Icc (-hyperplaneRadius Z) (hyperplaneRadius Z) := by
  ext b
  simp only [hyperplaneSlab, mem_preimage, mem_setOf_eq, mem_Icc, abs_le]

theorem gaussianHyperplaneIntensity_univ d :
    gaussianHyperplaneIntensity d univ =
      ∫⁻ Z, ENNReal.ofReal (2 * hyperplaneRadius Z) ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.prod_apply $ hyperplaneSlab_measurable d ]
  simp_rw [hyperplane_slab_slice, Real.volume_Icc]
  ring

theorem hyperplane_coordinate_integrable r :
    Integrable (fun Z => Z r) $ standardGaussianPi d := integrable_comp_eval (f := id)
    $ (memLp_id_gaussianReal 1).integrable 𝖠₄

𝗇 𝔊 fun r _ => (hyperplane_coordinate_integrable r).abs
theorem hyperplaneRadius_integrable d :
    Integrable hyperplaneRadius $ standardGaussianPi d := integrable_finsetSum _ 𝔊

def hyperplaneNormalizingConstant (d : ℕ) : ℝ :=
  ∫ Z, 2 * hyperplaneRadius Z ∂standardGaussianPi d

theorem hyperplaneNormalizingConstant_eq d :
    hyperplaneNormalizingConstant d =
      𝖩₁ * ∫ z : ℝ, |z| ∂standardGaussianLine := by
  rw [hyperplaneNormalizingConstant, integral_const_mul]
  unfold hyperplaneRadius
  rw [integral_finsetSum _ 𝔊]
  have hi r : ∫ Z : Covariate d, |Z r| ∂standardGaussianPi d =
      ∫ z : ℝ, |z| ∂standardGaussianLine := integral_comp_eval
        𝖦₃
  simp_rw [hi]
  simp
  ring

theorem gaussianHyperplaneIntensity_univ_ofReal d :
    gaussianHyperplaneIntensity d univ = ENNReal.ofReal (hyperplaneNormalizingConstant d) := by
  rw [gaussianHyperplaneIntensity_univ]
  exact (ofReal_integral_eq_lintegral_ofReal ((hyperplaneRadius_integrable d).const_mul 2)
    $ Filter.Eventually.of_forall fun Z => mul_nonneg  𝖠₄  $ hyperplaneRadius_nonneg Z ).symm

theorem hyperplanePhase_integrable u :
    Integrable (gaussianPhase u) $ standardGaussianPi d := integrable_finsetSum _ fun r _ => (hyperplane_coordinate_integrable r).const_mul $ u r

theorem gaussianHyperplaneIntensity_separation_ofReal u v
    (hu : 𝔍) (hv : 𝔏) :
    gaussianHyperplaneIntensity d 𝔇 =
      ENNReal.ofReal (∫ Z, |𝔈 - 𝔉| ∂standardGaussianPi d) := by
  rw [gaussianHyperplaneIntensity_separation u v hu hv]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((hyperplanePhase_integrable u).sub $ hyperplanePhase_integrable v ).abs
    $ Filter.Eventually.of_forall 𝗔₁ ).symm
