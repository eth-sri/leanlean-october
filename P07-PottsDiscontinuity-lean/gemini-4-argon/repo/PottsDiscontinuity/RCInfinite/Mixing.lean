module

public import PottsDiscontinuity.RCInfinite.GeneratorMixing
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section

theorem translatedEdge_not_mem_box_of_far {e : Edge} {m k : ℕ} {a : LatticeVertex}
    (he : e ∈ boxEdges (0, 0) k) (ha : a ∉ latticeBox (0, 0) (m + k)) :
    translatedEdge (-a) e ∉ boxEdges (0, 0) m := by
  intro ht
  obtain ⟨⟨x, y⟩, hxy⟩ := Sym2.mk_surjective e.val
  have hx : x ∈ e.val := by rw [← hxy]; simp
  have hxk := (mem_boxEdges_iff (0, 0) k e).mp he x hx
  have hxm := (mem_boxEdges_iff (0, 0) m _).mp ht _
    (Sym2.mem_map.mpr ⟨x, hx, rfl⟩ : latticeTranslate (-a) x ∈ (translatedEdge (-a) e).val)
  apply ha
  simp only [mem_latticeBox, latticeTranslate, Prod.fst_neg, Prod.snd_neg, zero_sub, zero_add] at hxk hxm ⊢
  omega

theorem eventually_cylinder_translate_outside_cofinite (m : ℕ)
    {B : Set LatticeConfiguration} (hB : IsCylinder B) :
    ∀ᶠ a : LatticeVertex in cofinite,
      DependsOn (boxEdges (0, 0) m)ᶜ ((edgeTranslate a) ⁻¹' B) := by
  obtain ⟨F, hF⟩ := hB
  obtain ⟨k, hk⟩ := (eventually_finset_in_box F).exists
  filter_upwards [(latticeBox (0, 0) (m + k)).eventually_cofinite_notMem] with a ha ω η hω
  exact hF (edgeTranslate a ω) (edgeTranslate a η) fun e he => by
    simpa only [edgeTranslate, latticeConfigurationTranslate_apply, translatedEdge] using
      hω _ (translatedEdge_not_mem_box_of_far (hk he) ha)

theorem allOpen_cylinder_covariance_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : IsCylinder B) :
    Tendsto (fun a : LatticeVertex => covariance μ (LatticeConfiguration.allOpen F)
      ((edgeTranslate a) ⁻¹' B)) cofinite (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have herror : Tendsto (fun m =>
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_cylinder_probability θ i μ hμ (isCylinder_allOpen F)).sub
        (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F)))).abs
  obtain ⟨m, hFm, hm⟩ := ((eventually_finset_in_box F).and (herror.eventually (gt_mem_nhds hε))).exists
  filter_upwards [eventually_cylinder_translate_outside_cofinite m hB] with a ha
  simpa only [Real.dist_eq, sub_zero, covariance] using
    (cylinder_exterior_covariance_bound θ i μ hμ m F hFm
      ((edgeTranslate a) ⁻¹' B) (hB.preimage_translate a) ha).trans_lt hm

theorem allOpen_measurable_covariance_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : MeasurableSet B) :
    Tendsto (fun a : LatticeVertex => covariance μ (LatticeConfiguration.allOpen F)
      ((edgeTranslate a) ⁻¹' B)) cofinite (𝓝 0) := by
  have : IsProbabilityMeasure μ := hμ.1
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨C, hC, hCB⟩ := exists_cylinder_approx μ hB (show 0 < ε / 4 by positivity)
  filter_upwards [(Metric.tendsto_nhds.mp (allOpen_cylinder_covariance_cofinite θ i μ hμ F hC))
    (ε / 2) (half_pos hε)] with a ha
  have hchange := covariance_change_right μ (isCylinder_allOpen F).measurableSet
    ((edgeTranslate_measurable a) hB) ((edgeTranslate_measurable a) hC.measurableSet)
  rw [← Set.preimage_symmDiff, limit_translate_real θ i μ hμ a (hB.symmDiff hC.measurableSet),
    symmDiff_comm] at hchange
  have htriangle := abs_sub_le (covariance μ (LatticeConfiguration.allOpen F) ((edgeTranslate a) ⁻¹' B))
    (covariance μ (LatticeConfiguration.allOpen F) ((edgeTranslate a) ⁻¹' C)) 0
  simp only [sub_zero, Real.dist_eq] at ha htriangle ⊢
  nlinarith [htriangle, hchange]

theorem allOpen_measurable_joint_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : MeasurableSet B) :
    Tendsto (fun a : LatticeVertex => μ.real (LatticeConfiguration.allOpen F ∩
      (edgeTranslate a) ⁻¹' B)) cofinite
      (𝓝 (μ.real (LatticeConfiguration.allOpen F) * μ.real B)) := by
  simpa only [covariance, limit_translate_real θ i μ hμ _ hB, sub_add_cancel, zero_add] using
    (allOpen_measurable_covariance_cofinite θ i μ hμ F hB).add
      (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F) * μ.real B))

/-- On the compact bond space, convergence on all-open generators implies
weak convergence. No monotonicity premise is needed when the limit is given. -/
theorem probabilityMeasures_tendsto_of_allOpen_real {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure LatticeConfiguration} {ν : ProbabilityMeasure LatticeConfiguration}
    (h : ∀ F : Finset Edge, Tendsto
      (fun j => (νs j).toMeasure.real (LatticeConfiguration.allOpen F)) l
      (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F)))) : Tendsto νs l (𝓝 ν) := by
  let κ : ProbabilityMeasure LatticeConfiguration → (Finset Edge → ℝ) :=
    fun η F => η.toMeasure.real (LatticeConfiguration.allOpen F)
  have hcont : Continuous κ := continuous_pi fun F => continuous_iff_continuousAt.mpr fun η => by
    simpa only [ContinuousAt, κ, ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal,
      Function.comp_def, id_eq]
      using (NNReal.continuous_coe.tendsto _).comp
        (LatticeConfiguration.tendsto_allOpen_of_weak (l := 𝓝 η) tendsto_id F)
  have hinj : Function.Injective κ := fun η ζ heq =>
    LatticeConfiguration.probabilityMeasure_eq_of_allOpen fun F => NNReal.coe_injective <| by
      simpa only [κ, ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal] using congrFun heq F
  exact (hcont.isClosedEmbedding hinj).tendsto_nhds_iff.mpr (tendsto_pi_nhds.mpr h)

/-- The actual normalized restriction to an event of positive mass. -/
def conditionalLaw (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (B : Set LatticeConfiguration) (hB : μ B ≠ 0) : ProbabilityMeasure LatticeConfiguration :=
  ⟨ProbabilityTheory.cond μ B, ProbabilityTheory.cond_isProbabilityMeasure hB⟩

theorem conditionalLaw_real (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (B : Set LatticeConfiguration) (hB : μ B ≠ 0)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    (conditionalLaw μ B hB).toMeasure.real A = (μ.real B)⁻¹ * μ.real (A ∩ B) := by
  change (ProbabilityTheory.cond μ B A).toReal = _
  rw [ProbabilityTheory.cond_apply' hA μ, ENNReal.toReal_mul, ENNReal.toReal_inv, inter_comm]
  rfl

theorem cylinder_measurable_joint_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    {A B : Set LatticeConfiguration} (hA : IsCylinder A) (hB : MeasurableSet B) :
    Tendsto (fun a : LatticeVertex => μ.real (A ∩ (edgeTranslate a) ⁻¹' B)) cofinite
      (𝓝 (μ.real A * μ.real B)) := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hmass (a : LatticeVertex) : μ ((edgeTranslate a) ⁻¹' B) = μ B := by
    rw [← Measure.map_apply (edgeTranslate_measurable a) hB,
      translation_invariant θ.toP θ.toQ θ.property i μ hμ a]
  by_cases hzero : μ B = 0
  · have hjoint (a : LatticeVertex) : μ (A ∩ (edgeTranslate a) ⁻¹' B) = 0 :=
      measure_mono_null inter_subset_right (by rw [hmass a, hzero])
    simpa only [Measure.real, hjoint, hzero, ENNReal.toReal_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : LatticeVertex => (0 : ℝ)) cofinite (𝓝 0))
  have hbne : μ.real B ≠ 0 := fun hh =>
    hzero (((ENNReal.toReal_eq_zero_iff (μ B)).mp hh).resolve_right (measure_ne_top μ B))
  let ν : LatticeVertex → ProbabilityMeasure LatticeConfiguration := fun a =>
    conditionalLaw μ ((edgeTranslate a) ⁻¹' B) (by rw [hmass a]; exact hzero)
  have hformula (a : LatticeVertex) {S : Set LatticeConfiguration} (hS : MeasurableSet S) :
      (ν a).toMeasure.real S = (μ.real B)⁻¹ * μ.real (S ∩ (edgeTranslate a) ⁻¹' B) := by
    simpa only [ν, limit_translate_real θ i μ hμ a hB] using
      conditionalLaw_real μ ((edgeTranslate a) ⁻¹' B) (by rw [hmass a]; exact hzero) hS
  let μp : ProbabilityMeasure LatticeConfiguration := ⟨μ, hprob⟩
  have hweak : Tendsto ν cofinite (𝓝 μp) :=
    probabilityMeasures_tendsto_of_allOpen_real fun F => by
      simpa only [hformula _ (isCylinder_allOpen F).measurableSet,
        show (μ.real B)⁻¹ * (μ.real (LatticeConfiguration.allOpen F) * μ.real B) =
          μ.real (LatticeConfiguration.allOpen F) by field_simp,
        μp, ProbabilityMeasure.coe_mk] using
        (tendsto_const_nhds (x := (μ.real B)⁻¹)).mul (allOpen_measurable_joint_cofinite θ i μ hμ F hB)
  have hreal : Tendsto (fun a => (ν a).toMeasure.real A) cofinite (𝓝 (μ.real A)) := by
    simpa only [ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal, Function.comp_def, μp,
      ProbabilityMeasure.coe_mk, ProbabilityMeasure.coeFn_mk]
      using (NNReal.continuous_coe.tendsto _).comp
        (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak hA.isClopen)
  have hjoint (a : LatticeVertex) : μ.real (A ∩ (edgeTranslate a) ⁻¹' B) =
      μ.real B * (ν a).toMeasure.real A := by
    rw [hformula a hA.measurableSet, ← mul_assoc, mul_inv_cancel₀ hbne, one_mul]
  simpa only [← hjoint, mul_comm] using (tendsto_const_nhds (x := μ.real B)).mul hreal

theorem covariance_comm (μ : Measure LatticeConfiguration) (A B : Set LatticeConfiguration) :
    covariance μ A B = covariance μ B A := by
  simp only [covariance, inter_comm, mul_comm]

theorem measurable_covariance_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    {A B : Set LatticeConfiguration} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun a : LatticeVertex => covariance μ A ((edgeTranslate a) ⁻¹' B)) cofinite (𝓝 0) := by
  have : IsProbabilityMeasure μ := hμ.1
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨C, hC, hCA⟩ := exists_cylinder_approx μ hA (show 0 < ε / 4 by positivity)
  have hlimC : Tendsto (fun a : LatticeVertex => covariance μ C ((edgeTranslate a) ⁻¹' B))
      cofinite (𝓝 0) := by
    simpa only [covariance, limit_translate_real θ i μ hμ _ hB, sub_self] using
      (cylinder_measurable_joint_cofinite θ i μ hμ hC hB).sub
        (tendsto_const_nhds (x := μ.real C * μ.real B))
  filter_upwards [(Metric.tendsto_nhds.mp hlimC) (ε / 2) (half_pos hε)] with a ha
  have hchange := covariance_change_right μ ((edgeTranslate_measurable a) hB) hA hC.measurableSet
  rw [covariance_comm μ _ A, covariance_comm μ _ C, symmDiff_comm A C] at hchange
  have htriangle := abs_sub_le (covariance μ A ((edgeTranslate a) ⁻¹' B))
    (covariance μ C ((edgeTranslate a) ⁻¹' B)) 0
  simp only [Real.dist_eq, sub_zero] at ha htriangle ⊢
  nlinarith [htriangle, hchange]

/-- Strong mixing as the translation vector leaves every finite subset of
the lattice, for arbitrary measurable events. -/
theorem measurable_joint_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    {A B : Set LatticeConfiguration} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun a : LatticeVertex => μ.real (A ∩ (edgeTranslate a) ⁻¹' B)) cofinite
      (𝓝 (μ.real A * μ.real B)) := by
  simpa only [covariance, limit_translate_real θ i μ hμ _ hB, sub_add_cancel, zero_add] using
    (measurable_covariance_cofinite θ i μ hμ hA hB).add
      (tendsto_const_nhds (x := μ.real A * μ.real B))

def IsEdgeTranslationMixing (μ : Measure LatticeConfiguration) : Prop :=
  (∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) ∧
    ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a : LatticeVertex => μ.real (A ∩ (edgeTranslate a) ⁻¹' B)) cofinite
        (𝓝 (μ.real A * μ.real B))

theorem isRCInfiniteVolumeLimit_interior_edge_mixing (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    IsEdgeTranslationMixing μ :=
  ⟨fun a => translation_invariant θ.toP θ.toQ θ.property i μ hμ a,
    fun _ _ hA hB => measurable_joint_cofinite θ i μ hμ hA hB⟩

end
end PottsDiscontinuity.RCInfinite
