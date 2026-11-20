module

public import PottsDiscontinuity.Infra.MeasureMixing
public import PottsDiscontinuity.RCInfinite.LimitComparison
public import PottsDiscontinuity.RCInfinite.TranslationSupport

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK

theorem translatedEdge_not_mem_box_of_far {e : Edge} {m k : ℕ} {a : LatticeVertex}
    (he : e ∈ boxEdges (0, 0) k) (ha : a ∉ latticeBox (0, 0) (m + k)) :
    translatedEdge (-a) e ∉ boxEdges (0, 0) m := by
  intro ht
  obtain ⟨⟨x, y⟩, hxy⟩ := Sym2.mk_surjective e.val
  have hx : x ∈ e.val := by rw [← hxy]; simp
  have hxk := (mem_boxEdges_iff (0, 0) k e).mp he x hx
  have hxt : latticeTranslate (-a) x ∈ (translatedEdge (-a) e).val := by
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  have hxm := (mem_boxEdges_iff (0, 0) m _).mp ht _ hxt
  apply ha
  simp only [mem_latticeBox, latticeTranslate, Prod.fst_neg, Prod.snd_neg, zero_sub, zero_add] at hxk hxm ⊢
  omega

theorem eventually_cylinder_translate_outside_cofinite (m : ℕ)
    {B : Set LatticeConfiguration} (hB : IsCylinder B) :
    ∀ᶠ a : LatticeVertex in cofinite,
      DependsOn (boxEdges (0, 0) m)ᶜ ((edgeTranslate a) ⁻¹' B) := by
  obtain ⟨F, hF⟩ := hB
  obtain ⟨k, hk⟩ := (eventually_finset_in_box F).exists
  filter_upwards [(latticeBox (0, 0) (m + k)).eventually_cofinite_notMem] with a ha
  intro ω η hω
  apply hF
  intro e he
  simpa using
      hω _ (translatedEdge_not_mem_box_of_far (hk he) ha)

theorem allOpen_cylinder_joint_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : IsCylinder B) :
    MixingLimit μ (fun a : LatticeVertex => edgeTranslate a) cofinite (LatticeConfiguration.allOpen F) B := by
  let p := μ.real (LatticeConfiguration.allOpen F) * μ.real B
  suffices h : Tendsto (fun a : LatticeVertex =>
      μ.real (LatticeConfiguration.allOpen F ∩ (edgeTranslate a) ⁻¹' B) - p) cofinite (𝓝 0) by
    simpa [MixingLimit] using h.add (tendsto_const_nhds (x := p))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun m =>
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)|)
      atTop (𝓝 0) := by
    simpa using
          ((tendsto_cylinder_probability θ i μ hμ (isCylinder_allOpen F)).sub
            (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F)))).abs
  have herr := herror.eventually (gt_mem_nhds hε)
  obtain ⟨m, hFm, hm⟩ := ((eventually_finset_in_box F).and herr).exists
  filter_upwards [eventually_cylinder_translate_outside_cofinite m hB] with a ha
  have hbound := cylinder_exterior_covariance_bound θ i μ hμ m F hFm
    ((edgeTranslate a) ⁻¹' B) (hB.preimage_translate a) ha
  simpa [limit_translate_real θ i μ hμ a hB.measurableSet]
      using hbound.trans_lt hm

/-- Strong mixing as the translation vector leaves every finite subset of the lattice. -/
theorem measurable_joint_cofinite (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    {A B : Set LatticeConfiguration} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MixingLimit μ (fun a : LatticeVertex => edgeTranslate a) cofinite A B := by
  have := hμ.1
  refine mixing_of_generators LatticeConfiguration.generateFrom_allOpenCylinders.symm
    LatticeConfiguration.isPiSystem_allOpenCylinders μ (fun a => ⟨edgeTranslate_measurable a,
      isRCInfiniteVolumeLimit_interior_translation_invariant θ i μ hμ a⟩) ?_ hA hB
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
  exact allOpen_cylinder_joint_cofinite θ i μ hμ F (isCylinder_allOpen G)

def IsEdgeTranslationMixing (μ : Measure LatticeConfiguration) : Prop :=
  (∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) ∧
    ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      MixingLimit μ (fun a : LatticeVertex => edgeTranslate a) cofinite A B

theorem isRCInfiniteVolumeLimit_interior_edge_mixing (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    IsEdgeTranslationMixing μ :=
  ⟨fun a => isRCInfiniteVolumeLimit_interior_translation_invariant θ i μ hμ a,
    fun _ _ hA hB => measurable_joint_cofinite θ i μ hμ hA hB⟩

end PottsDiscontinuity.RCInfinite
