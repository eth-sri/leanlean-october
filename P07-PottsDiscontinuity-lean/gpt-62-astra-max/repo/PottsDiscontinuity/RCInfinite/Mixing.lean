module

public import PottsDiscontinuity.RCInfinite.LimitComparison
public import PottsDiscontinuity.RCInfinite.TranslationSupport
public import PottsDiscontinuity.Infra.Mixing

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
  have hx : x ∈ e.val := by grind
  have hxk := (mem_boxEdges_iff _ k e).mp he x hx
  have hxt : latticeTranslate (-a) x ∈ (translatedEdge (-a) e).val := Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  have hxm := (mem_boxEdges_iff _ m _).mp ht _ hxt
  grind [mem_latticeBox, latticeTranslate, Prod.fst_neg, Prod.snd_neg, zero_sub, zero_add]

variable (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (F : Finset Edge) (m : ℕ)
    {B : Set LatticeConfiguration} (hB : IsCylinder B)

include hB in
theorem eventually_cylinder_translate_outside_cofinite :
    ∀ᶠ a : LatticeVertex in cofinite,
      DependsOn (boxEdges (0, 0) m)ᶜ ((edgeTranslate a) ⁻¹' B) := by
  obtain ⟨F, hF⟩ := hB
  obtain ⟨k, hk⟩ := (eventually_finset_in_box F).exists
  filter_upwards [(latticeBox (0, 0) (m + k)).eventually_cofinite_notMem] with a ha
  intro ω η hω
  apply hF
  intro e he
  simpa using hω _ (translatedEdge_not_mem_box_of_far (hk he) ha)

include hμ hB in
theorem allOpen_cylinder_covariance_cofinite :
    Tendsto (fun a : LatticeVertex => μ.real (LatticeConfiguration.allOpen F ∩ (edgeTranslate a) ⁻¹' B) -
      μ.real (LatticeConfiguration.allOpen F) * μ.real ((edgeTranslate a) ⁻¹' B)) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun m =>
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)|)
      atTop (𝓝 0) := by
    simpa using ((tendsto_cylinder_probability hμ (isCylinder_allOpen F)).sub (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F)))).abs
  obtain ⟨m, hFm, hm⟩ := ((eventually_finset_in_box F).and (herror.eventually (gt_mem_nhds hε))).exists
  filter_upwards [eventually_cylinder_translate_outside_cofinite m hB] with a ha
  have hbound := cylinder_exterior_covariance_bound θ i μ hμ m F hFm
    _ (hB.preimage_translate a) ha
  simpa only [Real.dist_eq, sub_zero] using hbound.trans_lt hm

include hμ in
theorem isRCInfiniteVolumeLimit_interior_edge_mixing :
    MixingFamily (fun a => ⇑(edgeTranslate a)) μ cofinite := by
  have := hμ.1
  have hp a : MeasurePreserving (edgeTranslate a) μ μ :=
    ⟨edgeTranslate_measurable a, isRCInfiniteVolumeLimit_interior_translation_invariant hμ a⟩
  refine ⟨hp, fun {_ _} => mixing_of_piSystem hp LatticeConfiguration.generateFrom_allOpenCylinders.symm
    LatticeConfiguration.isPiSystem_allOpenCylinders ?_⟩
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
  have hg := isCylinder_allOpen G
  simpa only [limit_translate_real θ i μ hμ _ hg.measurableSet, sub_add_cancel, zero_add] using
    (allOpen_cylinder_covariance_cofinite θ i μ hμ F hg).add
      (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F) * μ.real (LatticeConfiguration.allOpen G)))

end
end PottsDiscontinuity.RCInfinite
