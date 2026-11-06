module

public import PottsDiscontinuity.RCInfinite.EdgeErgodicity
public import PottsDiscontinuity.RCInfinite.SpatialComparison

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

abbrev translatedEdge (a : LatticeVertex) : Edge ≃ Edge :=
  (latticeTranslationIso a).mapEdgeSet

theorem mem_boxEdges_iff (c : LatticeVertex) (r : ℕ) (e : Edge) :
    e ∈ boxEdges c r ↔ ∀ x ∈ e.val, x ∈ latticeBox c r := by
  constructor
  · rintro ⟨f, rfl⟩ x hx
    change x ∈ Sym2.map Subtype.val f.val at hx
    obtain ⟨v, _, hv⟩ := Sym2.mem_map.mp hx
    grind
  · intro h
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact ⟨⟨s(⟨x, (by simp_all)⟩, ⟨y, (by simp_all)⟩), he⟩, rfl⟩

theorem eventually_finset_in_box (F : Finset Edge) :
    ∀ᶠ n : ℕ in atTop, (F : Set Edge) ⊆ boxEdges (0, 0) n := by
  have h := (eventually_all_finset F).2 (fun e _ => eventually_edge_in_box e)
  tauto

theorem translatedEdge_not_mem_box {e : Edge} {m k n : ℕ}
    (he : e ∈ boxEdges (0, 0) k) (hn : m + k < n) :
    translatedEdge (-((n : ℤ), 0)) e ∉ boxEdges (0, 0) m := by
  intro ht
  obtain ⟨⟨x, y⟩, hxy⟩ := Sym2.mk_surjective e.val
  have hx : x ∈ e.val := by tauto
  have hxk := (mem_boxEdges_iff (0, 0) k e).mp he x hx
  have hxt : latticeTranslate (-((n : ℤ), 0)) x ∈
      (translatedEdge (-((n : ℤ), 0)) e).val :=
    Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  have hxm := (mem_boxEdges_iff (0, 0) m _).mp ht _ hxt
  simp only [mem_latticeBox, latticeTranslate, Prod.fst_neg, Prod.snd_neg,
    neg_zero, add_zero, zero_sub, zero_add] at hxk hxm
  omega

theorem IsCylinder.preimage_translate {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (a : LatticeVertex) : IsCylinder ((edgeTranslate a) ⁻¹' A) := by
  obtain ⟨F, hF⟩ := hA
  refine ⟨F.map (translatedEdge (-a)).toEmbedding, ?_⟩
  intro ω η hω
  apply hF
  intro e he
  have hmem : translatedEdge (-a) e ∈ F.map (translatedEdge (-a)).toEmbedding :=
    Finset.mem_map.mpr ⟨e, he, rfl⟩
  simpa using hω _ hmem

theorem cylinder_translate_outside (m k n : ℕ) (hn : m + k < n)
    {A : Set LatticeConfiguration} {F : Finset Edge} (hA : DependsOn (F : Set Edge) A)
    (hF : (F : Set Edge) ⊆ boxEdges (0, 0) k) :
    DependsOn (boxEdges (0, 0) m)ᶜ ((edgeTranslate ((n : ℤ), 0)) ⁻¹' A) := by
  intro ω η hω
  apply hA
  intro e he
  simpa only [edgeTranslate, latticeConfigurationTranslate_apply, translatedEdge] using
    hω _ (translatedEdge_not_mem_box (hF he) hn)

theorem eventually_cylinder_translate_outside (m : ℕ) {A : Set LatticeConfiguration}
    (hA : IsCylinder A) :
    ∀ᶠ n : ℕ in atTop,
      DependsOn (boxEdges (0, 0) m)ᶜ ((edgeTranslate ((n : ℤ), 0)) ⁻¹' A) := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨k, hk⟩ := (eventually_finset_in_box F).exists
  filter_upwards [eventually_gt_atTop (m + k)] with n hn
  exact cylinder_translate_outside m k n hn hF hk

theorem limit_translate_real (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (a : LatticeVertex) {B : Set LatticeConfiguration} (hB : MeasurableSet B) :
    μ.real ((edgeTranslate a) ⁻¹' B) = μ.real B := by
  simp only [Measure.real]
  rw [← Measure.map_apply (edgeTranslate_measurable a) hB,
    translation_invariant θ.toP θ.toQ θ.property i μ hμ a]

end
end PottsDiscontinuity.RCInfinite
