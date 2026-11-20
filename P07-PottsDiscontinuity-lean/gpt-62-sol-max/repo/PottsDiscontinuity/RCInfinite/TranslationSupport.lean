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
    exact hv ▸ v.property
  · intro h
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hx := h x (by simp)
      have hy : y ∈ latticeBox c r := h y (by simp)
      exact ⟨⟨s(⟨x, hx⟩, ⟨y, hy⟩), he⟩, rfl⟩

theorem eventually_finset_in_box (F : Finset Edge) :
    ∀ᶠ n : ℕ in atTop, (F : Set Edge) ⊆ boxEdges (0, 0) n := by
  have h := (eventually_all_finset F).2 (fun e _ => eventually_edge_in_box e)
  assumption

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

theorem limit_translate_real (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (a : LatticeVertex) {B : Set LatticeConfiguration} (hB : MeasurableSet B) :
    μ.real ((edgeTranslate a) ⁻¹' B) = μ.real B := by
  simp only [Measure.real]
  rw [← Measure.map_apply (edgeTranslate_measurable a) hB,
    isRCInfiniteVolumeLimit_interior_translation_invariant θ i μ hμ a]

end
end PottsDiscontinuity.RCInfinite
