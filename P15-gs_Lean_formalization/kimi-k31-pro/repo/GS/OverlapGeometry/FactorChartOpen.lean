module

public import GS.ManifoldCompletion.FactorCoordinates

@[expose] public section

noncomputable section
open Set
namespace GS.OverlapGeometry

/-- A local product chart descends to open slice images when the projection is
constant in the second coordinate. -/
theorem isOpen_slice_image_of_productChart
    {H K M X : Type*} [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X]
    (e : OpenPartialHomeomorph (H × K) M) (q : M → X) (p : H → X)
    (hq : IsOpenMap q)
    (heq : ∀ z ∈ e.source, q (e z) = p z.1)
    (U : Set H) (hU : IsOpen U)
    (hcover : ∀ h ∈ U, ∃ k : K, (h, k) ∈ e.source) :
    IsOpen (p '' U) := by
  let V : Set (H × K) := e.source ∩ Prod.fst ⁻¹' U
  have hV : IsOpen V := e.open_source.inter (hU.preimage continuous_fst)
  have hopen : IsOpen (q '' (e '' V)) :=
    hq _ (e.isOpen_image_of_subset_source hV inter_subset_left)
  have himage : q '' (e '' V) = p '' U := by
    ext x
    constructor
    · rintro ⟨m, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z.1, hz.2, (heq z hz.1).symm⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨k, hk⟩ := hcover h hh
      exact ⟨e (h, k), ⟨(h, k), ⟨hk, hh⟩, rfl⟩, heq (h, k) hk⟩
  rwa [himage] at hopen

end GS.OverlapGeometry
