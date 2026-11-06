
import GS.ManifoldCompletion.FactorCoordinates



/-!
# Openness of factor charts and horizontal slice images

The inverse Cayley chart is an open map on the whole supported-skew model.
The final lemma transfers openness through a local product chart whenever its
second coordinate leaves the projected image unchanged. It is used for the
horizontal/stabilizer decomposition of an orbit with overlap.
-/

open Set

namespace GS.OverlapGeometry








/-- A local product chart descends to open slice images when the projection is
constant in the second coordinate. Only a representative above every point of
the first-coordinate domain is needed. -/
theorem isOpen_slice_image_of_productChart
    {H K M X : Type*} [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X]
    (e : OpenPartialHomeomorph (H × K) M) (q : M → X) (p : H → X)
    (hq : IsOpenMap q)
    (heq : ∀ z ∈ e.source, q (e z) = p z.1)
    (U : Set H) (hU : IsOpen U)
    (hcover : ∀ h ∈ U, ∃ k : K, (h, k) ∈ e.source) :
    IsOpen (p '' U) := by
  let V := e.source ∩ Prod.fst ⁻¹' U
  have hV := e.open_source.inter (hU.preimage continuous_fst)
  have hopen :=
    hq _ (e.isOpen_image_of_subset_source hV inter_subset_left)
  have himage : q '' (e '' V) = p '' U := by grind
  rwa [himage] at hopen

end GS.OverlapGeometry
