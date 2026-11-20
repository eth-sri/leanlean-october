module

public import RequestProject.PushoutUniversalEmbedding
public import RequestProject.CombCoveringLift

@[expose] public section

/-! The actual L-copy in the universal pushout is injective on all cells.
The base map itself identifies old cells; source/base vertices and the
covering lifting uniqueness recover them. Unverified source. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.PushoutSheets
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

include hp hiV hiE in
theorem pushE_injective_at_source {e f : L.E}
    (hs : L.src e = L.src f) (hf : pushE p i e = pushE p i f) : e = f := by
  rcases glueCell_eq p.onE hiE hf with h | ⟨d, e, rfl, rfl, h⟩
  · exact h
  · have hsrc := hiV (by simpa only [i.src_onE] using hs)
    exact congrArg i.onE (hp.uniqueLifts.edge_eq hsrc h)

include hp hiV hiF in
theorem pushF_injective_at_base {e f : L.F}
    (hs : L.base e = L.base f) (hf : pushF p i e = pushF p i f) : e = f := by
  rcases glueCell_eq p.onF hiF hf with h | ⟨d, e, rfl, rfl, h⟩
  · exact h
  · have hbase := hiV (by simpa only [i.base_onF] using hs)
    exact congrArg i.onF (hp.uniqueLifts.face_eq hbase h)

include hp hr he in
theorem univLift_edges_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onE :=
  univLiftE_injective _ (univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht)
    (fun _ _ => pushE_injective_at_source p hp i hiV hiE)

include hp hr he in
theorem univLift_faces_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onF :=
  univLiftF_injective _ (univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht)
    (fun _ _ => pushF_injective_at_base p hp i hiV hiF)

end FiniteChains.Comb.PushoutSheets
