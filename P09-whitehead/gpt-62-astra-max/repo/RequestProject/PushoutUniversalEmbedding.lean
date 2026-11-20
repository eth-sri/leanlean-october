module

public import RequestProject.PushoutFundamentalRetraction
public import RequestProject.RegularCoverEdgeLabels
public import RequestProject.UniversalCoverPi1Injection

@[expose] public section

/-! Actual sheet separation in the universal cover of the descent pushout.
The map L→K∪D L identifies old vertices, so fundamental-group injection
alone is insufficient; the regular-cover labels supply the missing test.
No universal-cover embedding hypothesis is assumed. Unverified source. -/

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u v

namespace EdgeLabels
variable {X : Complex2.{u}} {G : Type v} [Group G]

variable (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1) (a : X.V)

def vertexRead : UV X a → G :=
  Quotient.lift _ (fun _ _ h => read_htpy w hw h)

@[simp] theorem vertexRead_mk (p : PathFrom X a) : vertexRead w hw a (UV.mk p) = read w p.val := rfl
end EdgeLabels

namespace PushoutSheets
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

def potential (v : L.V) := if h : ∃ d, i.onV d = v then
  RegularCoverLabels.sheet p hp a hr h.choose else 1

include hiV in
theorem potential_core (d : D.V) : potential p hp a hr i (i.onV d) =
    RegularCoverLabels.sheet p hp a hr d := by
  have h : ∃ e, i.onV e = i.onV d := ⟨d, rfl⟩
  simp only [potential, dif_pos h, hiV h.choose_spec]

def labels : (pushoutComplex p i hiV hiE).E → Q
  | Sum.inl e => RegularCoverLabels.edge p hp a hr e
  | Sum.inr e => (potential p hp a hr i (L.src e.val))⁻¹ * potential p hp a hr i (L.tgt e.val)

include he in
theorem labels_pushE (e : L.E) : labels p hp a hr i hiV hiE (pushE p i e) =
    (potential p hp a hr i (L.src e))⁻¹ * potential p hp a hr i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE]
    rw [i.src_onE, i.tgt_onE, potential_core p hp a hr i hiV,
      potential_core p hp a hr i hiV]; exact RegularCoverLabels.edge_projection p hp a hr he d
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include he in
theorem read_pushPath {l : List _} {v w : L.V}
    (hl : IsPath L.src L.tgt l v w) :
    EdgeLabels.read (labels p hp a hr i hiV hiE)
      (mapPath (pushoutMap p i hiV hiE hiF) l) =
      (potential p hp a hr i v)⁻¹ * potential p hp a hr i w := by
  rw [EdgeLabels.read_mapPath]
  solve_by_elim [EdgeLabels.read_potential, labels_pushE]

include he hiF in
theorem labels_rel (f : (pushoutComplex p i hiV hiE).F) :
    EdgeLabels.read (labels p hp a hr i hiV hiE) ((pushoutComplex p i hiV hiE).att f) = 1 := by
  cases f with
  | inl f =>
      change EdgeLabels.read _ (mapPath (pushoutInl p i hiV hiE) _) = 1
      rw [EdgeLabels.read_mapPath]
      apply RegularCoverLabels.edge_rel <;> assumption
  | inr f =>
      have h := read_pushPath p hp a hr he i hiV hiE hiF (L.att_isLoop f.val)
      aesop

include hiV in
/-- An old vertex is determined by its projected vertex together with its
actual deck coordinate. Off-core vertices already retain their labels. -/
theorem pushV_potential_injective {v w : L.V}
    (hv : pushV p i v = pushV p i w)
    (hs : potential p hp a hr i v = potential p hp a hr i w) : v = w := by
  by_cases hvD : ∃ d, i.onV d = v
  · obtain ⟨d, rfl⟩ := hvD
    rw [pushV_of_mem p hiV] at hv
    by_cases hwD : ∃ e, i.onV e = w
    · grind [pushV_of_mem, potential_core, RegularCoverLabels.sheet_fibre_injective]
    · rw [pushV_of_off p i ⟨w, fun e he => hwD ⟨e, he⟩⟩] at hv <;> simp_all
  · rw [pushV_of_off p i ⟨v, fun d hd => hvD ⟨d, hd⟩⟩] at hv
    by_cases hwD : ∃ e, i.onV e = w
    · grind [pushV_of_mem]
    · rw [pushV_of_off p i ⟨w, fun e he => hwD ⟨e, he⟩⟩] at hv <;> grind

variable (v₀ : L.V)

theorem read_univLift (v : UV L v₀) :
    EdgeLabels.vertexRead _
      (labels_rel p hp a hr he i hiV hiE hiF) (pushV p i v₀)
      (univLiftV v₀ (pushoutMap p i hiV hiE hiF) v) =
      (potential p hp a hr i v₀)⁻¹ * potential p hp a hr i (endV v) := by
  induction v using UV.ind with
  | h l => exact read_pushPath p hp a hr he i hiV hiE hiF l.property

include hp hr he in
theorem univLift_endpoint_reflect {v w : UV L v₀}
    (h : univLiftV v₀ _ v =
      univLiftV v₀ (pushoutMap p i hiV hiE hiF) w) : endV v = endV w := by
  apply pushV_potential_injective p hp a hr i hiV
  · simpa only [endV_univLiftV, pushoutMap] using (congrArg endV h)
  · have hv := congrArg (EdgeLabels.vertexRead (labels p hp a hr i hiV hiE)
      (labels_rel p hp a hr he i hiV hiE hiF) (pushV p i v₀)) h
    rw [read_univLift p hp a hr he i hiV hiE hiF v₀ v,
      read_univLift p hp a hr he i hiV hiE hiF v₀ w] at hv <;> simp_all

include hp hr he in
theorem univLift_vertices_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF)) := by
  intro v w h
  obtain ⟨g, hg, _⟩ := (isRegular_univProj).simply_transitive v w (univLift_endpoint_reflect p hp a hr he i hiV hiE hiF (i.onV d₀) h)
  change deckV g v = w at hg
  have hfix : deckV (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀) g)
      (univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF) v) =
      univLiftV _ _ v := by
    grind [univLiftV_deckV]
  have hgone := PushoutFundamental.pi1_pushoutMap_injective p i hiV hiE hiF hD hL d₀ ht
    ((deckV_free _ _ _ hfix).trans (map_one _).symm)
  simp_all [hgone, deckV_one]

end PushoutSheets
end FiniteChains.Comb
