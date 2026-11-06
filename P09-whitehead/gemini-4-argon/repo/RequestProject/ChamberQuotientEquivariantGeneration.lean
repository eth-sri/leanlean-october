module

public import RequestProject.ChamberQuotientBaseSimplyConnected
public import RequestProject.OrderComponentLabels
public import RequestProject.OrderPosetCovering
public import RequestProject.SimplyConnectedCoverEquiv
public import RequestProject.OrderUniversalDeck
public import RequestProject.OrderSubposetChains
public import RequestProject.StrictOrderChains

@[expose] public section

/-! Actual quotient cycles are generated modulo genuine three-boundaries by
deck translates of genuine universal-cover cycles of the chosen base. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def qLiftedBaseTriangleMap (a : Qpos A X att) :
    OrdTri (QLiftedBase a) → OrdTri (UOrder (Qpos A X att) a) :=
  fun t => ⟨(t.1.1.1, t.1.2.1.1, t.1.2.2.1), t.2⟩

def qLiftedBaseFaceMap (a : Qpos A X att) :
    OrdTri (QLiftedBase a) → UF (orderCx (Qpos A X att)) a :=
  uOrderFace ∘ qLiftedBaseTriangleMap a

theorem qpos_isConnected_of_zpos
    (hconn : IsConnected (orderCx (Zpos A X (IsGamma A) att))) :
    IsConnected (orderCx (Qpos A X att)) := by
  intro q r
  obtain ⟨v, hv⟩ := zProj_surjective (A := A) (X := X) (att := att) q
  obtain ⟨w, hw⟩ := zProj_surjective (A := A) (X := X) (att := att) r
  obtain ⟨l, hl⟩ := hconn v w
  let p := orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone
  have h := isPath_mapPath p hl
  change IsPath (orderCx (Qpos A X att)).src (orderCx (Qpos A X att)).tgt
    (mapPath p l) (zProj v) (zProj w) at h
  erw [hv, hw] at h
  exact ⟨mapPath p l, h⟩

omit [Fintype V] in
theorem exists_qCover_base_cycle_preimage {a : Qpos A X att}
    (c : UF (orderCx (Qpos A X att)) a →₀ ℤ)
    (hs : ∀ t ∈ c.support, InQBase t.1.2.1.1 ∧ InQBase t.1.2.1.2.1 ∧
      InQBase t.1.2.1.2.2)
    (hc : Comb.bdry2 (uCover (orderCx (Qpos A X att)) a) c = 0) :
    ∃ d : OrdTri (QLiftedBase a) →₀ ℤ,
      Comb.bdry2 (orderCx (QLiftedBase a)) d = 0 ∧
      Finsupp.mapDomain (qLiftedBaseFaceMap a) d = c := by
  classical
  obtain ⟨e, ⟨he, hecyc⟩, _⟩ := exists_unique_uOrder_cycle c hc
  have he' : Finsupp.mapDomain uOrderFace e = c := he
  let S : Set (UOrder (Qpos A X att) a) := {p | InQBase (uOrderEnd p)}
  have hes : ∀ t ∈ e.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have ht' : uOrderFace t ∈ c.support := by
      erw [← he', Finsupp.mapDomain_support_of_injective uOrderFace_injective]
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    exact hs _ ht'
  obtain ⟨d, hd, hdcyc⟩ := exists_ordSubposet_cycle S e hes hecyc
  refine ⟨d, hdcyc, ?_⟩
  change Finsupp.mapDomain (uOrderFace ∘ (ordSubposetIncl S).onF) d = c
  erw [Finsupp.mapDomain_comp]
  change Finsupp.mapDomain uOrderFace (chain2 (ordSubposetIncl S) d) = c
  erw [hd, he']
