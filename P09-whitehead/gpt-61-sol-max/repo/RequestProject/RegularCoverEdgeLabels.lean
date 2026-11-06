import Mathlib.Tactic

import RequestProject.CombEdgeLabels
import RequestProject.CombCoveringLift

/-! Actual group-valued sheet coordinates of a regular cellular covering.
Edge compatibility of its deck maps is recorded explicitly: the older
`IsRegular` predicate only records compatibility on vertices. A deck map
of a genuine topological covering has both properties. Unverified source. -/

noncomputable section


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.RegularCoverLabels
variable {D K : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)

def sectionV (v : K.V)  := Classical.choose (hp.surjV v)
abbrev sectionV_spec (v : K.V)  :=
  Classical.choose_spec (hp.surjV v)

variable (d : D.V)
def sheet   := Classical.choose
  (hr.simply_transitive (sectionV p hp (p.onV d)) d (sectionV_spec p hp (p.onV d)))

theorem sheet_spec  : a.smulV (sheet p hp a hr d) (sectionV p hp (p.onV d)) = d :=
  (Classical.choose_spec (hr.simply_transitive (sectionV p hp (p.onV d)) d
    (sectionV_spec p hp (p.onV d)))).1

theorem sheet_unique  (q : Q)
    (hq : a.smulV q (sectionV p hp (p.onV d)) = d) : q = sheet p hp a hr d :=
  (Classical.choose_spec (hr.simply_transitive (sectionV p hp (p.onV d)) d
    (sectionV_spec p hp (p.onV d)))).2 q hq

theorem sheet_deck (q : Q) (d : D.V) :
    sheet p hp a hr (a.smulV q d) = q * sheet p hp a hr d := by
  symm
  apply sheet_unique
  rw [hr.compat, a.mul_smulV, sheet_spec]

theorem sheet_fibre_injective {d e : D.V} (hf : p.onV d = p.onV e)
    (hs : sheet p hp a hr d = sheet p hp a hr e) : d = e := by
  grind [sheet_spec]

variable (e : K.E)
def liftGerm   := Classical.choose
  (exists_unique_liftGerm hp (sectionV p hp (K.src e))
    (eb := (e, true)) (sectionV_spec p hp (K.src e)).symm)

abbrev liftGerm_spec   :=
  (Classical.choose_spec (exists_unique_liftGerm hp (sectionV p hp (K.src e))
    (eb := (e, true)) (sectionV_spec p hp (K.src e)).symm)).1

def liftEdge   := (liftGerm p hp e).1
theorem liftEdge_source  : D.src (liftEdge p hp e) = sectionV p hp (K.src e) := by
  grind [liftGerm, liftEdge, germSrc]
theorem liftEdge_projection  : p.onE (liftEdge p hp e) = e :=
  congrArg Prod.fst (liftGerm_spec p hp e).2

def edge   := sheet p hp a hr (D.tgt (liftEdge p hp e))

include he in
theorem lifted_edge_deck (e : D.E) :
    a.smulE (sheet p hp a hr (D.src e)) (liftEdge p hp (p.onE e)) = e := by
  have h := liftGerm_unique hp
    (x := (a.smulE (sheet p hp a hr (D.src e)) (liftEdge p hp (p.onE e)), true))
    (y := (e, true)) (by
      dsimp
      rw [a.src_smul, liftEdge_source, p.src_onE, sheet_spec]) rfl (by
      rw [he, liftEdge_projection])
  exact congrArg Prod.fst h

include he in
theorem edge_projection (e : D.E) :
    edge p hp a hr (p.onE e) = (sheet p hp a hr (D.src e))⁻¹ * sheet p hp a hr (D.tgt e) := by
  have h := congrArg (fun e => sheet p hp a hr (D.tgt e)) (lifted_edge_deck p hp a hr he e)
  rw [a.tgt_smul, sheet_deck] at h
  change sheet p hp a hr (D.src e) * edge p hp a hr (p.onE e) =
    sheet p hp a hr (D.tgt e) at h
  rw [← h]
  group

include he in
theorem read_projected_path {l : List (D.E × Bool)} {d e : D.V}
    (hl : IsPath D.src D.tgt l d e) :
    EdgeLabels.read (edge p hp a hr) (mapPath p l) =
      (sheet p hp a hr d)⁻¹ * sheet p hp a hr e := by
  rw [EdgeLabels.read_mapPath]
  exact EdgeLabels.read_potential _ (sheet p hp a hr) (edge_projection p hp a hr he) hl

include he in
theorem edge_rel (f : K.F) : EdgeLabels.read (edge p hp a hr) (K.att f) = 1 := by
  obtain ⟨g, ⟨hg, hb⟩, _⟩ := exists_unique_liftCell hp f
    (sectionV_spec p hp (K.base f)).symm
  have h := read_projected_path p hp a hr he (D.att_isLoop g)
  rw [mapPath_att, hg] at h
  simpa using h

end FiniteChains.Comb.RegularCoverLabels
