import RequestProject.CombEdgeLabels
import RequestProject.CombCoveringLift
import RequestProject.Tac


/-! Actual group-valued sheet coordinates of a regular cellular covering.
Edge compatibility of its deck maps is recorded explicitly: the older
`IsRegular` predicate only records compatibility on vertices. A deck map
of a genuine topological covering has both properties. Unverified source. -/

noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Comb.RegularCoverLabels
universe u v
variable {D K : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)

def sectionV (v : K.V) := Classical.choose (hp.surjV v)
theorem sectionV_spec v : p.onV (sectionV p hp v) = v := Classical.choose_spec (hp.surjV v)

def sheet (d : D.V) := Classical.choose
  (hr.simply_transitive _ d (sectionV_spec p hp _))

theorem sheet_spec d : a.smulV (sheet p hp a hr d) (sectionV p hp (p.onV d)) = d :=
  (Classical.choose_spec (hr.simply_transitive _ d
    (sectionV_spec p hp _))).1

theorem sheet_unique d q
    (hq : a.smulV q (sectionV p hp (p.onV d)) = d) : q = sheet p hp a hr d :=
  (Classical.choose_spec (hr.simply_transitive _ d
    (sectionV_spec p hp _))).2 q hq

theorem sheet_deck q d :
    sheet p hp a hr (a.smulV q d) = q * sheet p hp a hr d := by
  symm
  apply sheet_unique
  rw [hr.compat, a.mul_smulV, sheet_spec]

theorem sheet_fibre_injective (hf : p.onV d = p.onV e)
    (hs : sheet p hp a hr d = sheet p hp a hr e) : d = e := by
  rw [← sheet_spec p hp a hr d, ← sheet_spec p hp a hr e, hf, hs]

def liftGerm (e : K.E) := Classical.choose
  (exists_unique_liftGerm hp _
    (eb := (e, true)) (sectionV_spec p hp _).symm)

theorem liftGerm_spec e :
    gSrcX D (liftGerm p hp e) = sectionV p hp (K.src e) ∧
      (p.onE (liftGerm p hp e).1, (liftGerm p hp e).2) = (e, true) :=
  (Classical.choose_spec (exists_unique_liftGerm hp _
    (eb := (e, true)) (sectionV_spec p hp _).symm)).1

def liftEdge (e : K.E) := (liftGerm p hp e).1
theorem liftEdge_source e : D.src (liftEdge p hp e) = sectionV p hp (K.src e) := by
  have h := (liftGerm_spec p hp e).1
  have hb := congrArg Prod.snd (liftGerm_spec p hp e).2
  simp_all [liftEdge, germSrc, hb, if_true]
theorem liftEdge_projection e : p.onE (liftEdge p hp e) = e :=
  congrArg Prod.fst (liftGerm_spec p hp e).2

def edge (e : K.E) := sheet p hp a hr (D.tgt (liftEdge p hp e))

include he in
theorem lifted_edge_deck (e : D.E) :
    a.smulE (sheet p hp a hr (D.src e)) (liftEdge p hp (p.onE e)) = e := by
  have h := liftGerm_unique hp
    (x := (a.smulE (sheet p hp a hr (D.src e)) (liftEdge p hp (p.onE e)), true))
    (y := (e, true)) (by
      simp [a.src_smul, liftEdge_source, p.src_onE, sheet_spec]) rfl (by
      rw [he, liftEdge_projection])
  simp_all

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
    (hl : IsPathX D l d e) :
    EdgeLabels.read (edge p hp a hr) (mapPath p l) =
      (sheet p hp a hr d)⁻¹ * sheet p hp a hr e := by
  rw [EdgeLabels.read_mapPath]
  exact EdgeLabels.read_potential _ _ (edge_projection p hp a hr he) hl

include he in
theorem edge_rel (f : K.F) : EdgeLabels.read (edge p hp a hr) (K.att f) = 1 := by
  obtain ⟨g, ⟨hg, hb⟩, _⟩ := exists_unique_liftCell hp f
    (sectionV_spec p hp _).symm
  have h := read_projected_path p hp a hr he (D.att_isLoop g)
  simp_all [mapPath_att, hg]
