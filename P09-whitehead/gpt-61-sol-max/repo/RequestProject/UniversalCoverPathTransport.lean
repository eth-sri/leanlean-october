import Mathlib.Tactic

import RequestProject.CombPi2
import RequestProject.CombPi1Conj

/-!
# Universal-cover transport along an actual path

A path `a : x ⟶ y` gives a cellular map from the universal cover based at `y`
to the universal cover based at `x`, by prefixing `a` to every represented
path.  Its projection is the identity on every underlying cell.  The map
intertwines deck transformations by the actual conjugation `pi1Conj ha`.
No equality of base points or connectedness hypothesis is used.

-/

namespace FiniteChains.Comb


variable {K : Complex2.{u}} {x y : K.V} {a : List (K.E × Bool)}
  (ha : IsPath K.src K.tgt a x y)

variable (p : PathFrom K y)
/-- Prefix the actual path from `x` to `y` to a path starting at `y`. -/
def pathTransportP  : PathFrom K x :=
  ⟨a ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath ha]
    exact ha.append p.2⟩

theorem endpt_pathTransportP  :
    endpt K x (pathTransportP ha p).1 = endpt K y p.1 := by
  unfold FiniteChains.Comb.pathTransportP
  rw [endpt_append, endpt_eq_of_isPath ha]

/-- Prefixing descends to homotopy classes of paths. -/
def pathTransportV (c : UV K y) : UV K x :=
  Quotient.map (pathTransportP ha) (by
    intro p q hpq
    change Htpy K x (endpt K x (pathTransportP ha p).1)
      (pathTransportP ha p).1 (pathTransportP ha q).1
    rw [endpt_pathTransportP]
    exact Htpy.append_congr ha p.2 (Htpy.refl _) hpq) c

@[simp] theorem pathTransportV_mk  :
    pathTransportV ha (UV.mk p) = UV.mk (pathTransportP ha p) := rfl

@[simp] theorem endV_pathTransportV (c : UV K y) :
    endV (pathTransportV ha c) = endV c := by
  induction c using UV.ind <;> simp_all [endpt_pathTransportP]

/-- Prefixing commutes with extending a path by an edge, including the
convention that an edge with the wrong source leaves a path unchanged. -/
theorem extend_pathTransportV (eb : K.E × Bool) (c : UV K y) :
    extend eb (pathTransportV ha c) = pathTransportV ha (extend eb c) := by
  induction c using UV.ind with
  | h p =>
      have hl : (extendP eb (pathTransportP ha p)).1 =
          (pathTransportP ha (extendP eb p)).1 := by
        grind [endpt, germSrc, pathTransportP, endpt_pathTransportP, extendP]
      apply UV.sound
      
      rw [hl]
      exact Htpy.refl _

/-- Transport an edge by prefixing the path attached to its initial vertex. -/
def pathTransportE (e : UE K y) : UE K x :=
  ⟨(pathTransportV ha e.1.1, e.1.2), by rw [endV_pathTransportV]; exact e.2⟩

/-- Transport a face by prefixing the path attached to its base vertex. -/
def pathTransportF (t : UF K y) : UF K x :=
  ⟨(pathTransportV ha t.1.1, t.1.2), by rw [endV_pathTransportV]; exact t.2⟩

theorem liftGerm_pathTransportV {c : UV K y} {eb : K.E × Bool}
    (h : endV c = germSrc K.src K.tgt eb)
    (h' : endV (pathTransportV ha c) = germSrc K.src K.tgt eb) :
    liftGerm (pathTransportV ha c) eb h' =
      (pathTransportE ha (liftGerm c eb h).1, (liftGerm c eb h).2) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      aesop (add simp [extend_pathTransportV])

theorem uLiftPath_pathTransportV :
    ∀ (p : List (K.E × Bool)) (c : UV K y) (z : K.V),
      IsPath K.src K.tgt p (endV c) z →
        uLiftPath p (pathTransportV ha c) =
          (uLiftPath p c).map (fun eb => (pathTransportE ha eb.1, eb.2)) := by
  intro p
  induction p with
  | nil => intro c z _; rfl
  | cons eb p ih =>
      intro c z hp
      have h  := hp.1
      have h' : endV (pathTransportV ha c) = germSrc K.src K.tgt eb := by
        rw [endV_pathTransportV]
        exact h
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons,
        liftGerm_pathTransportV ha h h', extend_pathTransportV ha eb c,
        ih (extend eb c) z (by rw [endV_extend h]; exact hp.2)]

/-- The actual cellular change of universal-cover base along `a : x ⟶ y`. -/
noncomputable def uCoverPathTransport : Hom (uCover K y) (uCover K x) where
  onV := pathTransportV ha
  onE := pathTransportE ha
  onF := pathTransportF ha
  src_onE := fun _ => rfl
  tgt_onE := fun e => extend_pathTransportV ha (e.1.2, true) e.1.1
  base_onF := fun _ => rfl
  att_onF := by
    intro t
    
    apply uLiftPath_pathTransportV
    rw [t.2]
    exact K.att_isLoop t.1.2

theorem uCoverPathTransport_base :
    (uCoverPathTransport ha).onV (UV.base K y) =
      UV.mk ⟨a, by rw [endpt_eq_of_isPath ha]; exact ha⟩ := by
  
  apply congrArg UV.mk
  exact Subtype.ext (List.append_nil a)

/-- Prefix transport intertwines the deck actions by conjugation along the same path. -/
theorem uCoverPathTransport_deckV (γ : Pi1 K y) (c : UV K y) :
    (uCoverPathTransport ha).onV (deckV γ c) =
      deckV (pi1Conj ha γ) ((uCoverPathTransport ha).onV c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p =>
          apply UV.sound
          change Htpy K x (endpt K x (a ++ (g.1 ++ p.1)))
            (a ++ (g.1 ++ p.1)) ((a ++ g.1 ++ revPath a) ++ (a ++ p.1))
          rw [endpt_append, endpt_eq_of_isPath ha,
            endpt_append, endpt_eq_of_isPath g.2]
          have h := (htpy_revPath_append ha).congr_append (ha.append g.2) p.2
          simpa [List.append_assoc, List.nil_append] using h.symm

end FiniteChains.Comb
