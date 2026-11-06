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

universe u

variable {K : Complex2.{u}} {x y : K.V} {a : List (K.E × Bool)}
  (ha : IsPathX K a x y)

/-- Prefix the actual path from `x` to `y` to a path starting at `y`. -/
def pathTransportP (p : PathFrom K y) : PathFrom K x :=
  ⟨a ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath ha]
    exact ha.append p.2⟩

theorem endpt_pathTransportP p :
    endpt K x (pathTransportP ha p).1 = endpt K y p.1 := by
  change endpt K x (a ++ p.1) = endpt K y p.1
  rw [endpt_append, endpt_eq_of_isPath ha]

/-- Prefixing descends to homotopy classes of paths. -/
def pathTransportV (c : UV K y) : UV K x :=
  Quotient.map _ (by
    intro p q hpq
    change Htpy K x (endpt K x (pathTransportP ha p).1)
      (pathTransportP ha p).1 (pathTransportP ha q).1
    rw [endpt_pathTransportP]
    exact Htpy.append_congr ha p.2 (Htpy.refl _) hpq) c


@[simp] theorem endV_pathTransportV c :
    endV (pathTransportV ha c) = endV c := by
  induction c using UV.ind with
  | h p => exact endpt_pathTransportP ha p

/-- Prefixing commutes with extending a path by an edge, including the
convention that an edge with the wrong source leaves a path unchanged. -/
theorem extend_pathTransportV eb c :
    extend eb (pathTransportV ha c) = pathTransportV ha (extend eb c) := by
  induction c using UV.ind with
  | h p =>
      have hl : (extendP eb (pathTransportP ha p)).1 =
          (pathTransportP ha (extendP eb p)).1 := by
        by_cases h : endpt K y p.1 = gSrcX K eb
        · have h' : endpt K x (pathTransportP ha p).1 = gSrcX K eb := by
            grind [endpt_pathTransportP]
          rw [extendP_pos h']
          change (a ++ p.1) ++ [eb] = a ++ (extendP eb p).1
          rw [extendP_pos h]
          simp
        · have h' : ¬ endpt K x (pathTransportP ha p).1 = gSrcX K eb := by
            grind [endpt_pathTransportP]
          rw [extendP_neg h']
          change a ++ p.1 = a ++ (extendP eb p).1
          rw [extendP_neg h]
      apply UV.sound
      rw [hl]
      exact Htpy.refl _

/-- Transport an edge by prefixing the path attached to its initial vertex. -/
def pathTransportE (e : UE K y) : UE K x :=
  ⟨(pathTransportV ha e.1.1, e.1.2), by grind [endV_pathTransportV]⟩

/-- Transport a face by prefixing the path attached to its base vertex. -/
def pathTransportF (t : UF K y) : UF K x :=
  ⟨(pathTransportV ha t.1.1, t.1.2), by grind [endV_pathTransportV]⟩

theorem liftGerm_pathTransportV
    h
    h' :
    liftGerm (pathTransportV ha c) eb h' =
      (pathTransportE ha (liftGerm c eb h).1, (liftGerm c eb h).2) := by
  cases' eb with e b
  cases b with
  | true => rfl
  | false =>
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact Prod.ext (extend_pathTransportV ha _ c) rfl

theorem uLiftPath_pathTransportV :
    ∀ p c z,
      IsPathX K p (endV c) z →
        uLiftPath p (pathTransportV ha c) =
          (uLiftPath p c).map (fun eb => (pathTransportE ha eb.1, eb.2)) := by
  intro p
  induction p with
  | nil => simp
  | cons eb p ih =>
      intro c z hp
      have h := hp.1
      have h' : endV (pathTransportV ha c) = gSrcX K eb := by
        simp_all
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons,
        liftGerm_pathTransportV ha h h', extend_pathTransportV ha eb c,
        ih _ z (by simp_all [endV_extend h])]

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
      UV.mk ⟨a, by simp_all [endpt_eq_of_isPath ha]⟩ := by
  apply congrArg UV.mk
  exact Subtype.ext a.append_nil

/-- Prefix transport intertwines the deck actions by conjugation along the same path. -/
theorem uCoverPathTransport_deckV γ c :
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
