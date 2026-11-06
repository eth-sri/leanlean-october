import RequestProject.OrderComplexGluing
import RequestProject.Tac
noncomputable section


/-! The genuine simplicial two-skeleton of a partial order: no degenerate edges or triangles. -/

bwd

namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

def StrictOrdEdge := {p : P × P // p.1 < p.2}
def StrictOrdTri := {p : P × P × P // p.1 < p.2.1 ∧ p.2.1 < p.2.2}

def strictOrderCx : Complex2.{u} where
  V := P
  E := StrictOrdEdge P
  F := StrictOrdTri P
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t := [((⟨(t.1.1, t.1.2.1), t.2.1⟩ : StrictOrdEdge P), true),
    ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : StrictOrdEdge P), true),
    ((⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩ : StrictOrdEdge P), false)]
  att_isLoop := fun _ => ⟨rfl, rfl, rfl, rfl⟩

/-- The inclusion of nondegenerate simplices into the unnormalized cellular model. -/
def strictOrderIncl : Hom (strictOrderCx P) (orderCx P) where
  onV := id
  onE e := ⟨e.1, e.2.le⟩
  onF t := ⟨t.1, t.2.1.le, t.2.2.le⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

instance [Finite P] : Finite (strictOrderCx P).E :=
  inferInstanceAs (Finite {p : P × P // p.1 < p.2})
instance [Finite P] : Finite (strictOrderCx P).F :=
  inferInstanceAs (Finite {p : P × P × P // p.1 < p.2.1 ∧ p.2.1 < p.2.2})

variable {P}

/-- Erase a degenerate germ, retaining each genuine edge with its orientation. -/
def normalizeOrdGerm (e : (orderCx P).E × Bool) :
    List ((strictOrderCx P).E × Bool) := by
  classical
  exact if h : e.1.1.1 = e.1.1.2 then [] else
    [(⟨e.1.1, lt_of_le_of_ne e.1.2 h⟩, e.2)]

def normalizeOrdPath (p : List ((orderCx P).E × Bool)) := p.flatMap normalizeOrdGerm

theorem normalizeOrdGerm_isPath e :
    IsPathX (strictOrderCx P) (normalizeOrdGerm e)
      (gSrcX (orderCx P) e)
      (gTgtX (orderCx P) e) := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · cases' e with e b
    cases b with
    | false => exact h.symm
    | true => exact h
  tauto

/-- Normalizing an edge path preserves both endpoints. -/
theorem normalizeOrdPath_isPath {a b : P}
    (hp : IsPathX (orderCx P) p a b) :
    IsPathX (strictOrderCx P) (normalizeOrdPath p) a b := by
  induction p generalizing a with
  | nil => exact hp
  | cons e p ih =>
    cases' hp with ha hp
    subst a
    exact (normalizeOrdGerm_isPath e).append (ih hp)

/-- Removing degenerate simplices preserves connectedness. -/
theorem strictOrderCx_isConnected (h : IsConnected (orderCx P)) :
    IsConnected (strictOrderCx P) := by
  intro a b
  cases' h a b with p hp
  exact ⟨normalizeOrdPath p, normalizeOrdPath_isPath hp⟩

/-- The degenerate loop edge is null-homotopic, by its triangular relation. -/
theorem htpy_ordSelf_nil (a : P) :
    Htpy (orderCx P) a a [ordPos (le_refl a)] [] := by
  let e : Loop (orderCx P) a := ⟨[ordPos (le_refl a)], isPath_ordPos _⟩
  have hmul : Pi1.mk e * Pi1.mk e = Pi1.mk e :=
    Quotient.sound (htpy_orderCx_tri _ _)
  have hone : Pi1.mk e = 1 := by simp_all
  exact Quotient.exact hone

/-- The normalized single-germ path has the same homotopy class in the weak model. -/
theorem normalizeOrdGerm_htpy e :
    Htpy (orderCx P)
      (gSrcX (orderCx P) e)
      (gTgtX (orderCx P) e)
      (mapPath (strictOrderIncl P) (normalizeOrdGerm e)) [e] := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · obtain ⟨⟨⟨a, b⟩, hab⟩, o⟩ := e
    change a = b at h
    subst b
    cases o with
    | false =>
      have he := htpy_revPath (by aesop) (htpy_ordSelf_nil a)
      simpa [mapPath, revPath, revGerm, ordPos, ordNeg, Bool.not, orderCx] using he.symm
    | true => exact (htpy_ordSelf_nil a).symm
  tauto

/-- Erasing degenerate edges does not change an edge path's homotopy class. -/
theorem normalizeOrdPath_htpy {a b : P}
    (hp : IsPathX (orderCx P) p a b) :
    Htpy (orderCx P) a b (mapPath (strictOrderIncl P) (normalizeOrdPath p)) p := by
  induction p generalizing a with
  | nil => exact Htpy.refl _
  | cons e p ih =>
    cases' hp with ha hp
    subst a
    change Htpy (orderCx P) _ _
      (mapPath (strictOrderIncl P) (normalizeOrdGerm e ++ normalizeOrdPath p)) ([e] ++ p)
    rw [mapPath_append]
    exact Htpy.append_congr
      (isPath_mapPath _ (normalizeOrdGerm_isPath e))
      (isPath_mapPath _ (normalizeOrdPath_isPath hp))
      (normalizeOrdGerm_htpy e) (ih hp)

@[simp] theorem normalizeOrdPath_append (p q : List ((orderCx P).E × Bool)) :
    normalizeOrdPath (p ++ q) = normalizeOrdPath p ++ normalizeOrdPath q := by
  simp [normalizeOrdPath]

theorem normalizeOrdGerm_rev (e : (orderCx P).E × Bool) :
    normalizeOrdGerm (revGerm e) = revPath (normalizeOrdGerm e) := by
  classical
  unfold normalizeOrdGerm
  simp [revGerm]
  aesop

/-- Each unnormalized triangular relation becomes a genuine triangular relation or a backtrack. -/
theorem normalizeOrdTri_nullhomotopic f :
    Htpy (strictOrderCx P) ((orderCx P).base f) ((orderCx P).base f)
      (normalizeOrdPath ((orderCx P).att f)) [] := by
  classical
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := f
  by_cases he : a = b
  · subst b
    by_cases hf : a = c
    · subst c
      simpa [orderCx, normalizeOrdPath, normalizeOrdGerm] using
        (Htpy.refl (X := strictOrderCx P) (a := a) (b := a) [])
    · have hg : IsPathX (strictOrderCx P)
          [(⟨(a, c), lt_of_le_of_ne hbc hf⟩, true)] a c := by tauto
      simpa [orderCx, normalizeOrdPath, normalizeOrdGerm, hf, revPath, revGerm] using
        htpy_append_revPath hg
  · by_cases hf : b = c
    · subst c
      have hg : IsPathX (strictOrderCx P)
          [(⟨(a, b), lt_of_le_of_ne hab he⟩, true)] a b := by tauto
      simpa [orderCx, normalizeOrdPath, normalizeOrdGerm, he, revPath, revGerm] using
        htpy_append_revPath hg
    · have hac : a ≠ c := by grind
      let t : (strictOrderCx P).F := ⟨(a, b, c), lt_of_le_of_ne hab he, lt_of_le_of_ne hbc hf⟩
      have ht : Htpy _ a a ((strictOrderCx P).att t) [] :=
        Htpy.of_step ⟨(strictOrderCx P).att_isLoop t, rfl,
          Or.inr (by simp)⟩
      simpa [t, strictOrderCx, orderCx, normalizeOrdPath, normalizeOrdGerm, he, hf, hac] using ht

/-- Normalize an elementary cancellation while retaining its endpoints. -/
theorem normalizeOrdPath_step {a b : P} {l l'}
    (h : Step (orderCx P) a b l l') :
    Htpy (strictOrderCx P) a b (normalizeOrdPath l) (normalizeOrdPath l') := by
  obtain ⟨hl, _, hc⟩ := h
  rcases hc with ⟨p, q, e, rfl, rfl⟩ | ⟨p, q, f, rfl, rfl⟩
  · obtain ⟨v, hp, hh⟩ := isPath_append_iff.mp hl
    cases' hh with hv hr
    subst v
    have hq : IsPathX (orderCx P) q
        (gSrcX (orderCx P) e) b := by
      simp_all
    have he := htpy_append_revPath (normalizeOrdGerm_isPath e)
    have ht := he.congr_append (normalizeOrdPath_isPath hp) (normalizeOrdPath_isPath hq)
    simp_all [normalizeOrdPath_append, normalizeOrdPath, List.flatMap_append, List.flatMap_cons, normalizeOrdGerm_rev, List.append_assoc, List.append_nil]
  · rw [List.append_assoc] at hl
    obtain ⟨v, hp, hh⟩ := isPath_append_iff.mp hl
    have hv := hh.1
    subst v
    have hq := hh.2.2.2
    have ht := (normalizeOrdTri_nullhomotopic f).congr_append
      (normalizeOrdPath_isPath hp) (normalizeOrdPath_isPath hq)
    simp_all

/-- Normalization preserves edge-path homotopy. -/
theorem normalizeOrdPath_homotopic {a b : P} {p q}
    (h : Htpy (orderCx P) a b p q) :
    Htpy (strictOrderCx P) a b (normalizeOrdPath p) (normalizeOrdPath q) := by
  induction h with
  | refl => exact Htpy.refl _
  | tail _ hs ih =>
    rcases hs with hs | hs
    · exact ih.trans (normalizeOrdPath_step hs)
    · exact ih.trans (normalizeOrdPath_step hs).symm

/-- Normalization on edge-loop classes. -/
def strictPi1Normalize (a : P) : Pi1 (orderCx P) a →* Pi1 (strictOrderCx P) a where
  toFun := Quotient.map (fun p =>
    ⟨normalizeOrdPath p.1, normalizeOrdPath_isPath p.2⟩)
    (fun _ _ h => normalizeOrdPath_homotopic h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    apply Quotient.sound
    simp

theorem normalizeOrdGerm_strict e :
    normalizeOrdGerm ((strictOrderIncl P).onE e.1, e.2) = [e] := by
  classical
  have hn := e.1.2.ne
  simp [normalizeOrdGerm, strictOrderIncl, hn]

theorem normalizeOrdPath_map_strict p :
    normalizeOrdPath (mapPath (strictOrderIncl P) p) = p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change normalizeOrdGerm ((strictOrderIncl P).onE e.1, e.2) ++
      normalizeOrdPath (mapPath (strictOrderIncl P) p) = e :: p
    rw [normalizeOrdGerm_strict, ih]
    rfl

/-- The genuine simplicial two-skeleton has exactly the same edge-path fundamental group
as the weak-chain model. No group comparison is supplied as a hypothesis. -/
def strictOrderPi1Equiv (a : P) :
    Pi1 (strictOrderCx P) a ≃* Pi1 (orderCx P) a where
  toFun := pi1Map (strictOrderIncl P) a
  invFun := strictPi1Normalize a
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      simp [normalizeOrdPath_map_strict]
  right_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h p => exact Quotient.sound (normalizeOrdPath_htpy p.2)
  map_mul' := (pi1Map (strictOrderIncl P) a).map_mul

section Maps
variable {Q : Type u} [PartialOrder Q]

/-- A strict monotone map induces a cellular map on genuine simplicial two-skeleta. -/
def strictOrderCxMap (f : P → Q) (hf : StrictMono f) :
    Hom (strictOrderCx P) (strictOrderCx Q) where
  onV := f
  onE e := ⟨(f e.1.1, f e.1.2), hf e.2⟩
  onF t := ⟨(f t.1.1, f t.1.2.1, f t.1.2.2), hf t.2.1, hf t.2.2⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl
