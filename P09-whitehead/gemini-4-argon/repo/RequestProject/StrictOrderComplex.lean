module

public import RequestProject.OrderComplexGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
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
  att_isLoop _ := ⟨rfl, rfl, rfl, rfl⟩

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

open Classical in
def normalizeOrdGerm (e : (orderCx P).E × Bool) : List ((strictOrderCx P).E × Bool) :=
  if h : e.1.1.1 = e.1.1.2 then [] else [(⟨e.1.1, lt_of_le_of_ne e.1.2 h⟩, e.2)]

def normalizeOrdPath (p : List ((orderCx P).E × Bool)) :
    List ((strictOrderCx P).E × Bool) := p.flatMap normalizeOrdGerm

theorem normalizeOrdGerm_isPath (e : (orderCx P).E × Bool) :
    IsPath (strictOrderCx P).src (strictOrderCx P).tgt (normalizeOrdGerm e)
      (germSrc (orderCx P).src (orderCx P).tgt e) (germTgt (orderCx P).src (orderCx P).tgt e) := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · rcases e with ⟨e, false | true⟩ <;> [exact h.symm; exact h]
  · exact isPath_single _

theorem normalizeOrdPath_isPath : ∀ {p : List ((orderCx P).E × Bool)} {a b : P},
    IsPath (orderCx P).src (orderCx P).tgt p a b →
    IsPath (strictOrderCx P).src (strictOrderCx P).tgt (normalizeOrdPath p) a b
  | [], _, _, hp => hp
  | e :: _, _, _, ⟨rfl, hp⟩ => (normalizeOrdGerm_isPath e).append (normalizeOrdPath_isPath hp)

theorem strictOrderCx_isConnected (h : IsConnected (orderCx P)) : IsConnected (strictOrderCx P) :=
  fun a b => let ⟨p, hp⟩ := h a b; ⟨normalizeOrdPath p, normalizeOrdPath_isPath hp⟩

theorem htpy_ordSelf_nil (a : P) : Htpy (orderCx P) a a [ordPos (le_refl a)] [] := by
  let e : Loop (orderCx P) a := ⟨[ordPos (le_refl a)], isPath_ordPos _⟩
  have hmul : Pi1.mk e * Pi1.mk e = Pi1.mk e :=
    Quotient.sound (htpy_orderCx_tri (le_refl a) (le_refl a))
  have hone : Pi1.mk e = 1 := mul_eq_left.mp hmul
  exact Quotient.exact hone

theorem normalizeOrdGerm_htpy (e : (orderCx P).E × Bool) :
    Htpy (orderCx P) (germSrc (orderCx P).src (orderCx P).tgt e)
      (germTgt (orderCx P).src (orderCx P).tgt e)
      (mapPath (strictOrderIncl P) (normalizeOrdGerm e)) [e] := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · obtain ⟨⟨⟨a, b⟩, hab⟩, false | true⟩ := e <;> change a = b at h <;> subst b
    · simpa [mapPath, revPath, revGerm, ordPos, ordNeg, orderCx] using
        (htpy_revPath (isPath_ordPos (le_refl a)) (htpy_ordSelf_nil a)).symm
    · exact (htpy_ordSelf_nil a).symm
  · exact Htpy.refl _

theorem normalizeOrdPath_htpy : ∀ {p : List ((orderCx P).E × Bool)} {a b : P},
    IsPath (orderCx P).src (orderCx P).tgt p a b →
    Htpy (orderCx P) a b (mapPath (strictOrderIncl P) (normalizeOrdPath p)) p
  | [], _, _, _ => Htpy.refl _
  | e :: p, _, _, ⟨rfl, hp⟩ => by
      change Htpy (orderCx P) _ _
        (mapPath (strictOrderIncl P) (normalizeOrdGerm e ++ normalizeOrdPath p)) ([e] ++ p)
      rw [mapPath_append]
      exact Htpy.append_congr (isPath_mapPath (strictOrderIncl P) (normalizeOrdGerm_isPath e))
        (isPath_mapPath (strictOrderIncl P) (normalizeOrdPath_isPath hp))
        (normalizeOrdGerm_htpy e) (normalizeOrdPath_htpy hp)

@[simp] theorem normalizeOrdPath_append (p q : List ((orderCx P).E × Bool)) :
    normalizeOrdPath (p ++ q) = normalizeOrdPath p ++ normalizeOrdPath q := by
  simp [normalizeOrdPath]

theorem normalizeOrdPath_step {a b : P} {l l' : List ((orderCx P).E × Bool)}
    (h : Step (orderCx P) a b l l') :
    Htpy (strictOrderCx P) a b (normalizeOrdPath l) (normalizeOrdPath l') := by
  classical
  obtain ⟨hl, _, hc⟩ := h
  rcases hc with ⟨p, q, e, rfl, rfl⟩ | ⟨p, q, f, rfl, rfl⟩
  · obtain ⟨v, hp, rfl, hr⟩ := isPath_append_iff.mp hl
    have hq : IsPath (orderCx P).src (orderCx P).tgt q (germSrc (orderCx P).src (orderCx P).tgt e) b := by
      simpa only [germTgt_revGerm (X := orderCx P)] using hr.2
    have hrev : normalizeOrdGerm (revGerm e) = revPath (normalizeOrdGerm e) := by
      unfold normalizeOrdGerm; simp only [revGerm]; split_ifs <;> simp [revPath, revGerm]
    simpa only [normalizeOrdPath_append, normalizeOrdPath, List.flatMap_append, List.flatMap_cons,
      hrev, List.append_assoc, List.append_nil] using
      (htpy_append_revPath (normalizeOrdGerm_isPath e)).congr_append
        (normalizeOrdPath_isPath hp) (normalizeOrdPath_isPath hq)
  · rw [List.append_assoc] at hl
    obtain ⟨v, hp, hh⟩ := isPath_append_iff.mp hl
    obtain rfl : v = (orderCx P).base f := hh.1
    have hq : IsPath (orderCx P).src (orderCx P).tgt q ((orderCx P).base f) b := hh.2.2.2
    have htri : Htpy (strictOrderCx P) ((orderCx P).base f) ((orderCx P).base f)
        (normalizeOrdPath ((orderCx P).att f)) [] := by
      obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := f
      by_cases he : a = b
      · subst b
        by_cases hf : a = c
        · subst c; simpa [orderCx, normalizeOrdPath, normalizeOrdGerm] using Htpy.refl []
        · simpa [strictOrderCx, orderCx, normalizeOrdPath, normalizeOrdGerm, hf, revPath, revGerm] using
            htpy_append_revPath (isPath_single (X := strictOrderCx P) (⟨(a, c), lt_of_le_of_ne hbc hf⟩, true))
      · by_cases hf : b = c
        · subst c
          simpa [strictOrderCx, orderCx, normalizeOrdPath, normalizeOrdGerm, he, revPath, revGerm] using
            htpy_append_revPath (isPath_single (X := strictOrderCx P) (⟨(a, b), lt_of_le_of_ne hab he⟩, true))
        · have hac : a ≠ c := ((lt_of_le_of_ne hab he).trans (lt_of_le_of_ne hbc hf)).ne
          let t : (strictOrderCx P).F := ⟨(a, b, c), lt_of_le_of_ne hab he, lt_of_le_of_ne hbc hf⟩
          simpa [t, strictOrderCx, orderCx, normalizeOrdPath, normalizeOrdGerm, he, hf, hac] using
            (Htpy.of_step ⟨(strictOrderCx P).att_isLoop t, rfl, Or.inr ⟨[], [], t, rfl, rfl⟩⟩ :
              Htpy (strictOrderCx P) a a ((strictOrderCx P).att t) [])
    simpa only [normalizeOrdPath_append (P := P), List.append_assoc, List.nil_append] using
      htri.congr_append (normalizeOrdPath_isPath hp) (normalizeOrdPath_isPath hq)

def strictOrderPi1Equiv (a : P) :
    Pi1 (strictOrderCx P) a ≃* Pi1 (orderCx P) a where
  toFun := pi1Map (strictOrderIncl P) a
  invFun := Quotient.map (fun p => ⟨normalizeOrdPath p.1, normalizeOrdPath_isPath p.2⟩) fun _ _ h => by
    have hhtpy {l l'} (h : Htpy (orderCx P) a a l l') :
        Htpy (strictOrderCx P) a a (normalizeOrdPath l) (normalizeOrdPath l') := by
      induction h with
      | refl => exact Htpy.refl _
      | tail _ hs ih => exact ih.trans (hs.elim normalizeOrdPath_step fun hs => (normalizeOrdPath_step hs).symm)
    exact hhtpy h
  left_inv z := by
    induction z using Quotient.inductionOn with | h p =>
    refine Quotient.sound ?_
    change Htpy (strictOrderCx P) a a (normalizeOrdPath (mapPath (strictOrderIncl P) p.1)) p.1
    have hmap (l : List ((strictOrderCx P).E × Bool)) :
        normalizeOrdPath (mapPath (strictOrderIncl P) l) = l := by
      induction l with
      | nil => rfl
      | cons e l ih =>
          change normalizeOrdGerm ((strictOrderIncl P).onE e.1, e.2) ++
            normalizeOrdPath (mapPath (strictOrderIncl P) l) = e :: l
          rw [ih]
          classical simp [normalizeOrdGerm, strictOrderIncl, e.1.2.ne]
    rw [hmap]
  right_inv z := by
    induction z using Quotient.inductionOn with | h p => exact Quotient.sound (normalizeOrdPath_htpy p.2)
  map_mul' := (pi1Map (strictOrderIncl P) a).map_mul

variable {Q : Type u} [PartialOrder Q]

def strictOrderCxMap (f : P → Q) (hf : StrictMono f) :
    Hom (strictOrderCx P) (strictOrderCx Q) where
  onV := f
  onE e := ⟨(f e.1.1, f e.1.2), hf e.2⟩
  onF t := ⟨(f t.1.1, f t.1.2.1, f t.1.2.2), hf t.2.1, hf t.2.2⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl
