import Mathlib.Tactic

import RequestProject.ChamberAttachingJ
import RequestProject.CylinderPoset

/-!
# The complex `Z` of modified chambers, as an explicit poset

This file builds the object that the chamber route was missing: the poset `Z` obtained from the
poset of spherical cosets by **replacing the apex of each marked chamber by a copy of a base
poset `X`**, attached along the outer face poset of that chamber.  Everything is an honest
construction; no intersection formula is assumed as a field of a structure.

The data are

* a base preorder `X`;
* an attaching map `att : Finset V → X`, monotone for inclusion of simplices (`hatt`);  its
  restriction to the nonempty simplices of `L` is the attaching map `a_w : B_w → X` of the
  construction, the same marked map in every chamber, so the construction is equivariant;
* a predicate `M` on `W` marking the chambers to be modified (for the article, `M = Γ`).

The poset is

    Zpos = {p : Sph A | p is not a marked apex} ⊕ (Σ_{w ∈ M} X),

with the orders of the two pieces kept, no relation from an old element up into a copy of `X`,
no relation between different copies, and

    (w, x) ≤ p   ↔   p ∈ B_w  and  x ≤ att (type of p),

where `B_w` is the outer face poset of the chamber `F_w` (cells of `F_w` of nonempty type).
This is the mapping cylinder orientation of section 3 of the task: the outer end `B_w` is
upward closed and the copy of `X` is at the bottom, i.e. the opposite orientation of
`FiniteChains.Comb.CylP`; the collapse `Zpos → Sph A` is the retraction.

Proved here, for these actual subposets:

* `FiniteChains.Davis.inZChamber_of_le` — every chamber of `Zpos` is upward closed;
* `FiniteChains.Davis.exists_inZChamber_of_isChain` — every finite nonempty increasing chain of
  `Zpos` lies wholly in one chamber, so the unmixed chain-gluing lemmas apply to this
  filtration;
* `FiniteChains.Davis.inZChamber_inter_old`, `FiniteChains.Davis.eq_of_inZChamber_new` —
  intersections of distinct chambers contain only old elements and are the original
  spherical-coset intersections;
* `FiniteChains.Davis.mem_earlier_zchamber_iff` — **the attaching intersection of a chamber of
  `Zpos` with the union of the earlier chambers is exactly `J_w`** of
  `RequestProject/ChamberAttachingJ.lean` (the union of the descending mirrors), with its
  already proved contraction and simple connectedness;
* `FiniteChains.Davis.zCollapse_monotone` — collapsing each copy of `X` to the apex it replaced
  is a monotone map `Zpos → Sph A`;
* `FiniteChains.Davis.zChamberRetr_le`, `FiniteChains.Davis.zChamberRetr_monotone` — inside a
  modified chamber the retraction onto its copy of `X` is monotone and lies below the identity:
  the modified chamber is the mapping cylinder of `att`, in the dual orientation of
  `FiniteChains.Comb.CylP`.
-/

namespace FiniteChains.Davis


open RACG Mirror Comb Nerve


variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]

/-- The nonempty simplices of `L`, ordered by inclusion: the domain of the attaching map.  The
attaching map is **not** required to be defined on the empty simplex: the cone point of a
chamber is exactly what is removed.

The domain consists of the nonempty **simplices** of `L` and not of all nonempty finite sets of
vertices: the order complex of the latter poset is a cone (any finite family of finite sets has
an upper bound, namely their union), so an attaching map defined on it would be null-homotopic
on every loop of the boundary of a chamber and could never realise a nontrivial attaching word.
This is `FiniteChains.Davis.pi1_trivial_of_directed_domain` in
`RequestProject/ChamberAttachingTrivial.lean`. -/
abbrev NeSpx (A : CommRel V)  := {σ : Finset V // σ.Nonempty ∧ IsSimplex A σ}

/-- A cell of the model is a **marked apex** if it is the apex `{w}` of a chamber that is to be
modified. -/
def IsMarkedApex (M : CayGroup A → Prop) (p : Sph A)  := p.spx = ∅ ∧ M p.rep

/-- The cells of the model that are retained: everything but the marked apexes. -/
def Zold (A : CommRel V) (M : CayGroup A → Prop)  := {p : Sph A // ¬ IsMarkedApex M p}

/-- The adjoined copies of the base poset, one for each marked chamber. -/
def Znew (A : CommRel V) (M : CayGroup A → Prop) (X : Type u)  :=
  {w : CayGroup A // M w} × X

/-- **The poset `Z` of modified chambers.** -/
def Zpos (A : CommRel V) (X : Type u) [Preorder X] (M : CayGroup A → Prop)
    (_att : NeSpx A →o X)  :=
  Zold A M ⊕ Znew A M X

variable {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- The old cells of `Z`. -/
def zOld (p : Sph A) (hp : ¬ IsMarkedApex M p) : Zpos A X M att := Sum.inl ⟨p, hp⟩

/-- The new cells of `Z`: the elements of the copy of `X` replacing the apex of the chamber
`F_w`. -/
def zNew (w : {w : CayGroup A // M w}) (x : X) : Zpos A X M att := Sum.inr (w, x)

/-- The order of `Z`. -/
protected def Zle : Zpos A X M att → Zpos A X M att → Prop
  | Sum.inl p, Sum.inl q => p.1 ≤ q.1
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr wx, Sum.inl q =>
      InChamber wx.1.1 q.1 ∧ ∃ h : q.1.spx.Nonempty, wx.2 ≤ att ⟨q.1.spx, h, q.1.isSimplex⟩
  | Sum.inr wx, Sum.inr vy => wx.1 = vy.1 ∧ wx.2 ≤ vy.2

instance zposPreorder : Preorder (Zpos A X M att) where
  le := Davis.Zle
  le_refl z := by
    aesop (add simp [FiniteChains.Davis.Zle])
  le_trans z z' z'' hzz' hz'z'' := by
    cases z with
    | inl p =>
        cases z' with
        | inl q =>
            cases z'' <;> grind [FiniteChains.Davis.Zle]
        | inr wy => exact hzz'.elim
    | inr wx =>
        cases z' with
        | inl q =>
            cases z'' with
            | inl r =>
                obtain ⟨hne, hx⟩ := hzz'.2
                refine ⟨inChamber_of_le hz'z'' hzz'.1,
                  Finset.Nonempty.mono hz'z''.1 hne, ?_⟩
                exact le_trans hx (att.monotone (show (⟨q.1.spx, hne, q.1.isSimplex⟩ : NeSpx A) ≤
                  ⟨r.1.spx, Finset.Nonempty.mono hz'z''.1 hne, r.1.isSimplex⟩ from hz'z''.1))
            | inr wy => exact hz'z''.elim
        | inr wy =>
            cases z'' <;> grind [FiniteChains.Davis.Zle]





/-! ### The chambers of `Z` -/

/-- **The chambers of `Z`.**  For a marked `w` this is the modified chamber (the copy of `X`
together with the outer face poset `B_w`); for an unmarked `w` it is the ordinary chamber. -/
def InZChamber (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl p => InChamber w p.1
  | Sum.inr vx => vx.1.1 = w

/-- The old cells of the chamber of a marked `w` all have nonempty type: the apex was removed. -/
theorem spx_nonempty_of_marked {w : CayGroup A} (hw : M w) {p : Sph A}
    (hp : ¬ IsMarkedApex M p) (hpw : InChamber w p) : p.spx.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.spx with hemp | hne
  · refine absurd ?_ hp
    refine ⟨hemp, ?_⟩
    have h1 : p.rep⁻¹ * w ∈ specialSub A (p.spx : Set V) := hpw
    rw [hemp, Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
    rw [inv_mul_eq_one.1 h1]
    exact hw
  · exact hne

/-- **Every chamber of `Z` is upward closed.** -/
theorem inZChamber_of_le {w : CayGroup A} {z z' : Zpos A X M att}
    (h : z ≤ z') (hz : InZChamber w z) : InZChamber w z' := by
  cases z with
  | inl p =>
      cases z' with
      | inl q => exact inChamber_of_le h hz
      | inr wy => exact h.elim
  | inr wx =>
      cases z' with
      | inl q =>
          show InChamber w q.1
          rw [← hz]
          exact h.1
      | inr wy =>
          show wy.1.1 = w
          rw [← hz, h.1]

/-- Every element of `Z` lies in a chamber. -/
theorem exists_inZChamber (z : Zpos A X M att) : ∃ w : CayGroup A, InZChamber w z := by
  cases z with
  | inl p => exact ⟨p.1.rep, inChamber_rep p.1⟩
  | inr wx => exact ⟨wx.1.1, rfl⟩

/-! ### Intersections of chambers -/

/-- **A new cell lies in only one chamber.** -/
theorem eq_of_inZChamber_new {w v : CayGroup A} {u : {w : CayGroup A // M w}} {x : X}
    (hw : InZChamber (att := att) w (zNew u x)) (hv : InZChamber (att := att) v (zNew u x)) :
    w = v := by
  rw [← hw, ← hv]

section

variable [Fintype V]

/-- **The attaching subcomplex of the chamber of `w` inside `Z`**: the old cells of `J_w`.  The
new cells — the copy of `X` — never belong to it. -/
def ZJSet (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl p => JSet w p.1
  | Sum.inr _ => False

variable {w : CayGroup A}
  {z : Zpos A X M att}
theorem zJSet_imp_inZChamber   (h : ZJSet w z) :
    InZChamber w z := by
  cases z with
  | inl p => exact h.choose_spec.2.1
  | inr wx => exact h.elim

/-- **The attaching intersection of a chamber of `Z`.**  A cell of the chamber of `w` lies in
some other chamber of `Z` of length at most that of `w` exactly when it is an old cell of
`J_w = ⋃_{s ∈ D(w)} (F_s)_w`.  In particular the new cells — the copy of `X` — are attached
along nothing but `J_w`, and the intersection is the already-studied contractible subcomplex. -/
theorem mem_earlier_zchamber_iff   (hz : InZChamber w z) :
    (∃ v : CayGroup A, v ≠ w ∧ RACG.clen A v ≤ RACG.clen A w ∧ InZChamber v z) ↔ ZJSet w z := by
  cases z with
  | inl p =>
      classical solve_by_elim (transparency := .default) [FiniteChains.Davis.mem_earlier_chamber_iff_jSet]
  | inr wx =>
      constructor
      · rintro ⟨v, hvw, -, hv⟩
        exact absurd (eq_of_inZChamber_new hv hz) hvw
      · intro h
        exact h.elim

/-- The same intersection formula with strictly shorter chambers. -/
theorem mem_shorter_zchamber_iff   (hz : InZChamber w z) :
    (∃ v : CayGroup A, RACG.clen A v < RACG.clen A w ∧ InZChamber v z) ↔ ZJSet w z := by
  cases z with
  | inl p =>
      classical solve_by_elim (transparency := .default) [FiniteChains.Davis.mem_shorter_chamber_iff_jSet]
  | inr wx =>
      constructor
      · rintro ⟨v, hlen, hv⟩
        have  := eq_of_inZChamber_new hv hz
        subst this
        omega
      · intro h
        exact h.elim

end

/-! ### Collapsing the copies of the base -/

/-! ### The modified chamber is the mapping cylinder of `att` -/

section

variable (M att) (w : CayGroup A)

/-- The modified chamber of `w`, as a subposet of `Z`. -/
abbrev ZChamber  := {z : Zpos A X M att // InZChamber w z}

variable {M att w}

variable (hw : M w)
/-- The retraction of the modified chamber onto its copy of `X`: an old cell of type `σ` goes to
`att σ`, a new cell stays where it is. -/
def zChamberRetr  : ZChamber M att w → ZChamber M att w := fun z =>
  match z with
  | ⟨Sum.inl p, hp⟩ =>
      ⟨zNew ⟨w, hw⟩ (att ⟨p.1.spx, spx_nonempty_of_marked hw p.2 hp, p.1.isSimplex⟩), rfl⟩
  | ⟨Sum.inr wx, hwx⟩ => ⟨Sum.inr wx, hwx⟩

/-- The retraction lands in the copy of `X`. -/
theorem zChamberRetr_mem  (z : ZChamber M att w) :
    ∃ x : X, (zChamberRetr hw z).1 = zNew (att := att) ⟨w, hw⟩ x := by
  rcases z with ⟨p | ⟨u, x⟩, hz⟩
  · aesop
  · refine ⟨x, ?_⟩
    show Sum.inr (u, x) = Sum.inr ((⟨w, hw⟩ : {w : CayGroup A // M w}), x)
    have hu : u = (⟨w, hw⟩ : {w : CayGroup A // M w}) := Subtype.ext hz
    rw [hu]

/-- **The retraction lies below the identity**: this is the mapping cylinder identity `i r ≤ id`
of the chosen orientation, and it turns the prism operator into a chain homotopy. -/
theorem zChamberRetr_le  (z : ZChamber M att w) : zChamberRetr hw z ≤ z := by
  rcases z with ⟨p | wx, hz⟩
  · exact ⟨hz, spx_nonempty_of_marked hw p.2 hz, le_refl _⟩
  · exact ⟨rfl, le_refl _⟩

/-- The retraction is monotone. -/
theorem zChamberRetr_monotone  :
    Monotone (zChamberRetr (att := att) hw) := by
  rintro ⟨p | ⟨u, x⟩, hz⟩ ⟨q | ⟨v, y⟩, hz'⟩ h
  · classical solve_by_elim (transparency := .default) (maxDepth := 10) [And.intro, rfl, OrderHom.monotone, FiniteChains.Davis.spx_nonempty_of_marked, Subtype.property, FiniteChains.Davis.Sph.isSimplex, And.left, rfl]
  · exact h.elim
  · obtain ⟨hne, hx⟩ := h.2
    exact ⟨Subtype.ext hz, hx⟩
  · exact h

end

end FiniteChains.Davis

