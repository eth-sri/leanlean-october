module

public import RequestProject.ChamberAttachingJ
public import RequestProject.CylinderPoset

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]

abbrev NeSpx (A : CommRel V) : Type u := {σ : Finset V // σ.Nonempty ∧ IsSimplex A σ}

def IsMarkedApex (M : CayGroup A → Prop) (p : Sph A) : Prop := p.spx = ∅ ∧ M p.rep

def Zold (A : CommRel V) (M : CayGroup A → Prop) : Type u := {p : Sph A // ¬ IsMarkedApex M p}

def Znew (A : CommRel V) (M : CayGroup A → Prop) (X : Type u) : Type u :=
  {w : CayGroup A // M w} × X

def Zpos (A : CommRel V) (X : Type u) [Preorder X] (M : CayGroup A → Prop)
    (_att : NeSpx A →o X) : Type u :=
  Zold A M ⊕ Znew A M X

variable {M : CayGroup A → Prop} {att : NeSpx A →o X}

def zOld (p : Sph A) (hp : ¬ IsMarkedApex M p) : Zpos A X M att := Sum.inl ⟨p, hp⟩

def zNew (w : {w : CayGroup A // M w}) (x : X) : Zpos A X M att := Sum.inr (w, x)

protected def Zle : Zpos A X M att → Zpos A X M att → Prop
  | Sum.inl p, Sum.inl q => p.1 ≤ q.1
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr wx, Sum.inl q =>
      InChamber wx.1.1 q.1 ∧ ∃ h : q.1.spx.Nonempty, wx.2 ≤ att ⟨q.1.spx, h, q.1.isSimplex⟩
  | Sum.inr wx, Sum.inr vy => wx.1 = vy.1 ∧ wx.2 ≤ vy.2

instance zposPreorder : Preorder (Zpos A X M att) where
  le := Davis.Zle
  le_refl | .inl p => le_refl p.1 | .inr wx => ⟨rfl, le_refl wx.2⟩
  le_trans
    | .inl _, .inl _, .inl _, h1, h2 => le_trans h1 h2
    | .inl _, .inl _, .inr _, _, h2 => h2.elim
    | .inl _, .inr _, _, h1, _ => h1.elim
    | .inr _, .inl q, .inl r, ⟨hwq, hne, hx⟩, hqr =>
        ⟨inChamber_of_le hqr hwq, Finset.Nonempty.mono hqr.1 hne,
         hx.trans (att.monotone (show (⟨q.1.spx, hne, q.1.isSimplex⟩ : NeSpx A) ≤
           ⟨r.1.spx, Finset.Nonempty.mono hqr.1 hne, r.1.isSimplex⟩ from hqr.1))⟩
    | .inr _, .inl _, .inr _, _, h2 => h2.elim
    | .inr _, .inr _, .inl _, h1, ⟨hvr, hne, hy⟩ => ⟨h1.1 ▸ hvr, hne, h1.2.trans hy⟩
    | .inr _, .inr _, .inr _, h1, h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

def InZChamber (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl p => InChamber w p.1
  | Sum.inr vx => vx.1.1 = w

theorem spx_nonempty_of_marked {w : CayGroup A} (hw : M w) {p : Sph A}
    (hp : ¬ IsMarkedApex M p) (hpw : InChamber w p) : p.spx.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.spx with hemp | hne
  · refine (hp ⟨hemp, ?_⟩).elim
    have h1 : p.rep⁻¹ * w ∈ specialSub A (p.spx : Set V) := hpw
    rw [hemp, Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
    rwa [inv_mul_eq_one.1 h1]
  · exact hne

theorem inZChamber_of_le {w : CayGroup A} {z z' : Zpos A X M att}
    (h : z ≤ z') (hz : InZChamber w z) : InZChamber w z' := by
  rcases z with p | wx <;> rcases z' with q | wy
  · exact inChamber_of_le h hz
  · exact h.elim
  · exact hz ▸ h.1
  · exact (congrArg Subtype.val h.1).symm.trans hz

theorem exists_inZChamber (z : Zpos A X M att) : ∃ w : CayGroup A, InZChamber w z := by
  rcases z with p | wx
  exacts [⟨p.1.rep, inChamber_rep p.1⟩, ⟨wx.1.1, rfl⟩]

section

variable [Fintype V]

def ZJSet (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl p => JSet w p.1
  | Sum.inr _ => False

theorem zJSet_imp_inZChamber {w : CayGroup A} {z : Zpos A X M att} (h : ZJSet w z) :
    InZChamber w z := by
  rcases z with p | _
  exacts [h.choose_spec.2.1, h.elim]

theorem mem_earlier_zchamber_iff {w : CayGroup A} {z : Zpos A X M att} (hz : InZChamber w z) :
    (∃ v : CayGroup A, v ≠ w ∧ RACG.clen A v ≤ RACG.clen A w ∧ InZChamber v z) ↔ ZJSet w z := by
  rcases z with p | wx
  · exact mem_earlier_chamber_iff_jSet hz
  · exact ⟨fun ⟨v, hvw, _, hv⟩ => hvw (hv.symm.trans hz), False.elim⟩

theorem mem_shorter_zchamber_iff {w : CayGroup A} {z : Zpos A X M att} (hz : InZChamber w z) :
    (∃ v : CayGroup A, RACG.clen A v < RACG.clen A w ∧ InZChamber v z) ↔ ZJSet w z := by
  rcases z with p | wx
  · exact mem_shorter_chamber_iff_jSet hz
  · exact ⟨fun ⟨v, hlen, hv⟩ => (lt_irrefl _ (hv.symm.trans hz ▸ hlen)).elim, False.elim⟩

end

variable (M att) (w : CayGroup A)

abbrev ZChamber : Type u := {z : Zpos A X M att // InZChamber w z}

variable {M att w}

def zChamberRetr (hw : M w) : ZChamber M att w → ZChamber M att w
  | ⟨Sum.inl p, hp⟩ =>
      ⟨zNew ⟨w, hw⟩ (att ⟨p.1.spx, spx_nonempty_of_marked hw p.2 hp, p.1.isSimplex⟩), rfl⟩
  | ⟨Sum.inr wx, hwx⟩ => ⟨Sum.inr wx, hwx⟩

theorem zChamberRetr_mem (hw : M w) (z : ZChamber M att w) :
    ∃ x : X, (zChamberRetr hw z).1 = zNew (att := att) ⟨w, hw⟩ x := by
  rcases z with ⟨p | ⟨u, x⟩, hz⟩
  · exact ⟨att ⟨p.1.spx, spx_nonempty_of_marked hw p.2 hz, p.1.isSimplex⟩, rfl⟩
  · exact ⟨x, congrArg (fun u => Sum.inr (u, x)) (Subtype.ext hz)⟩

theorem zChamberRetr_le (hw : M w) (z : ZChamber M att w) : zChamberRetr hw z ≤ z := by
  rcases z with ⟨p | wx, hz⟩
  exacts [⟨hz, spx_nonempty_of_marked hw p.2 hz, le_rfl⟩, ⟨rfl, le_rfl⟩]

theorem zChamberRetr_monotone (hw : M w) :
    Monotone (zChamberRetr (att := att) hw) := by
  rintro ⟨p | ⟨u, x⟩, hz⟩ ⟨q | ⟨v, y⟩, hz'⟩ h
  · exact ⟨rfl, att.monotone (show (⟨p.1.spx, spx_nonempty_of_marked hw p.2 hz,
      p.1.isSimplex⟩ : NeSpx A) ≤
      ⟨q.1.spx, spx_nonempty_of_marked hw q.2 hz', q.1.isSimplex⟩ from h.1)⟩
  · exact h.elim
  · exact ⟨Subtype.ext hz, h.2.2⟩
  · exact h

end FiniteChains.Davis
