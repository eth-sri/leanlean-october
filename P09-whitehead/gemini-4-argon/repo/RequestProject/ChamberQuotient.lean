module

public import RequestProject.ChamberZPi1Base
public import RequestProject.ChamberZPoset
public import RequestProject.CoverLevelComparison
public import RequestProject.RACGSpecialParity

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]

def IsGamma (A : CommRel V) (w : CayGroup A) : Prop := phi A w = 0

theorem isGamma_one : IsGamma A (1 : CayGroup A) := by
  show phi A 1 = 0
  rw [← cword_nil A, phi_cword, parList_nil]; rfl

structure QCube (A : CommRel V) : Type u where
  spx : Finset V
  sgn : V → ZMod 2
  isSimplex : IsSimplex A spx
  sgn_eq_zero : ∀ v ∈ spx, sgn v = 0

theorem QCube.ext' {c d : QCube A} (hs : c.spx = d.spx)
    (hv : ∀ v, v ∉ d.spx → c.sgn v = d.sgn v) : c = d := by
  have hsgn : c.sgn = d.sgn := funext fun v =>
    if h : v ∈ d.spx then (c.sgn_eq_zero v (hs ▸ h)).trans (d.sgn_eq_zero v h).symm else hv v h
  cases c; cases d; cases hs; cases hsgn; rfl

instance : PartialOrder (QCube A) where
  le c d := c.spx ⊆ d.spx ∧ ∀ v, v ∉ d.spx → c.sgn v = d.sgn v
  le_refl _ := ⟨Finset.Subset.refl _, fun _ _ => rfl⟩
  le_trans _ _ _ hcd hde :=
    ⟨hcd.1.trans hde.1, fun v hv => (hcd.2 v fun h => hv (hde.1 h)).trans (hde.2 v hv)⟩
  le_antisymm _ _ hcd hdc := QCube.ext' (Finset.Subset.antisymm hcd.1 hdc.1) hcd.2

def QOld (A : CommRel V) : Type u := {c : QCube A // ¬ (c.spx = ∅ ∧ c.sgn = 0)}

def Qpos (A : CommRel V) (X : Type u) [Preorder X] (_att : NeSpx A →o X) : Type u :=
  QOld A ⊕ X

variable {att : NeSpx A →o X}

def qOld (c : QCube A) (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)) : Qpos A X att := Sum.inl ⟨c, hc⟩

def qNew (x : X) : Qpos A X att := Sum.inr x

protected def Qle : Qpos A X att → Qpos A X att → Prop
  | Sum.inl c, Sum.inl d => c.1 ≤ d.1
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr x, Sum.inl d =>
      d.1.sgn = 0 ∧ ∃ h : d.1.spx.Nonempty, x ≤ att ⟨d.1.spx, h, d.1.isSimplex⟩
  | Sum.inr x, Sum.inr y => x ≤ y

instance qposPreorder : Preorder (Qpos A X att) where
  le := Davis.Qle
  le_refl | .inl c => le_refl c.1 | .inr x => le_refl x
  le_trans
    | .inl _, .inl _, .inl _, h1, h2 => le_trans h1 h2
    | .inl _, .inl _, .inr _, _, h2 => h2.elim
    | .inl _, .inr _, _, h1, _ => h1.elim
    | .inr _, .inl d, .inl e, ⟨hd0, hne, hx⟩, hde =>
        ⟨funext fun v => if hv : v ∈ e.1.spx then e.1.sgn_eq_zero v hv
          else (hde.2 v hv).symm.trans (congrFun hd0 v),
         Finset.Nonempty.mono hde.1 hne,
         hx.trans (att.monotone (show (⟨d.1.spx, hne, d.1.isSimplex⟩ : NeSpx A) ≤
           ⟨e.1.spx, Finset.Nonempty.mono hde.1 hne, e.1.isSimplex⟩ from hde.1))⟩
    | .inr _, .inl _, .inr _, _, h2 => h2.elim
    | .inr _, .inr _, .inl _, h1, ⟨he0, hne, hy⟩ => ⟨he0, hne, h1.trans hy⟩
    | .inr _, .inr _, .inr _, h1, h2 => le_trans h1 h2

theorem qNew_monotone : Monotone (qNew (A := A) (X := X) (att := att)) := fun _ _ h => h

theorem phi_rep_eq_of_inChamber {x : CayGroup A} {p : Sph A} (h : InChamber x p) {v : V}
    (hv : v ∉ p.spx) : phi A p.rep v = phi A x v := by
  have hmul : phi A x = phi A p.rep + phi A (p.rep⁻¹ * x) := by
    simpa [mul_inv_cancel_left] using phi_mul A p.rep (p.rep⁻¹ * x)
  rw [congrFun hmul v, Pi.add_apply, phi_eq_zero_of_mem_specialSub A h (by simpa using hv), add_zero]

theorem inChamber_rep_of_le {p q : Sph A} (h : p ≤ q) : InChamber p.rep q := by
  simpa [InChamber, mul_inv_rev] using Subgroup.inv_mem _ h.2

theorem eq_of_inChamber_spx_eq {x : CayGroup A} {r r' : Sph A} (hr : InChamber x r)
    (hr' : InChamber x r') (hs : r.spx = r'.spx) : r = r' :=
  Sph.ext' ((existsUnique_shortest_coset A (commuting_of_isSimplex r.isSimplex) x).unique
    ⟨by simpa [mul_inv_rev] using Subgroup.inv_mem _ hr,
     fun s hs' => r.no_rdesc s (Finset.mem_coe.1 hs')⟩
    ⟨by simpa [hs, mul_inv_rev] using Subgroup.inv_mem _ hr',
     fun s hs' => r'.no_rdesc s (hs ▸ Finset.mem_coe.1 hs')⟩) hs

noncomputable def qProjSgn (p : Sph A) : V → ZMod 2 :=
  fun v => if v ∈ p.spx then 0 else phi A p.rep v

noncomputable def qProjCube (p : Sph A) : QCube A where
  spx := p.spx
  sgn := qProjSgn p
  isSimplex := p.isSimplex
  sgn_eq_zero v hv := by simp [qProjSgn, hv]

theorem qProjCube_sgn_of_not_mem {p : Sph A} {v : V} (hv : v ∉ p.spx) :
    (qProjCube p).sgn v = phi A p.rep v := by simp [qProjCube, qProjSgn, hv]

theorem qProjCube_eq_iff {p : Sph A} {c : QCube A} :
    qProjCube p = c ↔ p.spx = c.spx ∧ ∀ v, v ∉ c.spx → phi A p.rep v = c.sgn v :=
  ⟨by rintro rfl; exact ⟨rfl, fun _ hv => (qProjCube_sgn_of_not_mem hv).symm⟩,
   fun ⟨hs, hv⟩ => QCube.ext' hs fun v hvc =>
    (qProjCube_sgn_of_not_mem (hs ▸ hvc)).trans (hv v hvc)⟩

theorem not_isMarkedApex_of_qProjCube_eq {r : Sph A} {c : QCube A}
    (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)) (h : qProjCube r = c) :
    ¬ IsMarkedApex (IsGamma A) r := by
  rintro ⟨hemp, hrep⟩
  refine hc ⟨h ▸ hemp, funext fun v => ?_⟩
  rw [← h, qProjCube_sgn_of_not_mem (by simp [hemp])]
  exact congrFun hrep v

theorem not_vplus_qProjCube {p : Sph A} (hp : ¬ IsMarkedApex (IsGamma A) p) :
    ¬ ((qProjCube p).spx = ∅ ∧ (qProjCube p).sgn = 0) := fun ⟨hemp, hsgn⟩ =>
  hp ⟨hemp, funext fun v => by
    rw [← qProjCube_sgn_of_not_mem (by simp [show p.spx = ∅ from hemp])]; exact congrFun hsgn v⟩

noncomputable def zProj : Zpos A X (IsGamma A) att → Qpos A X att
  | Sum.inl p => qOld (qProjCube p.1) (not_vplus_qProjCube p.2)
  | Sum.inr wx => qNew wx.2

@[simp] theorem zProj_zNew (w : {w : CayGroup A // IsGamma A w}) (x : X) :
    zProj (A := A) (att := att) (zNew w x) = qNew x := rfl

theorem zProj_monotone : Monotone (zProj (A := A) (X := X) (att := att)) := by
  rintro (p | ⟨u, x⟩) (q | ⟨v, y⟩) h
  · refine ⟨h.1, fun w hw => ?_⟩
    rw [qProjCube_sgn_of_not_mem (fun hc => hw (h.1 hc)), qProjCube_sgn_of_not_mem hw]
    exact (phi_rep_eq_of_inChamber (inChamber_rep_of_le h) hw).symm
  · exact h.elim
  · refine ⟨funext fun w => ?_, h.2.1, h.2.2⟩
    by_cases hw : w ∈ q.1.spx
    · exact (qProjCube q.1).sgn_eq_zero w hw
    · rw [qProjCube_sgn_of_not_mem hw, phi_rep_eq_of_inChamber h.1 hw]
      exact congrFun u.2 w
  · exact h.2

variable [Fintype V]

theorem exists_zOld_qProjCube (c : QCube A) : ∃ p : Sph A, qProjCube p = c := by
  obtain ⟨w, hw⟩ := phi_surjective A c.sgn
  exact ⟨chamberPt w c.isSimplex, qProjCube_eq_iff.2 ⟨rfl, fun v hv => by
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber w c.isSimplex) (by simpa using hv), hw]⟩⟩

theorem zProj_surjective : Function.Surjective (zProj (A := A) (X := X) (att := att)) := by
  rintro (⟨c, hc⟩ | x)
  · obtain ⟨p, hp⟩ := exists_zOld_qProjCube c
    exact ⟨zOld p (not_isMarkedApex_of_qProjCube_eq hc hp), congrArg Sum.inl (Subtype.ext hp)⟩
  · exact ⟨zNew ⟨1, isGamma_one⟩ x, rfl⟩

end FiniteChains.Davis
