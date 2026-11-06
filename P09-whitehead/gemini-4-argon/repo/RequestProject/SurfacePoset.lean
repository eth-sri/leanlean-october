module

public import RequestProject.CmpNerve

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

inductive Cell (κ ι : Type u) (M : ℕ) : Type u
  | vtx (v : κ) : Cell κ ι M
  | bed (e : ι) : Cell κ ι M
  | cvx (p : Fin M) : Cell κ ι M
  | ced (p : Fin M) : Cell κ ι M
  | dia (p : Fin M) : Cell κ ι M
  | gdi (p : Fin M) : Cell κ ι M
  | tr1 (p : Fin M) : Cell κ ι M
  | tr2 (p : Fin M) : Cell κ ι M
  | ctr : Cell κ ι M
  | rad (p : Fin M) : Cell κ ι M
  | inn (p : Fin M) : Cell κ ι M
  deriving DecidableEq, Fintype

namespace Cell

variable {κ ι : Type u} {M : ℕ}

def rk : Cell κ ι M → ℕ
  | vtx _ | cvx _ | ctr => 0
  | bed _ | ced _ | dia _ | gdi _ | rad _ => 1
  | tr1 _ | tr2 _ | inn _ => 2

end Cell

variable {κ ι : Type u} {M : ℕ} [NeZero M]

open Cell

def plt (vc : Fin M → κ) (ec : Fin M → ι) : Cell κ ι M → Cell κ ι M → Prop
  | vtx v, bed e => ∃ i, ec i = e ∧ (vc i = v ∨ vc (i + 1) = v)
  | vtx v, dia p | vtx v, gdi p | vtx v, tr2 p => vc p = v
  | cvx q, ced r | cvx q, tr2 r | cvx q, inn r => q = r ∨ q = r + 1
  | cvx q, dia r | cvx q, rad r => q = r
  | cvx q, gdi r | cvx q, tr1 r => q = r + 1
  | ctr, rad _ | ctr, inn _ => True
  | bed e, tr1 p => e = ec p
  | ced r, tr2 p | ced r, inn p | dia r, tr2 p | gdi r, tr1 p | gdi r, tr2 p => r = p
  | dia r, tr1 p => r = p + 1
  | rad r, inn p => r = p ∨ r = p + 1
  | vtx v, tr1 p => vc p = v ∨ vc (p + 1) = v
  | _, _ => False

variable {vc : Fin M → κ} {ec : Fin M → ι}

theorem rk_lt_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) : x.rk < y.rk := by
  cases x <;> cases y <;> simp_all [plt, rk]

theorem plt_irrefl (x : Cell κ ι M) : ¬ plt vc ec x x := fun h => absurd (rk_lt_of_plt h) (by omega)

omit [NeZero M] in
theorem rk_le_two (x : Cell κ ι M) : x.rk ≤ 2 := by cases x <;> simp [rk]

def Compat (vc : Fin M → κ) (ec : Fin M → ι) : Prop :=
  ∀ i j : Fin M, ec i = ec j →
    (vc i = vc j ∧ vc (i + 1) = vc (j + 1)) ∨ (vc i = vc (j + 1) ∧ vc (i + 1) = vc j)

theorem plt_trans (hc : Compat vc ec) {x y z : Cell κ ι M} (hxy : plt vc ec x y)
    (hyz : plt vc ec y z) : plt vc ec x z := by
  cases y with
  | bed e =>
      cases x <;> cases z <;> simp_all [plt]
      rcases hxy with ⟨i, hi, rfl | rfl⟩ <;> rcases hc i _ hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  | ced _ | dia _ | gdi _ | rad _ =>
      cases x <;> cases z <;> simp_all [plt]
  | vtx _ | cvx _ | ctr | tr1 _ | tr2 _ | inn _ =>
      have := rk_lt_of_plt hxy; have := rk_lt_of_plt hyz; have := rk_le_two z
      simp [rk] at * ; try omega

def SCell (_vc : Fin M → κ) (_ec : Fin M → ι) (_hc : Compat vc ec) : Type u := Cell κ ι M

instance instPartialOrderSCell (hc : Compat vc ec) : PartialOrder (SCell vc ec hc) where
  le x y := x = y ∨ plt vc ec x y
  le_refl _ := .inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | h1
    · exact hbc
    rcases hbc with rfl | h2
    · exact .inr h1
    exact .inr (plt_trans hc h1 h2)
  le_antisymm a b hab hba := by
    rcases hab with rfl | h1
    · rfl
    rcases hba with rfl | h2
    · rfl
    have := rk_lt_of_plt h1; have := rk_lt_of_plt h2; omega

instance instDecidableEqSCell [DecidableEq κ] [DecidableEq ι] (hc : Compat vc ec) :
    DecidableEq (SCell vc ec hc) := inferInstanceAs (DecidableEq (Cell κ ι M))

instance instFintypeSCell [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (hc : Compat vc ec) : Fintype (SCell vc ec hc) := inferInstanceAs (Fintype (Cell κ ι M))

variable (vc ec)

def toS (hc : Compat vc ec) (x : Cell κ ι M) : SCell vc ec hc := x

variable {vc ec}

theorem le_of_plt (hc : Compat vc ec) {x y : Cell κ ι M} (h : plt vc ec x y) :
    toS vc ec hc x ≤ toS vc ec hc y := .inr h
