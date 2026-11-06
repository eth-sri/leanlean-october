module

public import RequestProject.ConeAdjPoset
public import RequestProject.CylinderPoset
public import RequestProject.OrderCxNatHtpy

@[expose] public section

namespace FiniteChains.PresModel

open Comb

universe u

variable {α J : Type u}

theorem ordPos_congr {P : Type u} [Preorder P] {a b a' b' : P} (ha : a = a') (hb : b = b')
    (h : a ≤ b) (h' : a' ≤ b') : ordPos h = ordPos h' := by
  subst ha; subst hb; rfl

theorem ordNeg_congr {P : Type u} [Preorder P] {a b a' b' : P} (ha : a = a') (hb : b = b')
    (h : a ≤ b) (h' : a' ≤ b') : ordNeg h = ordNeg h' := by
  subst ha; subst hb; rfl

inductive Rose (α : Type u) : Type u
  | base : Rose α
  | mid (i : α) : Rose α
  | edg (i : α) (b : Bool) : Rose α

namespace Rose

protected def le : Rose α → Rose α → Prop
  | base, base => True
  | base, edg _ _ => True
  | mid i, mid i' => i = i'
  | mid i, edg i' _ => i = i'
  | edg i b, edg i' b' => i = i' ∧ b = b'
  | _, _ => False

instance : Preorder (Rose α) where
  le := Rose.le
  le_refl x := by cases x <;> simp [Rose.le]
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> simp_all [Rose.le]

@[simp] theorem base_le_edg (i : α) (b : Bool) : (base : Rose α) ≤ edg i b := trivial

@[simp] theorem mid_le_edg (i : α) (b : Bool) : (mid i : Rose α) ≤ edg i b := rfl

end Rose

inductive CPos : Type
  | cor : CPos
  | cmid : CPos
  | cedgL : CPos
  | cedgR : CPos
  deriving DecidableEq

def TCirc (_w : J → List (α × Bool)) : Type u := J × ℕ × CPos

namespace TCirc

variable (w : J → List (α × Bool))

def pt (j : J) (k : ℕ) (t : CPos) : TCirc w := (j, k, t)

def csucc (j : J) (k : ℕ) : ℕ := (k + 1) % (w j).length

protected def lt : TCirc w → TCirc w → Prop
  | (j, k, t), (j', k', t') =>
      j = j' ∧ k' < (w j).length ∧
        ((t = CPos.cor ∧ t' = CPos.cedgL ∧ k = k') ∨
         (t = CPos.cmid ∧ t' = CPos.cedgL ∧ k = k') ∨
         (t = CPos.cmid ∧ t' = CPos.cedgR ∧ k = k') ∨
         (t = CPos.cor ∧ t' = CPos.cedgR ∧ k = csucc w j k'))

protected def le (x y : TCirc w) : Prop := x = y ∨ TCirc.lt w x y

theorem lt_left_tag {x y : TCirc w} (h : TCirc.lt w x y) :
    x.2.2 = CPos.cor ∨ x.2.2 = CPos.cmid := by
  rcases h with ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
  exacts [.inl h, .inr h, .inr h, .inl h]

theorem lt_right_tag {x y : TCirc w} (h : TCirc.lt w x y) :
    y.2.2 = CPos.cedgL ∨ y.2.2 = CPos.cedgR := by
  rcases h with ⟨-, -, ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩⟩
  exacts [.inl h, .inl h, .inr h, .inr h]

instance : Preorder (TCirc w) where
  le := TCirc.le w
  le_refl _ := .inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | h1
    · exact hbc
    rcases hbc with rfl | h2
    · exact .inr h1
    rcases lt_right_tag w h1 with h | h <;> rcases lt_left_tag w h2 with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

theorem cor_le_cedgL {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j k CPos.cor ≤ pt w j k CPos.cedgL :=
  .inr ⟨rfl, hk, .inl ⟨rfl, rfl, rfl⟩⟩

theorem cmid_le_cedgL {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j k CPos.cmid ≤ pt w j k CPos.cedgL :=
  .inr ⟨rfl, hk, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩

theorem cmid_le_cedgR {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j k CPos.cmid ≤ pt w j k CPos.cedgR :=
  .inr ⟨rfl, hk, .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))⟩

theorem cor_csucc_le_cedgR {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j (csucc w j k) CPos.cor ≤ pt w j k CPos.cedgR :=
  .inr ⟨rfl, hk, .inr (.inr (.inr ⟨rfl, rfl, rfl⟩))⟩

end TCirc

variable (w : J → List (α × Bool))

def aFun : TCirc w → Rose α
  | (_, _, CPos.cor) => Rose.base
  | (j, k, CPos.cmid) =>
      match (w j)[k]? with
      | some p => Rose.mid p.1
      | none => Rose.base
  | (j, k, CPos.cedgL) =>
      match (w j)[k]? with
      | some p => Rose.edg p.1 (!p.2)
      | none => Rose.base
  | (j, k, CPos.cedgR) =>
      match (w j)[k]? with
      | some p => Rose.edg p.1 p.2
      | none => Rose.base

theorem aFun_cmid_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (j, k, CPos.cmid) = Rose.mid p.1 := by simp [aFun, h]

theorem aFun_cedgL_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (j, k, CPos.cedgL) = Rose.edg p.1 (!p.2) := by simp [aFun, h]

theorem aFun_cedgR_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (j, k, CPos.cedgR) = Rose.edg p.1 p.2 := by simp [aFun, h]

theorem aFun_pt_cmid_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (TCirc.pt w j k CPos.cmid) = Rose.mid p.1 := aFun_cmid_of_get w h

theorem aFun_pt_cedgL_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (TCirc.pt w j k CPos.cedgL) = Rose.edg p.1 (!p.2) := aFun_cedgL_of_get w h

theorem aFun_pt_cedgR_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (TCirc.pt w j k CPos.cedgR) = Rose.edg p.1 p.2 := aFun_cedgR_of_get w h

theorem aFun_pt_cor (j : J) (k : ℕ) : aFun w (TCirc.pt w j k CPos.cor) = Rose.base := rfl

theorem exists_get_of_lt {j : J} {k : ℕ} (hk : k < (w j).length) :
    ∃ p : α × Bool, (w j)[k]? = some p :=
  ⟨(w j)[k], List.getElem?_eq_getElem hk⟩

theorem aFun_monotone : Monotone (aFun w) := by
  rintro x y (rfl | h)
  · exact le_rfl
  rcases x with ⟨j, k, t⟩; rcases y with ⟨j', k', t'⟩
  rcases h with ⟨rfl, hk', hcase⟩
  obtain ⟨p, hp⟩ := exists_get_of_lt w hk'
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [aFun, hp]

def aHom : TCirc w →o Rose α := ⟨aFun w, aFun_monotone w⟩

abbrev CylBase : Type u := CylP (aHom w)

def circSet (j : J) (x : CylBase w) : Prop :=
  ∃ k t, k < (w j).length ∧ x = cylOuter (aHom w) (TCirc.pt w j k t)

def PresPos : Type u := ConeAdj (circSet w)

instance : Preorder (PresPos w) := inferInstanceAs (Preorder (ConeAdj (circSet w)))

def iRose (x : Rose α) : PresPos w := ConeAdj.inc (cylIn (aHom w) x)

def iCirc (x : TCirc w) : PresPos w := ConeAdj.inc (cylOuter (aHom w) x)

def apexOf (j : J) : PresPos w := ConeAdj.apex j

theorem iRose_monotone : Monotone (iRose w) := fun _ _ h => h

theorem iCirc_monotone : Monotone (iCirc w) := fun _ _ h => h

theorem iRose_aFun_monotone : Monotone (fun x => iRose w (aFun w x)) :=
  (iRose_monotone w).comp (aFun_monotone w)

theorem iCirc_le_iRose_aFun (x : TCirc w) : iCirc w x ≤ iRose w (aFun w x) :=
  le_refl (aFun w x)

theorem iCirc_le_apexOf {j : J} {k : ℕ} (t : CPos) (hk : k < (w j).length) :
    iCirc w (TCirc.pt w j k t) ≤ apexOf w j :=
  ConeAdj.inc_le_apex_of_mem ⟨k, t, hk, rfl⟩

def ptBase : PresPos w := iRose w Rose.base

def genLoop (i : α) : List ((orderCx (PresPos w)).E × Bool) :=
  [ordPos ((iRose_monotone w) (Rose.base_le_edg i false)),
   ordNeg ((iRose_monotone w) (Rose.mid_le_edg i false)),
   ordPos ((iRose_monotone w) (Rose.mid_le_edg i true)),
   ordNeg ((iRose_monotone w) (Rose.base_le_edg i true))]

theorem isPath_genLoop (i : α) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (genLoop w i)
      (ptBase w) (ptBase w) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def genLoopRev (i : α) : List ((orderCx (PresPos w)).E × Bool) :=
  [ordPos ((iRose_monotone w) (Rose.base_le_edg i true)),
   ordNeg ((iRose_monotone w) (Rose.mid_le_edg i true)),
   ordPos ((iRose_monotone w) (Rose.mid_le_edg i false)),
   ordNeg ((iRose_monotone w) (Rose.base_le_edg i false))]

def letterLoop (p : α × Bool) : List ((orderCx (PresPos w)).E × Bool) :=
  if p.2 then genLoop w p.1 else genLoopRev w p.1

def wordLoop (l : List (α × Bool)) : List ((orderCx (PresPos w)).E × Bool) :=
  l.flatMap (letterLoop w)

@[simp] theorem wordLoop_append (l l' : List (α × Bool)) :
    wordLoop w (l ++ l') = wordLoop w l ++ wordLoop w l' := by
  simp [wordLoop]

theorem isPath_wordLoop (l : List (α × Bool)) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (wordLoop w l)
      (ptBase w) (ptBase w) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      refine isPath_append_iff.mpr ⟨ptBase w, ?_, ih⟩
      rcases p with ⟨i, _ | _⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def segAt (j : J) (k : ℕ) : List ((orderCx (TCirc w)).E × Bool) :=
  if hk : k < (w j).length then
    [ordPos (TCirc.cor_le_cedgL w hk), ordNeg (TCirc.cmid_le_cedgL w hk),
     ordPos (TCirc.cmid_le_cedgR w hk), ordNeg (TCirc.cor_csucc_le_cedgR w hk)]
  else []

def circPath (j : J) : ℕ → List ((orderCx (TCirc w)).E × Bool)
  | 0 => []
  | m + 1 => circPath j m ++ segAt w j m

def circLoop (j : J) : List ((orderCx (TCirc w)).E × Bool) := circPath w j (w j).length

end FiniteChains.PresModel
