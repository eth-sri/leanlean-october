module

public import RequestProject.ConeAdjPoset
public import RequestProject.CylinderPoset
public import RequestProject.OrderCxNatHtpy

@[expose] public section

/-!
# The poset model of a presentation complex

Given the attaching words `w : J → List (α × Bool)` of a presentation this file builds a
**poset** whose order complex is a model of the presentation complex, in the precise form needed
by the chamber comparison: the base of the chamber construction is a poset, so the comparison of
the article's base with the model has to be made for an honest poset and not for an abstract
two-complex.

The model is assembled from three pieces.

* `FiniteChains.PresModel.Rose α` — the subdivided rose: a vertex `base`, a midpoint `mid i` for
  every generator and the two halves `edg i false`, `edg i true` of its loop, so that the
  generator `i` is carried by the four-edge circuit
  `base — edg i false — mid i — edg i true — base` of the order complex.
* `FiniteChains.PresModel.TCirc w` — for every relator a subdivided circle with four elements
  per letter, mapped onto the rose by `FiniteChains.PresModel.aFun`, which reads the letter with
  its sign: this is the attaching map of the two-cell.  The mapping cylinder of that map is the
  already available `FiniteChains.Comb.CylP`.
* a cone point over each circle (`FiniteChains.Comb.ConeAdj`): the two-cell itself.

`FiniteChains.PresModel.PresPos w` is the resulting poset, `genLoop` the loop of a generator,
`circPath` the loop of an attaching circle and `wordLoop` the loop read off a word; the identity
`mapPath_circPath` says that the attaching circle is carried onto the loop of its word.  The
comparison homomorphisms themselves are built in `RequestProject/PresPosetAlpha.lean` and
`RequestProject/PresPosetReading.lean`.
-/

namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u}

/-! ### Two elementary congruences for edges of an order complex -/

section

variable {P : Type u}
    [Preorder P]
    {a b a' b' : P}
    (ha : a = a')
    (hb : b = b')
    (h : a ≤ b)
    (h' : a' ≤ b')
include P a b a' b' ha hb

theorem ordPos_congr : ordPos h = ordPos h' := by
  simp_all

theorem ordNeg_congr : ordNeg h = ordNeg h' := by
  simp_all

end

/-! ### The subdivided rose -/

/-- The cells of the subdivided rose: the base vertex, the midpoint of the loop of a generator,
and the two halves of that loop. -/
inductive Rose (α : Type u) : Type u
  | base : Rose α
  | mid (i : α) : Rose α
  | edg (i : α) (b : Bool) : Rose α

namespace Rose

/-- The face order of the subdivided rose. -/
protected def le : Rose α → Rose α → Prop
  | base, base => True
  | base, edg _ _ => True
  | mid i, mid i' => i = i'
  | mid i, edg i' _ => i = i'
  | edg i b, edg i' b' => i = i' ∧ b = b'
  | _, _ => False

instance : Preorder (Rose α) where
  le := Rose.le
  le_refl x := by
    cases x with
    | base => exact trivial
    | mid i => exact rfl
    | edg i b => solve_by_elim
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [Rose.le]

variable (i : α) (b : Bool)

@[simp] theorem base_le_edg : base ≤ edg i b := trivial

@[simp] theorem mid_le_edg : (mid i) ≤ edg i b := rfl

end Rose

/-! ### The subdivided attaching circles -/

/-- The four elements of the circle attached to one letter of a relator: the corner in front of
the letter, the midpoint of the letter, and the two halves of the letter. -/
inductive CPos : Type
  | cor : CPos
  | cmid : CPos
  | cedgL : CPos
  | cedgR : CPos
  deriving DecidableEq

/-- The disjoint union of the subdivided attaching circles of the relators with words `w`.  The
element `(j, k, t)` belongs to the circle of the relator `j` at the position `k` of its word;
positions beyond the length of the word carry no relation. -/
def TCirc (_w : J → List (α × Bool)) := J × ℕ × CPos

namespace TCirc

variable (w : J → List (α × Bool))

variable (j : J) (k : ℕ)

variable (t : CPos)

/-- An element of a circle. -/
def pt : TCirc w := (j, k, t)

@[simp] theorem pt_fst : (pt w j k t).1 = j := rfl

@[simp] theorem pt_snd_snd : (pt w j k t).2.2 = t := rfl

@[simp] theorem pt_eq : pt w j k t = (j, k, t) := rfl

/-- The cyclic successor of a position of the word of the relator `j`. -/
def csucc := (k + 1) % (w j).length

/-- The strict relations of the circles: the corner and the midpoint of a letter lie under its
two halves, and the corner in front of the next letter lies under the right half. -/
protected def lt : TCirc w → TCirc w → Prop
  | (j, k, t), (j', k', t') =>
      j = j' ∧ k' < (w j).length ∧
        ((t = CPos.cor ∧ t' = CPos.cedgL ∧ k = k') ∨
         (t = CPos.cmid ∧ t' = CPos.cedgL ∧ k = k') ∨
         (t = CPos.cmid ∧ t' = CPos.cedgR ∧ k = k') ∨
         (t = CPos.cor ∧ t' = CPos.cedgR ∧ k = csucc w j k'))

/-- The face order of the circles. -/
protected def le (x y : TCirc w) := x = y ∨ TCirc.lt w x y

section

variable {x y : TCirc w} (h : TCirc.lt w x y)
include x y h

theorem lt_left_tag :
    x.2.2 = CPos.cor ∨ x.2.2 = CPos.cmid := by
  obtain ⟨-, -, h⟩ := h <;> grind

theorem lt_right_tag :
    y.2.2 = CPos.cedgL ∨ y.2.2 = CPos.cedgR := by
  obtain ⟨-, -, h⟩ := h <;> grind

end

instance : Preorder (TCirc w) where
  le := TCirc.le w
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | h1
    · exact hbc
    rcases hbc with rfl | h2
    · exact Or.inr h1
    exact absurd ((lt_left_tag w h2).elim (fun h => (lt_right_tag w h1).elim
      (fun h' => by simp_all)
      (fun h' => by simp_all))
      (fun h => (lt_right_tag w h1).elim
      (fun h' => by simp_all)
      (fun h' => by simp_all))) not_false

variable {j : J} {k : ℕ} (hk : k < (w j).length)
include hk

/-- The corner of a letter lies under its left half. -/
theorem cor_le_cedgL :
    pt w j k CPos.cor ≤ pt w j k CPos.cedgL :=
  Or.inr ⟨rfl, hk, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The midpoint of a letter lies under its left half. -/
theorem cmid_le_cedgL :
    pt w j k CPos.cmid ≤ pt w j k CPos.cedgL :=
  Or.inr ⟨rfl, hk, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩

/-- The midpoint of a letter lies under its right half. -/
theorem cmid_le_cedgR :
    pt w j k CPos.cmid ≤ pt w j k CPos.cedgR :=
  Or.inr ⟨rfl, hk, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩

/-- The corner in front of the next letter lies under the right half of a letter. -/
theorem cor_csucc_le_cedgR :
    pt w j (csucc w j k) CPos.cor ≤ pt w j k CPos.cedgR :=
  Or.inr ⟨rfl, hk, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩

end TCirc

/-! ### The attaching map -/

variable (w : J → List (α × Bool))

/-- The attaching map of the circles onto the rose: a corner goes to the base vertex, the
midpoint of a letter to the midpoint of its generator, and the two halves of a letter to the two
halves of the loop of its generator, in the order prescribed by the sign of the letter. -/
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

@[simp] theorem aFun_cor (j : J) (k : ℕ) : aFun w (j, k, CPos.cor) = Rose.base := rfl

section

variable {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p)
include h

theorem aFun_cmid_of_get :
    aFun w (j, k, CPos.cmid) = Rose.mid p.1 := by
  show (match (w j)[k]? with
    | some p => Rose.mid p.1
    | none => Rose.base) = _
  simp [h]

theorem aFun_cedgL_of_get :
    aFun w (j, k, CPos.cedgL) = Rose.edg p.1 (!p.2) := by
  show (match (w j)[k]? with
    | some p => Rose.edg p.1 _
    | none => Rose.base) = _
  simp [h]

theorem aFun_cedgR_of_get :
    aFun w (j, k, CPos.cedgR) = Rose.edg p.1 p.2 := by
  show (match (w j)[k]? with
    | some p => Rose.edg p.1 p.2
    | none => Rose.base) = _
  simp [h]

theorem aFun_pt_cmid_of_get :
    aFun w (TCirc.pt w j k CPos.cmid) = Rose.mid p.1 := aFun_cmid_of_get w h

theorem aFun_pt_cedgL_of_get :
    aFun w (TCirc.pt w j k CPos.cedgL) = Rose.edg p.1 (!p.2) := aFun_cedgL_of_get w h

theorem aFun_pt_cedgR_of_get :
    aFun w (TCirc.pt w j k CPos.cedgR) = Rose.edg p.1 p.2 := aFun_cedgR_of_get w h

end

theorem aFun_pt_cor (j : J) (k : ℕ) : aFun w (TCirc.pt w j k CPos.cor) = Rose.base := rfl

/-- The letter at a valid position, as an element of the word. -/
theorem exists_get_of_lt {j : J} {k : ℕ} (hk : k < (w j).length) :
    ∃ p : α × Bool, (w j)[k]? = some p :=
  by simp_all

theorem aFun_monotone : Monotone (aFun w) := by
  rintro x y (rfl | h)
  · exact le_refl _
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', hcase⟩ := h
  obtain ⟨p, hp⟩ := exists_get_of_lt w hk'
  grind [aFun_cor, aFun_cedgL_of_get, Rose.base_le_edg, aFun_cmid_of_get, Rose.mid_le_edg, aFun_cedgR_of_get]

/-- The attaching map as a monotone map. -/
def aHom : TCirc w →o Rose α := ⟨aFun w, aFun_monotone w⟩

/-! ### The model -/

/-- The mapping cylinder of the attaching map: the rose with the attaching circles sitting under
their images. -/
abbrev CylBase := CylP (aHom w)

/-- The circle of the relator `j`, as a subset of the cylinder. -/
def circSet (j : J) (x : CylBase w) :=
  ∃ k t, k < (w j).length ∧ x = cylOuter (aHom w) (TCirc.pt w j k t)

/-- **The poset model of the presentation complex**: the mapping cylinder of the attaching
circles with a cone point added over each circle. -/
def PresPos := ConeAdj (circSet w)

instance : Preorder (PresPos w) := inferInstanceAs (Preorder (ConeAdj (circSet w)))

/-- The rose inside the model. -/
def iRose (x : Rose α) : PresPos w := ConeAdj.inc (cylIn (aHom w) x)

/-- The attaching circles inside the model. -/
def iCirc (x : TCirc w) : PresPos w := ConeAdj.inc (cylOuter (aHom w) x)

/-- The two-cell of the relator `j`. -/
def apexOf (j : J) : PresPos w := ConeAdj.apex j

theorem iRose_monotone : Monotone (iRose w) := by solve_by_elim

theorem iCirc_monotone : Monotone (iCirc w) := by solve_by_elim

theorem iRose_aFun_monotone : Monotone (fun x => iRose w (aFun w x)) :=
  (iRose_monotone w).comp (aFun_monotone w)

/-- The defining relation of the cylinder: a point of a circle lies under its image. -/
theorem iCirc_le_iRose_aFun (x : TCirc w) : iCirc w x ≤ iRose w (aFun w x) :=
  le_refl (aFun w x)

/-- A point of the circle of `j` lies under the two-cell of `j`. -/
theorem iCirc_le_apexOf {j : J} {k : ℕ} (t : CPos) (hk : k < (w j).length) :
    iCirc w (TCirc.pt w j k t) ≤ apexOf w j :=
  ConeAdj.inc_le_apex_of_mem ⟨k, t, hk, rfl⟩

/-- The base point of the model. -/
def ptBase := iRose w Rose.base

/-! ### The loops of the generators -/

variable (i : α)

/-- The loop of the generator `i`: the four-edge circuit of its subdivided loop. -/
def genLoop :=
  [ordPos ((iRose_monotone w) (Rose.base_le_edg i false)),
   ordNeg ((iRose_monotone w) (Rose.mid_le_edg i false)),
   ordPos ((iRose_monotone w) (Rose.mid_le_edg i true)),
   ordNeg ((iRose_monotone w) (Rose.base_le_edg i true))]

theorem isPath_genLoop :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (genLoop w i)
      (ptBase w) (ptBase w) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The loop of a generator traversed backwards. -/
def genLoopRev :=
  [ordPos ((iRose_monotone w) (Rose.base_le_edg i true)),
   ordNeg ((iRose_monotone w) (Rose.mid_le_edg i true)),
   ordPos ((iRose_monotone w) (Rose.mid_le_edg i false)),
   ordNeg ((iRose_monotone w) (Rose.base_le_edg i false))]

theorem isPath_genLoopRev :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (genLoopRev w i)
      (ptBase w) (ptBase w) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The loop of a letter: the loop of its generator, reversed for a negative letter. -/
def letterLoop (p : α × Bool) :=
  if p.2 then genLoop w p.1 else genLoopRev w p.1

/-- The loop read off a word. -/
def wordLoop (l : List _) :=
  l.flatMap (letterLoop w)

@[simp] theorem wordLoop_nil : wordLoop w ([]) = [] := rfl

@[simp] theorem wordLoop_append (l l' : List _) :
    wordLoop w (l ++ l') = wordLoop w l ++ wordLoop w l' := by
  simp [wordLoop]

theorem isPath_letterLoop (p : α × Bool) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (letterLoop w p)
      (ptBase w) (ptBase w) := by
  obtain ⟨i, b⟩ := p
  cases b with
  | true => exact isPath_genLoop w i
  | false => exact isPath_genLoopRev w i

theorem isPath_wordLoop (l : List _) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (wordLoop w l)
      (ptBase w) (ptBase w) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      exact isPath_append_iff.mpr ⟨ptBase w, isPath_letterLoop w p, ih⟩

/-! ### The loops of the attaching circles -/

/-- The four edges of the circle of `j` at the position `k`, as a path of the order complex of
the circles. -/
def segAt (j : J) (k : ℕ) :=
  if hk : k < (w j).length then
    [ordPos (TCirc.cor_le_cedgL w hk), ordNeg (TCirc.cmid_le_cedgL w hk),
     ordPos (TCirc.cmid_le_cedgR w hk), ordNeg (TCirc.cor_csucc_le_cedgR w hk)]
  else []

/-- The path along the circle of `j` through its first `m` letters. -/
def circPath (j : J) : ℕ → List ((orderCx (TCirc w)).E × Bool)
  | 0 => []
  | m + 1 => circPath j m ++ segAt w j m

/-- The attaching loop of the relator `j`. -/
def circLoop (j : J) := circPath w j (w j).length

end PresModel
end FiniteChains
