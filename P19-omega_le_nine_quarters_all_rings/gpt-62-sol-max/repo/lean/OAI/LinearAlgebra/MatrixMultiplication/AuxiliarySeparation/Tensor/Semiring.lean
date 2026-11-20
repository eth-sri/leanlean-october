module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Ring.Subsemiring.Order
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.Option

public section

@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

noncomputable section
open Foundation

section Sums

variable {X Y Z U V W : Type*}

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : IntTensor X Y Z) (S : IntTensor U V W) :
    IntTensor (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

/-- Independent restrictions of both summands give a restriction of the sum. -/
theorem sumTensor_restrict
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (M : Tensor.Maps ℤ X' Y' Z' X Y Z) (L : Tensor.Maps ℤ U' V' W' U V W)
    (T : IntTensor X Y Z) (S : IntTensor U V W) :
    Tensor.restrict ⟨Matrix.fromBlocks M.left 0 0 L.left, Matrix.fromBlocks M.middle 0 0 L.middle,
      Matrix.fromBlocks M.right 0 0 L.right⟩ (sumTensor T S) =
      sumTensor (Tensor.restrict M T) (Tensor.restrict L S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumTensor, Fintype.sum_sum_type]

/-- Branches share their first coordinate; the other legs carry their labels. -/
def sharedFirstTensor {M : ℕ} {Y Z : Fin M → Type} (B : ∀ b, IntTensor X (Y b) (Z b)) :
    IntTensor X (Σ b, Y b) (Σ b, Z b) := by
  classical
  exact fun x y z => if h : z.1 = y.1 then B y.1 x y.2 (h ▸ z.2) else 0


end Sums

def unitTensor : IntTensor PUnit PUnit PUnit := 1

abbrev scalarTensor (r : ℕ) := Tensor.diagonal (Fin r)

namespace TensorSemiring

section Restriction

variable {X Y Z U V W : Type*}
variable [Fintype U] [Fintype V] [Fintype W]

/-- A coefficient tensor is obtained by three local linear maps. -/
def IsRestriction (T : IntTensor X Y Z) (S : IntTensor U V W) : Prop :=
  ∃ M : Tensor.Maps ℤ X Y Z U V W, T = Tensor.restrict M S

namespace IsRestriction

theorem pullback (T : IntTensor U V W) (f : X → U) (g : Y → V) (h : Z → W) :
    IsRestriction (Tensor.pullback f g h T) T := by
  classical exact ⟨_, Tensor.pullback_eq_restrict f g h T⟩

theorem refl (T : IntTensor U V W) : IsRestriction T T := pullback T id id id

theorem trans {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
    {T : IntTensor X Y Z} {S : IntTensor U V W} {L : IntTensor P Q R}
    (hTS : IsRestriction T S) (hSL : IsRestriction S L) : IsRestriction T L := by
  obtain ⟨M, rfl⟩ := hTS
  obtain ⟨L', rfl⟩ := hSL
  exact ⟨_, Tensor.restrict_restrict L' M L⟩

theorem zero (S : IntTensor U V W) : IsRestriction (0 : IntTensor X Y Z) S := by
  exact ⟨⟨0, 0, 0⟩, by ext; simp [Tensor.restrict]⟩

variable {X' Y' Z' U' V' W' : Type*} [Fintype U'] [Fintype V'] [Fintype W']
variable {T : IntTensor X Y Z} {S : IntTensor U V W}
variable {T' : IntTensor X' Y' Z'} {S' : IntTensor U' V' W'}

theorem product (h : IsRestriction T S) (h' : IsRestriction T' S') :
    IsRestriction (Tensor.product T T') (Tensor.product S S') := by
  obtain ⟨M, rfl⟩ := h
  obtain ⟨L', rfl⟩ := h'
  exact ⟨_, (Tensor.restrict_product M L' S S').symm⟩

theorem sum (h : IsRestriction T S) (h' : IsRestriction T' S') :
    IsRestriction (sumTensor T T') (sumTensor S S') := by
  obtain ⟨M, rfl⟩ := h
  obtain ⟨L', rfl⟩ := h'
  exact ⟨_, (sumTensor_restrict M L' S S').symm⟩

end IsRestriction
end Restriction

/-- Finite presentations, with arbitrary coordinate types rather than a choice
of enumerations. This makes the quotient operations compute on representatives. -/
structure FiniteTensor where
  X : Type
  Y : Type
  Z : Type
  [fx : Fintype X]
  [fy : Fintype Y]
  [fz : Fintype Z]
  coeff : IntTensor X Y Z

attribute [instance] FiniteTensor.fx FiniteTensor.fy FiniteTensor.fz

instance : Preorder FiniteTensor where
  le T S := IsRestriction T.coeff S.coeff
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

abbrev TensorClass := Antisymmetrization FiniteTensor (· ≤ ·)

variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

def classOf (T : IntTensor X Y Z) : TensorClass := toAntisymmetrization (· ≤ ·) ⟨X, Y, Z, T⟩

theorem classOf_reindex (T : IntTensor X Y Z) (e : U ≃ X) (f : V ≃ Y) (g : W ≃ Z) :
    classOf (Tensor.pullback e f g T) = classOf T :=
  le_antisymm (IsRestriction.pullback T e f g) (by
    change IsRestriction T _
    convert IsRestriction.pullback (Tensor.pullback e f g T) e.symm f.symm g.symm using 1
    funext x y z
    simp [Tensor.pullback])

theorem classOf_eq_of_reindex {T : IntTensor X Y Z} {S : IntTensor U V W}
    (e : X ≃ U) (f : Y ≃ V) (g : Z ≃ W) (h : Tensor.pullback e f g S = T) :
    classOf T = classOf S := h ▸ classOf_reindex S e f g

theorem class_ind {P : TensorClass → Prop} (h : ∀ T : FiniteTensor, P (classOf T.coeff)) : ∀ T, P T :=
  fun T => Quotient.inductionOn T h

/-- A monotone operation lifts through the product of quotient orders. -/
def lift₂ (f : FiniteTensor × FiniteTensor →o FiniteTensor) :
    TensorClass × TensorClass →o TensorClass :=
  f.antisymmetrization.comp (OrderHom.ofClass (Antisymmetrization.prodEquiv FiniteTensor FiniteTensor).symm)

instance : Mul FiniteTensor := ⟨fun T S => ⟨_, _, _, Tensor.product T.coeff S.coeff⟩⟩
instance : Add FiniteTensor := ⟨fun T S => ⟨_, _, _, sumTensor T.coeff S.coeff⟩⟩

def mulOp : TensorClass × TensorClass →o TensorClass :=
  lift₂ ⟨fun p => p.1 * p.2, fun _ _ h => IsRestriction.product h.1 h.2⟩

def addOp : TensorClass × TensorClass →o TensorClass :=
  lift₂ ⟨fun p => p.1 + p.2, fun _ _ h => IsRestriction.sum h.1 h.2⟩

instance : Mul TensorClass := ⟨Function.curry mulOp⟩
instance : Add TensorClass := ⟨Function.curry addOp⟩

theorem classOf_product (T : IntTensor X Y Z) (S : IntTensor U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := rfl

theorem classOf_sum (T : IntTensor X Y Z) (S : IntTensor U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := rfl

instance : Zero TensorClass := ⟨classOf (0 : IntTensor Empty Empty Empty)⟩
instance : One TensorClass := ⟨classOf unitTensor⟩

theorem classOf_const_one
    [Unique X] [Unique Y] [Unique Z] : classOf (1 : IntTensor X Y Z) = 1 :=
  classOf_eq_of_reindex (Equiv.equivPUnit X) (Equiv.equivPUnit Y) (Equiv.equivPUnit Z) rfl

theorem classOf_eq_zero
    {T : IntTensor X Y Z} (h : T = 0) : classOf T = 0 :=
  h ▸ le_antisymm (IsRestriction.zero _) (IsRestriction.zero _)

-- The class laws are the usual coordinate permutations of sums and products.
local macro "reindex_by " e:term : tactic =>
  `(tactic| ((try simp only [← classOf_sum, ← classOf_product]); refine classOf_eq_of_reindex $e $e $e ?_))

private theorem class_add_comm : ∀ a b : TensorClass, a + b = b + a :=
  class_ind fun a => class_ind fun b => by
    reindex_by (Equiv.sumComm _ _)
    aesop

private theorem class_mul_comm : ∀ a b : TensorClass, a * b = b * a :=
  class_ind fun a => class_ind fun b => by
    reindex_by (Equiv.prodComm _ _)
    grind [Tensor.pullback, Tensor.product, mul_comm]

private theorem class_add_zero : ∀ a : TensorClass, a + 0 = a :=
  class_ind fun _ => by
    symm
    reindex_by (Equiv.sumEmpty _ Empty).symm
    rfl

private theorem class_mul_one : ∀ a : TensorClass, a * 1 = a :=
  class_ind fun _ => by
    symm
    reindex_by (Equiv.prodPUnit _).symm
    ext; simp [Tensor.pullback, Tensor.product, unitTensor]

private theorem class_mul_zero : ∀ a : TensorClass, a * 0 = 0 :=
  class_ind fun _ => classOf_eq_zero (funext fun x => x.2.elim)

private theorem class_left_distrib : ∀ a b c : TensorClass, a * (b + c) = a * b + a * c :=
  class_ind fun a => class_ind fun b => class_ind fun c => by
    symm
    reindex_by (Equiv.prodSumDistrib _ _ _).symm
    funext x y z
    cases x <;> cases y <;> cases z <;> simp [Tensor.pullback, Tensor.product, sumTensor]

instance : CommSemiring TensorClass where
  add_assoc := class_ind fun a => class_ind fun b => class_ind fun c => by
    reindex_by (Equiv.sumAssoc _ _ _)
    aesop
  add_comm := by exact class_add_comm
  zero_add a := by exact (class_add_comm 0 a).trans (class_add_zero a)
  add_zero := by exact class_add_zero
  nsmul := nsmulRec
  mul_assoc := class_ind fun a => class_ind fun b => class_ind fun c => by
    reindex_by (Equiv.prodAssoc _ _ _)
    grind [Tensor.pullback, Tensor.product, mul_assoc]
  mul_comm := by exact class_mul_comm
  one_mul a := by exact (class_mul_comm 1 a).trans (class_mul_one a)
  mul_one := by exact class_mul_one
  mul_zero := by exact class_mul_zero
  zero_mul a := by exact (class_mul_comm 0 a).trans (class_mul_zero a)
  left_distrib := by exact class_left_distrib
  right_distrib a b c := by
    rw [class_mul_comm (a+b) c, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

theorem mul_mono {a b c d : TensorClass} (ha : a ≤ b) (hb : c ≤ d) : a * c ≤ b * d :=
  mulOp.monotone ⟨ha, hb⟩

theorem add_mono {a b c d : TensorClass} (ha : a ≤ b) (hb : c ≤ d) : a + c ≤ b + d :=
  addOp.monotone ⟨ha, hb⟩

instance : IsBotZeroClass TensorClass where
  isBot_zero := class_ind fun T => IsRestriction.zero T.coeff

instance : IsOrderedRing TensorClass where
  add_le_add_left _ _ h _ := add_mono h le_rfl
  add_le_add_right _ _ h _ := add_mono le_rfl h
  zero_le_one := zero_le
  mul_le_mul_of_nonneg_left _ _ _ _ h := mul_mono le_rfl h
  mul_le_mul_of_nonneg_right _ _ _ _ h := mul_mono h le_rfl

/-- The two generators of the three-leg permutations. -/
def permuteRep (rotate : Bool) (T : FiniteTensor) : FiniteTensor :=
  match rotate with
  | false => ⟨T.X, T.Z, T.Y, fun x z y => T.coeff x y z⟩
  | true => ⟨T.Y, T.Z, T.X, Tensor.cyclic T.coeff⟩

def permuteClass (rotate : Bool) : TensorClass →+*o TensorClass :=
  let p : FiniteTensor →o FiniteTensor := ⟨permuteRep rotate, by
    rintro T S ⟨M,h⟩
    cases rotate <;>
      first | refine ⟨⟨M.left, M.right, M.middle⟩, ?_⟩ | refine ⟨⟨M.middle, M.right, M.left⟩, ?_⟩
    all_goals
      funext x y z
      simp only [permuteRep, Tensor.cyclic, h, Tensor.restrict]
    case' true => rw [Finset.sum_comm]
    all_goals
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.sum_comm]
      simp [mul_comm, mul_left_comm, mul_assoc]
      rfl⟩
  { p.antisymmetrization with
    map_zero' := by cases rotate <;> rfl
    map_one' := by cases rotate <;> rfl
    map_add' := class_ind fun T => class_ind fun S => by
      cases rotate <;> apply congrArg (fun U => classOf U) <;>
        funext x y z <;> cases x <;> cases y <;> cases z <;> rfl
    map_mul' := class_ind fun T => class_ind fun S => by cases rotate <;> rfl }

def dot (n : ℕ) : IntTensor Unit (Fin n) (Fin n) :=
  fun _ i j => if i = j then 1 else 0

/-- Dot product classes form a monotone multiplicative family. -/
def dotClass : ℕ →* TensorClass where
  toFun n := classOf (dot n)
  map_one' := by
    rw [show dot 1 = 1 by trivial]
    exact classOf_const_one
  map_mul' m n := by
    rw [← classOf_product]
    refine classOf_eq_of_reindex (Equiv.prodUnique Unit Unit).symm
      finProdFinEquiv.symm finProdFinEquiv.symm ?_
    ext x y z
    simp only [Tensor.pullback, Tensor.product, dot,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]

theorem dotClass_mono : Monotone dotClass := by
  intro m n h
  change IsRestriction (dot m) (dot n)
  convert IsRestriction.pullback (dot n) id (Fin.castLE h) (Fin.castLE h) using 1
  ext; simp [dot, Tensor.pullback]

/-- Matrix multiplication is the product of the three oriented dot products. -/
def matrixClass : ℕ →* TensorClass :=
  let p := (permuteClass true).toMonoidHom
  dotClass * p.comp dotClass * p.comp (p.comp dotClass)

theorem matrixClass_mono : Monotone matrixClass := by
  intro m n h
  have H := dotClass_mono h
  have P := (permuteClass true).monotone'
  exact mul_mono (mul_mono H (P H)) (P (P H))

theorem squareCoefficients_class (n : ℕ) :
    classOf (Tensor.squareCoefficients n) = matrixClass n := by
  change classOf (Tensor.squareCoefficients n) =
    classOf (Tensor.product (Tensor.product (dot n) (Tensor.cyclic (dot n))) (Tensor.cyclic (Tensor.cyclic (dot n))))
  refine classOf_eq_of_reindex
    ((Equiv.prodComm _ _).trans ((Equiv.uniqueProd _ Unit).symm.prodCongr (Equiv.refl _)))
    ((Equiv.prodComm _ _).trans (Equiv.prodUnique _ Unit).symm)
    ((Equiv.prodUnique _ Unit).symm.prodCongr (Equiv.refl _)) ?_
  ext x y z
  simp [dot, Tensor.squareCoefficients, Tensor.pullback, Tensor.product, Tensor.cyclic,
    ← ite_and, and_assoc, and_comm]


/-- A block sum in which the coordinate spaces can vary from block to block. -/
def blockSum {n : ℕ} {X Y Z : Fin n → Type}
    (B : ∀ b, IntTensor (X b) (Y b) (Z b)) : IntTensor (Σ b, X b) (Σ b, Y b) (Σ b, Z b) := by
  classical
  exact fun x y z => if h : y.1 = x.1 then if e : z.1 = x.1 then B x.1 x.2 (h ▸ y.2) (e ▸ z.2) else 0 else 0


/-- Split off the first block of a dependent family. -/
private def blockSplit {n : ℕ} (A : Fin (n+1) → Type) :
    (A 0 ⊕ (Σ i : Fin n, A i.succ)) ≃ (Σ i, A i) where
  toFun
    | .inl x => ⟨0, x⟩
    | .inr ⟨i,x⟩ => ⟨i.succ, x⟩
  invFun := fun ⟨i, x⟩ => Fin.cases (motive := fun i => A i → _) Sum.inl
    (fun j x => .inr ⟨j,x⟩) i x
  left_inv := by rintro (x | ⟨i,x⟩) <;> simp
  right_inv := by
    rintro ⟨i, x⟩
    induction i using Fin.cases <;> simp

/-- Passing to tensor classes converts a block sum into a sum. -/
theorem classOf_blockSum {n : ℕ} {X Y Z : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (B : ∀ b, IntTensor (X b) (Y b) (Z b)) :
    classOf (blockSum B) = ∑ i, classOf (B i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact classOf_eq_zero (funext fun x => x.1.elim0)
  | succ n ih =>
    rw [Fin.sum_univ_succ, ← ih (fun i => B i.succ), ← classOf_sum]
    symm
    reindex_by (blockSplit _)
    funext x y z
    rcases x with x | ⟨i,x⟩ <;> rcases y with y | ⟨j,y⟩ <;> rcases z with z | ⟨k,z⟩
    all_goals simp [blockSplit, Tensor.pullback, blockSum, sumTensor,
      show ∀ j : Fin n, 0 ≠ j.succ from fun j => j.succ_ne_zero.symm]
    case inr.inr.inr =>
      by_cases h : j = i <;> by_cases e : k = i
      · subst j k; simp
      all_goals simp [h, e]

/-- Tensor products with varying factors descend to products of classes. -/
@[simp] theorem classOf_wordProduct {n : ℕ} {X Y Z : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (B : ∀ i, IntTensor (X i) (Y i) (Z i)) :
    classOf (Tensor.wordProduct B) = ∏ i, classOf (B i) := by
  induction n with
  | zero =>
      rw [Fin.prod_univ_zero, show Tensor.wordProduct B = 1 by ext; simp [Tensor.wordProduct], classOf_const_one]
  | succ n ih =>
      rw [Fin.prod_univ_succ, ← ih (fun i => B i.succ), ← classOf_product]
      reindex_by (Fin.consEquiv _).symm
      ext x y z
      simp [Tensor.wordProduct, Tensor.pullback, Tensor.product, Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]

@[simp] theorem classOf_diagonal (I : Type) [Fintype I] [DecidableEq I] :
    classOf (Tensor.diagonal I) = (Fintype.card I : TensorClass) := by
  let e := (Fintype.equivFin I).trans (Equiv.sigmaPUnit _).symm
  have h : Tensor.diagonal I =
      Tensor.pullback e e e (blockSum (fun _ : Fin (Fintype.card I) => unitTensor)) := by
    ext x y z
    simp [e, Equiv.sigmaPUnit, Tensor.diagonal, Tensor.pullback, blockSum, unitTensor]
    split_ifs <;> grind [Equiv.apply_eq_iff_eq]
  rw [h, classOf_reindex, classOf_blockSum]
  change (∑ _ : Fin (Fintype.card I), (1 : TensorClass)) = _
  simp

theorem classOf_le_nat_iff_rankAtMost
    (T : IntTensor X Y Z) (r : ℕ) : classOf T ≤ (r : TensorClass) ↔ Tensor.RankAtMost T r := by
  rw [← show classOf (scalarTensor r) = (r : TensorClass) by simp]
  rfl

theorem exists_scalar_dominator : ∀ T : TensorClass, ∃ r : ℕ, T ≤ (r : TensorClass) :=
  class_ind fun t => by
  classical
  refine ⟨Fintype.card (t.X × t.Y), ?_⟩
  rw [← classOf_diagonal (t.X × t.Y)]
  refine ⟨⟨fun x q => if x = q.1 then 1 else 0, fun y q => if y = q.2 then 1 else 0,
    fun z q => t.coeff q.1 q.2 z⟩, ?_⟩
  ext x y z
  simp [Tensor.restrict_diagonal, Fintype.sum_prod_type, ite_mul, mul_ite]

end TensorSemiring
end
end OAI.MatrixMultiplication.AuxiliarySeparation
