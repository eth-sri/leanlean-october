module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic

public section

@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

noncomputable section

open MatrixMultiplication.Foundation Filter Topology Set Classical
open scoped BigOperators

variable {K : Type*} [CommSemiring K]

def sumRestriction {X U X' U' : Type*} (f : X' → X → K) (g : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | _, _ => 0

theorem sumTensor_restrict
    {X Y Z U V W X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X' → X → K) (g : Y' → Y → K) (h : Z' → Z → K)
    (f' : U' → U → K) (g' : V' → V → K) (h' : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (sumRestriction f f') (sumRestriction g g')
      (sumRestriction h h') (sumTensor T S) =
      sumTensor (Tensor.restrict f g h T) (Tensor.restrict f' g' h' S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]

namespace TensorSemiring

section Restriction

variable {X Y Z U V W P Q R : Type*} [Fintype U] [Fintype V] [Fintype W]

def IsRestriction (T : Tensor K X Y Z) (S : Tensor K U V W) : Prop :=
  ∃ (A : X → U → K) (B : Y → V → K) (C : Z → W → K),
    T = Tensor.restrict A B C S

theorem IsRestriction.refl (T : Tensor K U V W) : IsRestriction T T :=
  ⟨_, _, _, (Tensor.restrict_identity T).symm⟩

theorem IsRestriction.trans [Fintype P] [Fintype Q] [Fintype R]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    {L : Tensor K P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix A D, Tensor.composeRestrictionMatrix B E,
    Tensor.composeRestrictionMatrix C F, Tensor.restrict_restrict D E F A B C L⟩

theorem IsRestriction.pullback (T : Tensor K U V W)
    (fx : X → U) (fy : Y → V) (fz : Z → W) :
    IsRestriction (Tensor.pullback fx fy fz T) T :=
  ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

theorem IsRestriction.of_reindex (T : Tensor K X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  have h := IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z; simp [Tensor.pullback]
  rwa [heq] at h

theorem IsRestriction.product {U' V' W' : Type*}
    [Fintype P] [Fintype Q] [Fintype R] [Fintype U'] [Fintype V'] [Fintype W']
    {T : Tensor K X Y Z} {S : Tensor K U' V' W'}
    {T' : Tensor K U V W} {S' : Tensor K P Q R}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (Tensor.restrict_product A B C D E F T' S').symm⟩

theorem IsRestriction.sum {U' V' W' : Type*}
    [Fintype P] [Fintype Q] [Fintype R] [Fintype U'] [Fintype V'] [Fintype W']
    {T : Tensor K X Y Z} {S : Tensor K U' V' W'}
    {T' : Tensor K U V W} {S' : Tensor K P Q R}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (sumTensor_restrict A B C D E F T' S').symm⟩

theorem IsRestriction.zero (S : Tensor K U V W) :
    IsRestriction (0 : Tensor K X Y Z) S :=
  ⟨0, 0, 0, funext fun _ => funext fun _ => funext fun _ => by simp [Tensor.restrict]⟩

theorem IsRestriction.rank_le [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : IsRestriction T S) : exactRank T ≤ exactRank S := by
  rcases h with ⟨A, B, C, rfl⟩
  exact exactRank_restrict_le S A B C

end Restriction

variable [Nontrivial K]

structure FiniteTensor (K : Type*) where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  coeff : Tensor K (Fin nx) (Fin ny) (Fin nz)

namespace FiniteTensor

def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : FiniteTensor K :=
  ⟨Fintype.card X, Fintype.card Y, Fintype.card Z,
    Tensor.pullback (Fintype.equivFin X).symm (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T⟩

instance : LE (FiniteTensor K) := ⟨fun T S => IsRestriction T.coeff S.coeff⟩

instance : Preorder (FiniteTensor K) where
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

end FiniteTensor

abbrev TensorClass (K : Type*) [CommSemiring K] [Nontrivial K] := Antisymmetrization (FiniteTensor K) (· ≤ ·)

def classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : TensorClass K := toAntisymmetrization (· ≤ ·) (FiniteTensor.ofTensor T)

theorem classOf_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S :=
  ⟨fun h => (IsRestriction.of_reindex T _ _ _).trans (IsRestriction.trans h (IsRestriction.pullback S _ _ _)),
   fun h => (IsRestriction.pullback T _ _ _).trans (h.trans (IsRestriction.of_reindex S _ _ _))⟩

theorem classOf_eq_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := by
  rw [le_antisymm_iff, classOf_le_iff, classOf_le_iff]

theorem classOf_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.pullback T ex ey ez,
    IsRestriction.of_reindex T ex ey ez⟩

theorem classOf_eq_of_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem classOf_coeff (T : FiniteTensor K) :
    classOf T.coeff = toAntisymmetrization (· ≤ ·) T :=
  (toAntisymmetrization_eq (· ≤ ·) _ _).mpr
    ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

@[elab_as_elim] theorem ind {P : TensorClass K → Prop}
    (h : ∀ {nx ny nz} (T : Tensor K (Fin nx) (Fin ny) (Fin nz)), P (classOf T))
    (a : TensorClass K) : P a :=
  Quotient.inductionOn a fun T => by
    change P (toAntisymmetrization (· ≤ ·) T)
    rw [← classOf_coeff T]
    exact h T.coeff

instance : Mul (TensorClass K) where
  mul := Quotient.map₂ (fun T S => FiniteTensor.ofTensor (Tensor.product T.coeff S.coeff))
    fun _ _ hT _ _ hS =>
      ⟨(classOf_le_iff _ _).mpr (IsRestriction.product hT.1 hS.1),
       (classOf_le_iff _ _).mpr (IsRestriction.product hT.2 hS.2)⟩

instance : Add (TensorClass K) where
  add := Quotient.map₂ (fun T S => FiniteTensor.ofTensor (sumTensor T.coeff S.coeff))
    fun _ _ hT _ _ hS =>
      ⟨(classOf_le_iff _ _).mpr (IsRestriction.sum hT.1 hS.1),
       (classOf_le_iff _ _).mpr (IsRestriction.sum hT.2 hS.2)⟩

theorem classOf_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S :=
  (classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)).symm

theorem classOf_sum {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  change classOf (sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff) = _
  rw [show sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff =
    Tensor.pullback
      (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
      (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
      (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
      (sumTensor T S) from by funext x y z; cases x <;> cases y <;> cases z <;> rfl]
  exact classOf_reindex (sumTensor T S) _ _ _

instance : Zero (TensorClass K) := ⟨classOf (0 : Tensor K Empty Empty Empty)⟩
instance : One (TensorClass K) := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))⟩

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor K X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

theorem add_comm' (a b : TensorClass K) : a + b = b + a := by
  induction a using ind with | h a =>
  induction b using ind with | h b =>
  rw [← classOf_sum, ← classOf_sum]
  exact classOf_eq_of_reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
    (by funext x y z; cases x <;> cases y <;> cases z <;> rfl)

theorem mul_comm' (a b : TensorClass K) : a * b = b * a := by
  induction a using ind with | h a =>
  induction b using ind with | h b =>
  rw [← classOf_product, ← classOf_product]
  exact classOf_eq_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (by funext x y z; simp [Tensor.pullback, Tensor.product, mul_comm])

theorem left_distrib' (a b c : TensorClass K) : a * (b + c) = a * b + a * c := by
  induction a using ind with | h a =>
  induction b using ind with | h b =>
  induction c using ind with | h c =>
  simp only [← classOf_product, ← classOf_sum]
  exact (classOf_eq_of_reindex (Equiv.prodSumDistrib _ _ _).symm
    (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm
    (by funext x y z; cases x <;> cases y <;> cases z <;>
      simp [Tensor.pullback, Tensor.product, sumTensor])).symm

theorem add_zero' (a : TensorClass K) : a + 0 = a := by
  induction a using ind with | h a =>
  change classOf a + classOf (0 : Tensor K Empty Empty Empty) = classOf a
  rw [← classOf_sum]
  exact (classOf_eq_of_reindex (Equiv.sumEmpty _ Empty).symm
    (Equiv.sumEmpty _ Empty).symm (Equiv.sumEmpty _ Empty).symm rfl).symm

theorem mul_one' (a : TensorClass K) : a * 1 = a := by
  induction a using ind with | h a =>
  change classOf a * classOf (fun (_ _ _ : PUnit.{1}) => (1 : K)) = classOf a
  rw [← classOf_product]
  exact (classOf_eq_of_reindex (Equiv.prodPUnit _).symm
    (Equiv.prodPUnit _).symm (Equiv.prodPUnit _).symm
    (by funext x y z; simp [Tensor.pullback, Tensor.product])).symm

theorem mul_zero' (a : TensorClass K) : a * 0 = 0 := by
  induction a using ind with | h a =>
  change classOf a * classOf (0 : Tensor K Empty Empty Empty) = 0
  rw [← classOf_product,
    show Tensor.product a (0 : Tensor K Empty Empty Empty) = 0 from
      funext fun _ => funext fun _ => funext fun _ => by simp [Tensor.product], classOf_zero]

instance : CommSemiring (TensorClass K) where
  add_assoc a b c := by
    induction a using ind with | h a =>
    induction b using ind with | h b =>
    induction c using ind with | h c =>
    simp only [← classOf_sum]
    exact classOf_eq_of_reindex (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _)
      (by funext x y z; rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
        rcases z with (z | z) | z <;> rfl)
  add_comm := add_comm'
  add_zero := add_zero'
  zero_add a := (add_comm' 0 a).trans (add_zero' a)
  nsmul := nsmulRec
  mul_assoc a b c := by
    induction a using ind with | h a =>
    induction b using ind with | h b =>
    induction c using ind with | h c =>
    simp only [← classOf_product]
    exact classOf_eq_of_reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (by funext x y z; simp [Tensor.pullback, Tensor.product, mul_assoc])
  mul_comm := mul_comm'
  mul_one := mul_one'
  one_mul a := (mul_comm' 1 a).trans (mul_one' a)
  mul_zero := mul_zero'
  zero_mul a := (mul_comm' 0 a).trans (mul_zero' a)
  left_distrib := left_distrib'
  right_distrib a b c := by rw [mul_comm', left_distrib', mul_comm' c a, mul_comm' c b]

theorem mul_mono {T T' S S' : TensorClass K} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := by
  induction T using ind with | h T =>
  induction T' using ind with | h T' =>
  induction S using ind with | h S =>
  induction S' using ind with | h S' =>
  rw [← classOf_product, ← classOf_product, classOf_le_iff]
  exact IsRestriction.product ((classOf_le_iff _ _).mp hT) ((classOf_le_iff _ _).mp hS)

theorem add_mono {T T' S S' : TensorClass K} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := by
  induction T using ind with | h T =>
  induction T' using ind with | h T' =>
  induction S using ind with | h S =>
  induction S' using ind with | h S' =>
  rw [← classOf_sum, ← classOf_sum, classOf_le_iff]
  exact IsRestriction.sum ((classOf_le_iff _ _).mp hT) ((classOf_le_iff _ _).mp hS)

theorem zero_le (T : TensorClass K) : 0 ≤ T := by
  induction T using ind with | h T =>
  exact (classOf_le_iff _ _).mpr (IsRestriction.zero T)

def rank : TensorClass K → ℕ := Quotient.lift (fun T : FiniteTensor K => exactRank T.coeff)
  fun _ _ h => le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2)

@[simp] theorem rank_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono {T S : TensorClass K} (h : T ≤ S) : rank T ≤ rank S := by
  induction T using ind with | h T =>
  induction S using ind with | h S =>
  simpa only [rank_classOf] using IsRestriction.rank_le ((classOf_le_iff _ _).mp h)

theorem rank_mul_le (T S : TensorClass K) : rank (T * S) ≤ rank T * rank S := by
  induction T using ind with | h T =>
  induction S using ind with | h S =>
  rw [← classOf_product]
  simpa only [rank_classOf] using exactRank_product_le _ _

def matrixClass (n : ℕ) : TensorClass K := classOf ((matrixMultiplicationTensor (K := K)) n n n)

@[simp] theorem rank_matrixClass (n : ℕ) : rank ((matrixClass (K := K)) n) = (exactMatrixRank K) n :=
  rank_classOf _

theorem matrixClass_mul (m n : ℕ) : (matrixClass (K := K)) (m * n) = (matrixClass (K := K)) m * (matrixClass (K := K)) n := by
  let e : Fin (m * n) ≃ Fin m × Fin n := Fintype.equivOfCardEq (by simp)
  have h : (matrixClass (K := K)) (m * n) = classOf (Tensor.matrixCoefficients (K := K)
      (Fin m × Fin n) (Fin m × Fin n) (Fin m × Fin n)) := by
    apply classOf_eq_of_reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) (Equiv.prodCongr e e)
    funext x y z
    simp [Tensor.pullback, Tensor.matrixCoefficients, matrixMultiplicationTensor, e.injective.eq_iff]
  rw [h]
  change _ = classOf (Tensor.matrixCoefficients (K := K) (Fin m) (Fin m) (Fin m)) *
    classOf (Tensor.matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))
  rw [← classOf_product]
  apply classOf_eq_of_reindex (Equiv.prodProdProdComm _ _ _ _)
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

@[simp] theorem matrixClass_one : (matrixClass (K := K)) 1 = 1 := by
  let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
  apply classOf_eq_of_reindex e e e
  funext x y z
  simp [Tensor.pullback, matrixMultiplicationTensor,
    Subsingleton.elim x.2 y.1, Subsingleton.elim y.2 z.1, Subsingleton.elim z.2 x.1]

theorem matrixClass_pow (m j : ℕ) : (matrixClass (K := K)) (m ^ j) = (matrixClass (K := K)) m ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, matrixClass_mul, ih, pow_succ]

theorem one_le_classOf_of_coefficient_one {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] {T : Tensor K X Y Z}
    (hT : ∃ x y z, T x y z = 1) : 1 ≤ classOf T := by
  obtain ⟨x, y, z, hxyz⟩ := hT
  exact (classOf_le_iff _ _).mpr ⟨fun _ u => if u = x then 1 else 0,
    fun _ v => if v = y then 1 else 0, fun _ w => if w = z then 1 else 0,
    by funext a b c; simp [Tensor.restrict, ite_mul, mul_ite, hxyz]⟩

@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf ((scalarTensor (K := K)) r) = (r : TensorClass K) := by
  induction r with
  | zero =>
    rw [show (scalarTensor (K := K)) 0 = 0 from funext fun x => Fin.elim0 x, classOf_zero, Nat.cast_zero]
  | succ r ih =>
    have hadd : classOf ((scalarTensor (K := K)) (r + 1)) =
        classOf ((scalarTensor (K := K)) r) + classOf ((scalarTensor (K := K)) 1) := by
      refine (classOf_eq_of_reindex (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r + 1))
        finSumFinEquiv finSumFinEquiv ?_).symm.trans (classOf_sum _ _)
      funext x y z
      simp only [Tensor.pullback, scalarTensor, finSumFinEquiv.injective.eq_iff]
      cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]
    have hone : classOf ((scalarTensor (K := K)) 1) = (1 : TensorClass K) := by
      apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
        (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
      funext x y z
      simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]
    simp [hadd, ih, hone]

@[simp] theorem rank_natCast (r : ℕ) : rank (r : TensorClass K) = r := by
  rw [← classOf_scalarTensor r, rank_classOf]
  apply le_antisymm
  · refine exactRank_le ⟨fun i x => if x = i then 1 else 0,
      fun i y => if y = i then 1 else 0, fun i z => if z = i then 1 else 0, ?_⟩
    funext x y z
    simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
    split_ifs <;> simp_all
  · simpa only [Fintype.card_fin] using
      (exactRank_spec ((scalarTensor (K := K)) r)).card_le_of_identity id id id
        (by intro i j; simp [scalarTensor])

theorem le_rank (T : TensorClass K) : T ≤ (rank T : TensorClass K) := by
  induction T using ind with | h T =>
  rw [rank_classOf, ← classOf_scalarTensor, classOf_le_iff]
  rcases exactRank_spec T with ⟨a, b, c, h⟩
  exact ⟨fun x i => a i x, fun y i => b i y, fun z i => c i z,
    h.trans (Character.restrict_scalarTensor _ a b c).symm⟩

end TensorSemiring

section Farkas
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_nonneg_representation_erase (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ i ∈ s, ∃ v : I → ℝ, (∀ j ∈ s.erase i, 0 ≤ v j) ∧
      (∑ j ∈ s.erase i, v j • A j) = ∑ j ∈ s, w j • A j := by
  obtain ⟨g₀, hg₀, i₁, hi₁, hgi₁⟩ := (not_linearIndepOn_finset_iff (R := ℝ) (v := A)).mp h
  obtain ⟨g, hg, i, hi, hgi⟩ : ∃ g : I → ℝ, (∑ i ∈ s, g i • A i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
    rcases lt_or_gt_of_ne hgi₁ with hneg | hpos
    · refine ⟨fun j ↦ -g₀ j, ?_, i₁, hi₁, neg_pos.mpr hneg⟩
      simp_rw [neg_smul, Finset.sum_neg_distrib, hg₀, neg_zero]
    · exact ⟨g₀, hg₀, i₁, hi₁, hpos⟩
  let p := s.filter fun i ↦ 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ := p.exists_min_image (fun j ↦ w j / g j) ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : 0 < g i₀ := (Finset.mem_filter.mp hi₀).2
  let v : I → ℝ := fun j ↦ w j - w i₀ / g i₀ * g j
  refine ⟨i₀, hi₀s, v, fun j hj ↦ ?_, ?_⟩
  · have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    apply sub_nonneg.mpr
    by_cases hjp : j ∈ p
    · exact (le_div_iff₀ (Finset.mem_filter.mp hjp).2).mp (hmin j hjp)
    · have hgj : g j ≤ 0 := by simpa only [p, Finset.mem_filter, hjs, true_and, not_lt] using hjp
      exact (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hw i₀ hi₀s) hgi₀.le) hgj).trans (hw j hjs)
  · calc (∑ j ∈ s.erase i₀, v j • A j) = ∑ j ∈ s, v j • A j :=
          Finset.sum_erase _ (by simp [v, ne_of_gt hgi₀])
      _ = ∑ j ∈ s, w j • A j := by
          simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hg, smul_zero, sub_zero]

private theorem exists_nonneg_representation_linearIndependent (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndependent ℝ (fun i : t ↦ A i) ∧
      ∃ v : I → ℝ, (∀ i ∈ t, 0 ≤ v i) ∧ (∑ i ∈ t, v i • A i) = ∑ i ∈ s, w i • A i := by
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hs : LinearIndependent ℝ (fun i : s ↦ A i)
    · exact ⟨s, Finset.Subset.refl _, hs, w, hw, rfl⟩
    · obtain ⟨i, hi, v, hv, heq⟩ := exists_nonneg_representation_erase A s w hw hs
      obtain ⟨t, hts, ht, z, hz, hzeq⟩ := ih (s.erase i) (Finset.erase_ssubset hi) v hv
      exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, z, hz, hzeq.trans heq⟩

private theorem isClosed_pointedCone_hull_range_of_linearIndependent
    [Fintype I] (A : I → E) (hA : LinearIndependent ℝ A) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  let f := Fintype.linearCombination ℝ A
  have hf : IsClosedEmbedding f :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hA.fintypeLinearCombination_injective)
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      f '' {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    change x ∈ PointedCone.hull ℝ (Set.range A) ↔ _
    rw [PointedCone.hull, Submodule.mem_span_range_iff_exists_fun]
    exact ⟨fun ⟨c, hc⟩ ↦ ⟨fun i ↦ c i, fun i ↦ (c i).2, hc⟩,
      fun ⟨c, hc, hcx⟩ ↦ ⟨fun i ↦ ⟨c i, hc i⟩, hcx⟩⟩
  rw [heq]
  refine hf.isClosedMap _ ?_
  simpa only [Set.ofPred_forall] using
    isClosed_iInter fun i ↦ isClosed_le (continuous_const : Continuous fun _ : I → ℝ ↦ (0 : ℝ)) (continuous_apply i)

private theorem isClosed_pointedCone_hull_range [Fintype I] (A : I → E) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  let S := {s : Finset I // LinearIndependent ℝ (fun i : s ↦ A i)}
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      ⋃ s : S, (PointedCone.hull ℝ (Set.range (fun i : s.1 ↦ A i)) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg ℝ)).mp hx
      obtain ⟨s, _, hs, v, hv, heq⟩ := exists_nonneg_representation_linearIndependent A Finset.univ
        (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).2)
      refine Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
      have hsum : (∑ i ∈ s, v i • A i) = x := heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
      rw [← hsum]
      exact Submodule.sum_mem _ fun i hi ↦ PointedCone.smul_mem _ (hv i hi) (PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩)
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.1, rfl⟩) hs
  rw [heq]
  exact isClosed_iUnion_of_finite fun s : S ↦ isClosed_pointedCone_hull_range_of_linearIndependent _ s.2

theorem exists_normalized_nonneg_linear_of_no_nat_certificate
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) := by
  let AR : I → J → ℝ := fun i j ↦ A i j
  let C : ProperCone ℝ (J → ℝ) := ⟨PointedCone.hull ℝ (Set.range AR), isClosed_pointedCone_hull_range AR⟩
  have houtside : -(fun j ↦ (u j : ℝ)) ∉ C := by
    intro hmem
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg ℝ)).mp hmem
    obtain ⟨t, _, ht, v₀, hv₀, heq⟩ := exists_nonneg_representation_linearIndependent AR Finset.univ
      (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).2)
    have hveq : (∑ i ∈ t, v₀ i • AR i) = -(fun j ↦ (u j : ℝ)) :=
      heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
    obtain ⟨p, hp1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)
    have hp (q : ℚ) : p (q : ℝ) = q := by simpa [hp1] using p.map_smul q (1 : ℝ)
    let q : I → ℚ := fun i ↦ if i ∈ t then p (v₀ i) else 0
    have hq_sub (j : J) : ∑ i ∈ t, q i * (A i j : ℚ) = (-u j : ℚ) := by
      have hj := congrArg p (congrFun hveq j)
      have hj2 : p ((u j : ℤ) : ℝ) = (u j : ℚ) := by simpa only [Rat.cast_intCast] using hp (u j : ℚ)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, AR, map_sum,
        map_neg, hj2] at hj
      rw [← hj]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hm := p.map_smul (A i j : ℚ) (v₀ i)
      simpa only [q, hi, ↓reduceIte, Rat.smul_def, smul_eq_mul, Rat.cast_intCast, mul_comm] using hm.symm
    have hqeq (j : J) : ∑ i, q i * (A i j : ℚ) = (-u j : ℚ) := by
      rw [← hq_sub j]
      exact (Finset.sum_subset (Finset.subset_univ t) fun i _ hi ↦ by simp [q, hi]).symm
    have hqreal : (∑ i ∈ t, (q i : ℝ) • AR i) = ∑ i ∈ t, v₀ i • AR i := by
      rw [hveq]
      funext j
      have hj : (∑ i ∈ t, (q i : ℝ) * (A i j : ℝ)) = ((-u j : ℤ) : ℝ) := by exact_mod_cast hq_sub j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Int.cast_neg, AR] using hj
    have hqv (i : I) (hi : i ∈ t) : (q i : ℝ) = v₀ i :=
      sub_eq_zero.mp <| linearIndepOn_finset_iff.mp ht (fun i ↦ (q i : ℝ) - v₀ i)
        (by simp_rw [sub_smul, Finset.sum_sub_distrib, hqreal, sub_self]) i hi
    have hqpos (i : I) : 0 ≤ q i := by
      by_cases hi : i ∈ t
      · have : 0 ≤ (q i : ℝ) := by rw [hqv i hi]; exact hv₀ i hi
        exact_mod_cast this
      · simp [q, hi]
    let D : ℕ := ∏ i, (q i).den
    have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
    have hcdvd (i : I) : ∃ c : ℕ, (D : ℚ) * q i = c := by
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i)
      refine ⟨k * (q i).num.toNat, ?_⟩
      have hnum : ((q i).num.toNat : ℚ) = (q i).num := by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hqpos i))
      have hD_eq : (D : ℚ) = (q i).den * k := by exact_mod_cast hk
      rw [hD_eq, Nat.cast_mul, hnum]
      calc ((q i).den : ℚ) * k * q i = k * (((q i).den : ℚ) * q i) := by ring
        _ = k * (q i).num := by rw [Rat.den_mul_eq_num]
    choose c hc using hcdvd
    refine hno ⟨D, hD, c, fun j ↦ ?_⟩
    suffices hrat : (∑ i, (c i : ℚ) * (A i j : ℚ)) = -(D : ℚ) * (u j : ℚ) by exact_mod_cast hrat
    simp_rw [← hc, mul_assoc, ← Finset.mul_sum, hqeq j]
    ring
  obtain ⟨f, hf, hfu⟩ := C.hyperplane_separation_point houtside
  have hpos : 0 < f (fun j ↦ (u j : ℝ)) := by simpa only [map_neg, neg_neg, neg_lt_zero] using hfu
  refine ⟨(f (fun j ↦ (u j : ℝ)))⁻¹ • f.toLinearMap, ?_, fun i ↦ ?_⟩
  · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · exact mul_nonneg (inv_nonneg.mpr hpos.le) (hf _ (PointedCone.subset_hull (Set.mem_range_self i)))

end Farkas

section States
variable {S : Type*} [CommSemiring S]

section Preorder
variable [Preorder S]

def normalizedStates (R : S → ℝ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    (∀ x, k * f x ≤ f (d * x))}

inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)

def posEval {α : Type*} [AddCommMonoid α] (R : S → ℕ) (d : S) (f : S → α) :
    StateConstraint S → α
  | .lower x => f x
  | .upper x => R x • f 1
  | .addPos x y => f (x + y)
  | .addNeg x y => f x + f y
  | .order _ y _ => f y
  | .detector x => f (d * x)

def negEval {α : Type*} [AddCommMonoid α] (k : ℕ) (f : S → α) :
    StateConstraint S → α
  | .lower _ => 0
  | .upper x => f x
  | .addPos x y => f x + f y
  | .addNeg x y => f (x + y)
  | .order x _ _ => f x
  | .detector x => k • f x

theorem map_posEval {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (g : α →+ β) (R : S → ℕ) (d : S) (f : S → α) (c : StateConstraint S) :
    g (posEval R d f c) = posEval R d (g ∘ f) c := by
  cases c <;> simp [posEval]

theorem map_negEval {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (g : α →+ β) (k : ℕ) (f : S → α) (c : StateConstraint S) :
    g (negEval k f c) = negEval k (g ∘ f) c := by
  cases c <;> simp [negEval]

def evalConstraint (R : S → ℕ) (d : S) (k : ℕ) (f : S → ℝ) (c : StateConstraint S) : ℝ :=
  posEval R d f c - negEval k f c

def indNat (H : Finset S) (x : S) (j : H) : ℕ :=
  if (j : S) = x then 1 else 0

def evalS (H : Finset S) : (H → ℕ) →+ S where
  toFun v := ∑ j : H, (v j : S) * (j : S)
  map_zero' := by simp
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]

omit [Preorder S] in
theorem evalS_indNat {H : Finset S} {x : S} (hx : x ∈ H) :
    evalS H (indNat H x) = x := by
  change ∑ j : H, (indNat H x j : S) * (j : S) = x
  rw [Finset.sum_eq_single (⟨x, hx⟩ : H)
    (fun j _ hj => by simp [indNat, Subtype.ext_iff.not.mp hj])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [indNat]

def cSupp (d : S) : StateConstraint S → Finset S
  | .lower x | .upper x => {x}
  | .addPos x y | .addNeg x y => {x, y, x + y}
  | .order x y _ => {x, y}
  | .detector x => {x, d * x}

def posOrd (R : S → ℕ) : StateConstraint S → S
  | .lower x => x
  | .upper x => R x
  | .addPos x y | .addNeg x y => x + y
  | .order _ y _ => y
  | .detector _ => 0

def negOrd : StateConstraint S → S
  | .lower _ | .detector _ => 0
  | .upper x | .order x _ _ => x
  | .addPos x y | .addNeg x y => x + y

def detElem : StateConstraint S → S
  | .detector x => x
  | _ => 0

theorem posEval_eq_posOrd {H : Finset S} (R : S → ℕ) (d : S) (c : StateConstraint S)
    (h1 : (1 : S) ∈ H) (hc : ∀ a ∈ cSupp d c, a ∈ H) :
    posEval R d (evalS H ∘ indNat H) c = posOrd R c + d * detElem c := by
  cases c <;> simp [cSupp] at hc <;> simp [posEval, posOrd, detElem, h1, hc, evalS_indNat]

theorem negEval_eq_negOrd {H : Finset S} (d : S) (k : ℕ) (c : StateConstraint S)
    (hc : ∀ a ∈ cSupp d c, a ∈ H) :
    negEval k (evalS H ∘ indNat H) c = negOrd c + (k : S) * detElem c := by
  cases c <;> simp [cSupp] at hc <;> simp [negEval, negOrd, detElem, hc, evalS_indNat]

theorem normalizedStates_nonempty_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s) :
    (normalizedStates (fun x ↦ (R x : ℝ)) d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K : Set (S → ℝ) := B ∩ {f | f 1 = 1}
  let t : StateConstraint S → Set (S → ℝ) :=
    fun c ↦ {f | 0 ≤ evalConstraint R d k f c}
  have hBcompact : IsCompact B :=
    isCompact_pi_infinite (fun x ↦ isCompact_Icc (a := (0 : ℝ)) (b := (R x : ℝ)))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed (c : StateConstraint S) : IsClosed (t c) := by
    refine isClosed_le continuous_const ?_
    cases c <;> simp only [evalConstraint, posEval, negEval, nsmul_eq_mul] <;> fun_prop
  have hfinite (F : Finset (StateConstraint S)) : (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    let H : Finset S := insert 1 (F.biUnion (cSupp d))
    have hOne : (1 : S) ∈ H := Finset.mem_insert_self _ _
    let cs : F ⊕ (Bool × H) → StateConstraint S
      | .inl c => c
      | .inr (false, x) => .lower x
      | .inr (true, x) => .upper x
    have hH (i : F ⊕ (Bool × H)) (a : S) (ha : a ∈ cSupp d (cs i)) : a ∈ H := by
      rcases i with c | ⟨_ | _, x⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, c.2, ha⟩)
      · exact (Finset.mem_singleton.mp ha) ▸ x.2
      · exact (Finset.mem_singleton.mp ha) ▸ x.2
    let P (i : F ⊕ (Bool × H)) : H → ℕ := posEval R d (indNat H) (cs i)
    let Q (i : F ⊕ (Bool × H)) : H → ℕ := negEval k (indNat H) (cs i)
    let A (i : F ⊕ (Bool × H)) (j : H) : ℤ := (P i j : ℤ) - (Q i j : ℤ)
    let u (j : H) : ℤ := indNat H 1 j
    have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : (F ⊕ (Bool × H)) → ℕ,
        ∀ j : H, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j := by
      rintro ⟨m, hm, n, hn⟩
      have hnat : (∑ i, n i • P i) + m • indNat H 1 = ∑ i, n i • Q i := by
        funext j
        have hj := hn j
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, A, u,
          mul_sub, Finset.sum_sub_distrib] at hj ⊢
        zify; linarith
      have hS := congrArg (evalS H) hnat
      simp only [map_add, map_sum, map_nsmul, P, Q, map_posEval, map_negEval,
        evalS_indNat hOne, posEval_eq_posOrd R d _ hOne (hH _),
        negEval_eq_negOrd d k _ (hH _)] at hS
      simp only [nsmul_eq_mul, mul_one, mul_add, Finset.sum_add_distrib,
        mul_left_comm _ d, mul_left_comm _ (k : S), ← Finset.mul_sum] at hS
      let D := ∑ i, (n i : S) * negOrd (cs i)
      let Psum := ∑ i, (n i : S) * posOrd R (cs i)
      let s := ∑ i, (n i : S) * detElem (cs i)
      have hnsmul {a b : S} (hab : a ≤ b) (l : ℕ) : (l : S) * a ≤ (l : S) * b := by
        induction l with
        | zero => simp
        | succ l ih =>
          rw [Nat.cast_add, Nat.cast_one, add_mul, add_mul, one_mul, one_mul]
          exact hadd _ _ _ _ ih hab
      have hDP : ∀ t : Finset (F ⊕ (Bool × H)),
          ∑ i ∈ t, (n i : S) * negOrd (cs i) ≤ ∑ i ∈ t, (n i : S) * posOrd R (cs i) := by
        intro t
        induction t using Finset.induction_on with
        | empty => simp
        | @insert i t hi ih =>
          have hord : negOrd (cs i) ≤ posOrd R (cs i) := by
            cases cs i with
            | lower x => exact hzero x
            | upper x => exact hbound x
            | order _ _ h => exact h
            | _ => exact le_rfl
          simpa only [Finset.sum_insert hi] using hadd _ _ _ _ (hnsmul hord (n i)) ih
      exact hno D s m hm (calc
        D + (m : S) + d * s ≤ Psum + (m : S) + d * s :=
          hadd _ _ _ _ (hadd _ _ _ _ (hDP Finset.univ) le_rfl) le_rfl
        _ = Psum + d * s + (m : S) := by ac_rfl
        _ = D + (k : S) * s := hS)
    obtain ⟨L, hLu, hLA⟩ := exists_normalized_nonneg_linear_of_no_nat_certificate A u hcert
    let gL : (H → ℕ) →+ ℝ :=
      { toFun := fun v => L (fun j => (v j : ℝ))
        map_zero' := by convert L.map_zero; simp
        map_add' := fun u v => by simp [← map_add]; rfl }
    let f : S → ℝ := gL ∘ indNat H
    have hf1 : f 1 = 1 := by simpa [f, gL, u] using hLu
    have hfeval (i : F ⊕ (Bool × H)) : 0 ≤ evalConstraint R d k f (cs i) := by
      have hi := hLA i
      have heq : L (fun j : H => (A i j : ℝ)) = gL (P i) - gL (Q i) := by
        simp only [gL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← map_sub]
        congr 1; funext j; simp [A]
      rwa [heq, map_posEval, map_negEval] at hi
    refine ⟨f, ⟨fun x => ?_, hf1⟩, mem_iInter₂.mpr fun c hc => hfeval (.inl ⟨c, hc⟩)⟩
    by_cases hx : x ∈ H
    · exact ⟨by simpa [cs, evalConstraint, posEval, negEval] using hfeval (.inr (false, ⟨x, hx⟩)),
        by simpa [cs, evalConstraint, posEval, negEval, hf1, sub_nonneg, nsmul_eq_mul] using
          hfeval (.inr (true, ⟨x, hx⟩))⟩
    · have hx0 : indNat H x = 0 := funext fun j => by
        simp [indNat, show (j : S) ≠ x from fun h => hx (h ▸ j.2)]
      simp [f, hx0]
  obtain ⟨f, ⟨hfb, hf1⟩, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  have hc (c : StateConstraint S) : 0 ≤ evalConstraint R d k f c := mem_iInter.mp hft c
  refine ⟨f, hfb, hf1, fun x y => ?_, fun x y hxy => ?_, fun x => ?_⟩
  · have h1 := hc (.addPos x y); have h2 := hc (.addNeg x y)
    dsimp [evalConstraint, posEval, negEval] at h1 h2; linarith
  · have h1 := hc (.order x y hxy); dsimp [evalConstraint, posEval, negEval] at h1; linarith
  · have h1 := hc (.detector x)
    simp only [evalConstraint, posEval, negEval, nsmul_eq_mul, sub_nonneg] at h1
    exact h1

theorem normalizedStates_isCompact (R : S → ℝ) (d : S) (k : ℝ) :
    IsCompact (normalizedStates R d k) := by
  refine (isCompact_univ_pi fun x => isCompact_Icc (a := (0 : ℝ)) (b := R x)).of_isClosed_subset ?_
    fun f hf x _ => hf.1 x
  unfold normalizedStates
  simp only [ofPred_and, ofPred_forall]
  repeat' first
    | apply IsClosed.inter
    | (apply isClosed_iInter; intro _)
    | exact isClosed_le (by fun_prop) (by fun_prop)
    | exact isClosed_eq (by fun_prop) (by fun_prop)

theorem normalizedStates_convex (R : S → ℝ) (d : S) (k : ℝ) :
    Convex ℝ (normalizedStates R d k) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun x => ⟨add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1), ?_⟩,
    ?_, fun x y => ?_, fun x y hxy => ?_, fun x => ?_⟩
  · calc a * f x + b * g x ≤ a * R x + b * R x :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha) (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
      _ = R x := by rw [← add_mul, hab, one_mul]
  · change a * f 1 + b * g 1 = 1
    rw [hf.2.1, hg.2.1, mul_one, mul_one, hab]
  · change a * f (x + y) + b * g (x + y) = (a * f x + b * g x) + (a * f y + b * g y)
    rw [hf.2.2.1, hg.2.2.1]; ring
  · exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb)
  · change k * (a * f x + b * g x) ≤ a * f (d * x) + b * g (d * x)
    calc k * (a * f x + b * g x) = a * (k * f x) + b * (k * g x) := by ring
      _ ≤ a * f (d * x) + b * g (d * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 x) ha)
          (mul_le_mul_of_nonneg_left (hg.2.2.2.2 x) hb)

theorem state_zero {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) : f 0 = 0 := by
  have h := hf.2.2.1 0 0; rw [zero_add] at h; linarith

theorem state_nat_mul {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) (n : ℕ) (x : S) :
    f ((n : S) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simp [state_zero hf]
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]; push_cast; ring

theorem state_one_le {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) {z : S} (hz : 1 ≤ z) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 1 z hz

theorem state_rescale {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates (fun x => (R x : ℝ)) d k) (z : S) (hz : 1 ≤ z)
    (hmulmono : ∀ x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ x : S, z * x ≤ (R x : S) * z) :
    (fun x => f (z * x) / f z) ∈ normalizedStates (fun x => (R x : ℝ)) d k := by
  have hfz : 0 < f z := lt_of_lt_of_le zero_lt_one (state_one_le hf hz)
  refine ⟨fun x => ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, (div_le_iff₀ hfz).mpr ?_⟩,
    by simp [mul_one, ne_of_gt hfz], fun x y => ?_,
    fun x y hxy => div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (hmulmono x y hxy)) hfz.le,
    fun x => ?_⟩
  · simpa only [state_nat_mul hf] using hf.2.2.2.1 (z * x) ((R x : S) * z) (hdom x)
  · change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · have h := hf.2.2.2.2 (z * x)
    rw [show d * (z * x) = z * (d * x) by ring] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le

end Preorder

def normalizedTranslate (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

private def fIter (z : S) (f₀ : S → ℝ) : ℕ → S → ℝ
  | 0 => f₀
  | n + 1 => normalizedTranslate z (fIter z f₀ n)

private def uSeq (z : S) (f₀ : S → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => uSeq z f₀ n * fIter z f₀ n z

private theorem exists_approx_eigenstate {C : Set (S → ℝ)} {R : S → ℝ}
    (hCconvex : Convex ℝ C) (hCne : C.Nonempty)
    (hCbound : ∀ f ∈ C, ∀ x, 0 ≤ f x ∧ f x ≤ R x)
    (z : S) (hCz : ∀ f ∈ C, 1 ≤ f z)
    (hCmap : MapsTo (normalizedTranslate z) C C)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ g ∈ C, ∃ c : ℝ,
      ∀ x, |g (z * x) - c * g x| ≤ 8 * max (R z) 1 * ε * R x := by
  let q := 1 + ε
  have hq : 1 < q := by linarith
  obtain ⟨f₀, hf₀⟩ := hCne
  have hfIter (n : ℕ) : fIter z f₀ n ∈ C := by
    induction n with
    | zero => exact hf₀
    | succ n ih => exact hCmap ih
  let u := uSeq z f₀
  let B := max (R z) 1
  have hu_ge (n : ℕ) : 1 ≤ u n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact one_le_mul_of_one_le_of_one_le ih (hCz _ (hfIter n))
  have hu_le (n : ℕ) : u n ≤ B ^ n := by
    induction n with
    | zero => simp [u, uSeq]
    | succ n ih =>
      rw [pow_succ]
      exact mul_le_mul ih ((hCbound _ (hfIter n) z).2.trans (le_max_left _ _))
        (by linarith [hCz _ (hfIter n)]) (le_trans zero_le_one (hu_ge n) |>.trans ih)
  let a (c : ℝ) (n : ℕ) : ℝ := u n / c ^ n
  let Ssum (c : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, a c n
  let Unb (c : ℝ) : Prop := ∀ M : ℝ, ∃ N : ℕ, M ≤ Ssum c N
  have ha_pos {c : ℝ} (hc : 0 < c) (n : ℕ) : 0 < a c n :=
    div_pos (lt_of_lt_of_le zero_lt_one (hu_ge n)) (pow_pos hc n)
  have hS_mono {c : ℝ} (hc : 0 < c) {m n : ℕ} (hmn : m ≤ n) : Ssum c m ≤ Ssum c n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun i _ _ => (ha_pos hc i).le
  have hpow_gt (X : ℝ) : ∃ k : ℕ, X ≤ q ^ k :=
    ⟨⌈X / ε⌉₊, by linarith [(div_le_iff₀ hε0).mp (Nat.le_ceil (X / ε)),
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ε) ⌈X / ε⌉₊]⟩
  have hUnb0 : Unb (q ^ 0) := fun M => ⟨⌈M⌉₊, (Nat.le_ceil M).trans <|
    calc (⌈M⌉₊ : ℝ) = ∑ _i ∈ Finset.range ⌈M⌉₊, (1 : ℝ) := by simp
      _ ≤ Ssum (q ^ 0) ⌈M⌉₊ := Finset.sum_le_sum fun i _ => by simpa [a, pow_zero] using hu_ge i⟩
  have hNotUnb {c : ℝ} (hc : 2 * B ≤ c) : ¬ Unb c := by
    intro hU
    obtain ⟨N, hN⟩ := hU 3
    have hcpos : 0 < c := by linarith [le_max_right (R z) 1]
    have hle : Ssum c N ≤ ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum fun i _ => by
        rw [div_pow, one_pow, div_le_div_iff₀ (pow_pos hcpos i) (pow_pos zero_lt_two i), one_mul]
        calc u i * 2 ^ i ≤ B ^ i * 2 ^ i := mul_le_mul_of_nonneg_right (hu_le i) (by positivity)
          _ = (2 * B) ^ i := by ring
          _ ≤ c ^ i := pow_le_pow_left₀ (by positivity) hc i
    have hgeom (n : ℕ) : (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) + 2 * (1 / 2 : ℝ) ^ n = 2 := by
      induction n with
      | zero => norm_num
      | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
    linarith [hgeom N]
  obtain ⟨K, hK⟩ := hpow_gt (2 * B)
  have hexK : ∃ k, ¬ Unb (q ^ k) := ⟨K, hNotUnb hK⟩
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hexK = j + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 => Nat.find_spec hexK (h0 ▸ hUnb0)
  have hUj : Unb (q ^ j) := by_contra fun h => Nat.find_min hexK (hj ▸ Nat.lt_succ_self j) h
  have hNotUj1 : ¬ Unb (q ^ (j + 1)) := hj ▸ Nat.find_spec hexK
  let c := q ^ j
  have hcpos : 0 < c := pow_pos (by linarith) j
  have hcB : c ≤ 2 * B := by by_contra! hgt; exact hNotUnb hgt.le hUj
  obtain ⟨N₀, hN₀⟩ := hUj (max 1 (q - 1)⁻¹)
  have hex : ∃ k : ℕ, a c (N₀ + k) ≤ (q ^ 2 - 1) * Ssum c (N₀ + k) := by
    by_contra! hall
    have hgrow (k : ℕ) : (q ^ 2) ^ k ≤ Ssum c (N₀ + k) := by
      induction k with
      | zero => simpa using (le_max_left 1 (q - 1)⁻¹).trans hN₀
      | succ k ih =>
        dsimp only [Ssum]
        rw [pow_succ', ← Nat.add_assoc, Finset.sum_range_succ]
        calc q ^ 2 * (q ^ 2) ^ k ≤ q ^ 2 * Ssum c (N₀ + k) :=
              mul_le_mul_of_nonneg_left ih (by positivity)
          _ = Ssum c (N₀ + k) + (q ^ 2 - 1) * Ssum c (N₀ + k) := by ring
          _ ≤ Ssum c (N₀ + k) + a c (N₀ + k) := add_le_add le_rfl (hall k).le
    simp only [Unb, not_forall, not_exists, not_le] at hNotUj1
    obtain ⟨M, hM⟩ := hNotUj1
    obtain ⟨k, hk⟩ := hpow_gt (max M 1 * q ^ N₀ + 1)
    have hcmp : Ssum c (N₀ + k) ≤ q ^ (N₀ + k) * Ssum (q ^ (j + 1)) (N₀ + k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have heq : a c i = q ^ i * a (q ^ (j + 1)) i := by
        dsimp [a, c]
        rw [pow_succ, mul_pow, div_mul_eq_div_div, mul_div_cancel₀ _ (pow_ne_zero i (by linarith))]
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hq.le (Nat.le_of_lt (Finset.mem_range.mp hi)))
        (ha_pos (pow_pos (by linarith) _) i).le
    have h1 : q ^ k * q ^ k ≤ q ^ N₀ * max M 1 * q ^ k := calc
      q ^ k * q ^ k ≤ (q ^ 2) ^ k := by rw [← mul_pow, sq]
      _ ≤ Ssum c (N₀ + k) := hgrow k
      _ ≤ q ^ (N₀ + k) * Ssum (q ^ (j + 1)) (N₀ + k) := hcmp
      _ ≤ q ^ (N₀ + k) * max M 1 :=
        mul_le_mul_of_nonneg_left ((hM (N₀ + k)).le.trans (le_max_left _ _)) (by positivity)
      _ = q ^ N₀ * max M 1 * q ^ k := by rw [pow_add]; ring
    have h2 : q ^ k ≤ max M 1 * q ^ N₀ :=
      le_of_mul_le_mul_right (by linarith) (pow_pos (by linarith : 0 < q) k)
    linarith
  obtain ⟨k, hk⟩ := hex
  let N := N₀ + k
  have hSN_pos : 0 < Ssum c N :=
    lt_of_lt_of_le zero_lt_one (((le_max_left 1 (q - 1)⁻¹).trans hN₀).trans (hS_mono hcpos (Nat.le_add_right N₀ k)))
  have h1_le : 1 ≤ (q - 1) * Ssum c N := by
    have h := ((le_max_right 1 (q - 1)⁻¹).trans hN₀).trans (hS_mono hcpos (Nat.le_add_right N₀ k))
    rwa [inv_le_iff_one_le_mul₀' (by linarith)] at h
  let w (i : ℕ) : ℝ := a c i / Ssum c N
  have hw1 : ∑ i ∈ Finset.range N, w i = 1 := by
    simp only [w, div_eq_mul_inv, ← Finset.sum_mul]; exact mul_inv_cancel₀ hSN_pos.ne'
  let g : S → ℝ := ∑ i ∈ Finset.range N, w i • fIter z f₀ i
  refine ⟨g, hCconvex.sum_mem (fun i _ => div_nonneg (ha_pos hcpos i).le hSN_pos.le) hw1 (fun i _ => hfIter i), c, fun x => ?_⟩
  have hstep (i : ℕ) : a c i * fIter z f₀ i (z * x) = c * (a c (i + 1) * fIter z f₀ (i + 1) x) := by
    dsimp [a, u, uSeq, fIter, normalizedTranslate]
    have hfz : fIter z f₀ i z ≠ 0 := by linarith [hCz _ (hfIter i)]
    have hc_ne : c ≠ 0 := hcpos.ne'
    rw [pow_succ]; field_simp
  have htel : (∑ i ∈ Finset.range N, a c i * fIter z f₀ i (z * x)) -
      c * (∑ i ∈ Finset.range N, a c i * fIter z f₀ i x) =
      c * (a c N * fIter z f₀ N x - a c 0 * fIter z f₀ 0 x) := by
    simp_rw [hstep, ← Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [Finset.sum_range_sub (fun i => a c i * fIter z f₀ i x) N]
  have hgx (y : S) : g y = (∑ i ∈ Finset.range N, a c i * fIter z f₀ i y) / Ssum c N := by
    simp only [g, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_right_comm _ (Ssum c N)⁻¹, ← Finset.sum_mul]
  have hdiff : g (z * x) - c * g x =
      c * (a c N * fIter z f₀ N x - fIter z f₀ 0 x) / Ssum c N := by
    rw [hgx (z * x), hgx x, mul_div_assoc', ← sub_div, htel]; simp [a, u, uSeq]
  have hfN := hCbound _ (hfIter N) x
  have hf0 := hCbound _ (hfIter 0) x
  have haN : 0 ≤ a c N := (ha_pos hcpos N).le
  have hR_nonneg : 0 ≤ R x := hf0.1.trans hf0.2
  have habs : |a c N * fIter z f₀ N x - fIter z f₀ 0 x| ≤ (a c N + 1) * R x := by
    rw [abs_le]; constructor <;> nlinarith [hfN.1, hfN.2, hf0.1, hf0.2]
  have ha1 : a c N + 1 ≤ 4 * ε * Ssum c N := by dsimp [q] at hk h1_le; nlinarith
  have hB1 : 1 ≤ B := le_max_right _ _
  rw [hdiff, abs_div, abs_mul, abs_of_pos hcpos, abs_of_pos hSN_pos, div_le_iff₀ hSN_pos]
  calc c * |a c N * fIter z f₀ N x - fIter z f₀ 0 x|
      ≤ (2 * B) * ((a c N + 1) * R x) := mul_le_mul hcB habs (abs_nonneg _) (by positivity)
    _ ≤ (2 * B) * ((4 * ε * Ssum c N) * R x) := by gcongr
    _ = 8 * B * ε * R x * Ssum c N := by ring

private theorem exists_eigenstate {C : Set (S → ℝ)} {R : S → ℝ}
    (hCcompact : IsCompact C) (hCconvex : Convex ℝ C) (hCne : C.Nonempty)
    (hCnorm : ∀ f ∈ C, f 1 = 1)
    (hCbound : ∀ f ∈ C, ∀ x, 0 ≤ f x ∧ f x ≤ R x)
    (z : S) (hCz : ∀ f ∈ C, 1 ≤ f z)
    (hCmap : MapsTo (normalizedTranslate z) C C) :
    ∃ g ∈ C, ∀ x, g (z * x) = g z * g x := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
  let M₀ := 8 * max (R z) 1 * (1 + R 1)
  let E (n : ℕ) : Set C :=
    {g | ∀ x, ((n : ℝ) + 1) * |g.val (z * x) - g.val z * g.val x| ≤ M₀ * R x}
  have hEclosed (n : ℕ) : IsClosed (E n) := by
    simp only [E, ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le
      (continuous_const.mul ((((continuous_apply (z * x)).comp continuous_subtype_val).sub
        (((continuous_apply z).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))).abs))
      continuous_const
  have hEne (n : ℕ) : (E n).Nonempty := by
    let ε : ℝ := ((n : ℝ) + 1)⁻¹
    obtain ⟨g, hgC, c, hgc⟩ := exists_approx_eigenstate hCconvex hCne hCbound z hCz hCmap
      (by positivity) (inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ n + 1))
    refine ⟨⟨g, hgC⟩, fun x => ?_⟩
    have h1 := hgc 1; rw [mul_one, hCnorm g hgC, mul_one] at h1
    have hx := hgc x
    have hgx := (hCbound g hgC x).1
    have hgx2 := (hCbound g hgC x).2
    have hR1 : 0 ≤ R 1 := (hCbound g hgC 1).1.trans (hCbound g hgC 1).2
    have hB : 0 ≤ max (R z) 1 := le_trans zero_le_one (le_max_right _ _)
    have htri : |g (z * x) - g z * g x| ≤ |g (z * x) - c * g x| + |g z - c| * g x := calc
      |g (z * x) - g z * g x| = |(g (z * x) - c * g x) - (g z - c) * g x| := by ring_nf
      _ ≤ |g (z * x) - c * g x| + |(g z - c) * g x| := abs_sub _ _
      _ = |g (z * x) - c * g x| + |g z - c| * g x := by rw [abs_mul, abs_of_nonneg hgx]
    have hmul : |g z - c| * g x ≤ (8 * max (R z) 1 * ε * R 1) * R x :=
      mul_le_mul h1 hgx2 hgx (by positivity)
    have htot : |g (z * x) - g z * g x| ≤ M₀ * R x * ε := by dsimp [M₀]; linarith
    calc ((n : ℝ) + 1) * |g (z * x) - g z * g x|
        ≤ ((n : ℝ) + 1) * (M₀ * R x * ε) := mul_le_mul_of_nonneg_left htot (by positivity)
      _ = M₀ * R x := by dsimp [ε]; field_simp
  have hEfin (s : Finset ℕ) : (⋂ n ∈ s, E n).Nonempty := by
    obtain ⟨g, hg⟩ := hEne (s.sup id)
    exact ⟨g, mem_iInter₂.mpr fun n hn x =>
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right (Finset.le_sup (f := id) hn) 1)
        (abs_nonneg _)).trans (hg x)⟩
  obtain ⟨g, hg⟩ := CompactSpace.iInter_nonempty hEclosed hEfin
  refine ⟨g.val, g.property, fun x => ?_⟩
  by_contra hne
  have hpos : 0 < |g.val (z * x) - g.val z * g.val x| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let N := ⌈M₀ * R x / |g.val (z * x) - g.val z * g.val x|⌉₊
  linarith [mem_iInter.mp hg N x, (div_le_iff₀ hpos).mp (Nat.le_ceil (M₀ * R x / |g.val (z * x) - g.val z * g.val x|))]

theorem exists_monotone_semiringHom_of_normalizedStates [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ R x) ∧ k ≤ χ d := by
  let K := normalizedStates (fun x => (R x : ℝ)) d k
  have hKcompact := normalizedStates_isCompact (fun x => (R x : ℝ)) d k
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let F : {z : S // z ≠ 0} → Set K :=
    fun z => {f | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
  have hFclosed (z : {z : S // z ≠ 0}) : IsClosed (F z) := by
    change IsClosed {f : K | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply (z.val * x)).comp continuous_subtype_val)
        (((continuous_apply z.val).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))
  have hslice (t : Finset {z : S // z ≠ 0}) :
      ∃ C : Set (S → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
        (∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) C C) ∧
        ∀ f ∈ C, ∀ z ∈ t, ∀ x, f (z.val * x) = f z.val * f x := by
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨K, Subset.rfl, hne, hKcompact, normalizedStates_convex _ d k,
        fun z hz _ hf => state_rescale hf z (hunit z hz) (hmulmono z) (hdom z), by simp⟩
    | @insert z t _ ih =>
      obtain ⟨C, hCK, hCne, hCcompact, hCconvex, hCmap, hCt⟩ := ih
      obtain ⟨g, hgC, hgz⟩ := exists_eigenstate hCcompact hCconvex hCne
        (fun _ hf => (hCK hf).2.1) (fun _ hf => (hCK hf).1)
        z.val (fun _ hf => state_one_le (hCK hf) (hunit z.val z.property)) (hCmap z.val z.property)
      let c := g z.val
      let D : Set (S → ℝ) := C ∩ {f | ∀ x, f (z.val * x) = c * f x}
      refine ⟨D, fun _ hf => hCK hf.1, ⟨g, hgC, hgz⟩, ?_, ?_, ?_, ?_⟩
      · refine hCcompact.inter_right ?_
        simp only [ofPred_forall]
        exact isClosed_iInter fun x => isClosed_eq (by fun_prop) (by fun_prop)
      · refine hCconvex.inter fun f hf h hh a b _ _ _ x => ?_
        change a * f (z.val * x) + b * h (z.val * x) = c * (a * f x + b * h x)
        rw [hf x, hh x]; ring
      · intro w hw f hf
        refine ⟨hCmap w hw hf.1, fun x => ?_⟩
        change f (w * (z.val * x)) / f w = c * (f (w * x) / f w)
        rw [show w * (z.val * x) = z.val * (w * x) by ac_rfl, hf.2 (w * x)]; ring
      · intro f hf w hw x
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · have hfc : f w.val = c := by simpa only [mul_one, (hCK hf.1).2.1] using hf.2 1
          rw [hfc]; exact hf.2 x
        · exact hCt f hf.1 w hwt x
  have hFfinite (t : Finset {z : S // z ≠ 0}) : (⋂ z ∈ t, F z).Nonempty := by
    obtain ⟨C, hCK, ⟨f, hf⟩, _, _, _, hCt⟩ := hslice t
    exact ⟨⟨f, hCK hf⟩, mem_iInter₂.mpr fun z hz => hCt f hf z hz⟩
  obtain ⟨⟨f, hf⟩, hfm⟩ := CompactSpace.iInter_nonempty hFclosed hFfinite
  have hfmul (x y : S) : f (x * y) = f x * f y := by
    by_cases hx : x = 0
    · simp [hx, state_zero hf]
    · exact mem_iInter.mp hfm ⟨x, hx⟩ y
  refine ⟨⟨⟨⟨f, hf.2.1⟩, hfmul⟩, state_zero hf, hf.2.2.1⟩, fun x y hxy => hf.2.2.2.1 x y hxy, hf.1, ?_⟩
  simpa only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_one, hf.2.1] using hf.2.2.2.2 1

end States

variable [Nontrivial K]
open TensorSemiring

theorem le_add_right (A B : TensorClass K) : B ≤ A + B := by
  simpa only [zero_add] using add_mono (zero_le A) le_rfl

theorem le_add_left (A B : TensorClass K) : A ≤ A + B := by
  simpa only [add_zero] using add_mono (le_refl A) (zero_le B)

theorem natCast_mono {a b : ℕ} (h : a ≤ b) : (a : TensorClass K) ≤ (b : TensorClass K) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.cast_add]; exact le_add_left (a : TensorClass K) (q : TensorClass K)

theorem pow_mono {T S : TensorClass K} (h : T ≤ S) (n : ℕ) : T ^ n ≤ S ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_mono ih h

theorem add_nsmul_le_of_add_le {D A B : TensorClass K} (h : D + A ≤ D + B) (n : ℕ) :
    D + (n : TensorClass K) * A ≤ D + (n : TensorClass K) * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc D + ((n + 1 : ℕ) : TensorClass K) * A = (D + A) + (n : TensorClass K) * A := by push_cast; ring
      _ ≤ (D + B) + (n : TensorClass K) * A := add_mono h le_rfl
      _ = (D + (n : TensorClass K) * A) + B := by ring
      _ ≤ (D + (n : TensorClass K) * B) + B := add_mono ih le_rfl
      _ = D + ((n + 1 : ℕ) : TensorClass K) * B := by push_cast; ring

theorem spectral_coefficient_le_of_all_nat {ν k D : ℝ} {d : ℕ} (hν : 0 < ν)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν ≤ k := by
  have h1 (n : ℕ) (hn : 1 ≤ n) : (d : ℝ) ^ ν * (n : ℝ) ≤ (n : ℝ) * k + D := by
    have hn0 : (n : ℝ) ≠ 0 := (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn) : (0 : ℝ) < n).ne'
    have hdenom : Tendsto (fun m : ℕ => ν + 1 / ((m : ℝ) + 1)) atTop (𝓝 ν) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := ν)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hexponent : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1))) atTop (𝓝 1) := by
      have h : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1))) atTop (𝓝 (ν / ν)) :=
        (tendsto_const_nhds (x := ν)).div hdenom hν.ne'
      rwa [div_self hν.ne'] at h
    have hpower : Tendsto
        (fun m : ℕ => (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + 1 / ((m : ℝ) + 1))))
        atTop (𝓝 ((d : ℝ) ^ ν * (n : ℝ))) := by
      simpa using tendsto_const_nhds.mul ((Real.continuousAt_const_rpow hn0).tendsto.comp hexponent)
    exact le_of_tendsto' hpower fun m => hbound n hn _ (by positivity)
  by_contra h
  have hgap : 0 < (d : ℝ) ^ ν - k := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (D / ((d : ℝ) ^ ν - k)) 0)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hlarge : D < (n : ℝ) * ((d : ℝ) ^ ν - k) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_left _ _) hn)
  nlinarith [h1 n (by exact_mod_cast hn0)]

theorem tensor_catalytic_obstruction_of_scalar_gain_of_one_le
    {D s : TensorClass K} {d k m : ℕ}
    (hd : 0 < d) (hs1 : 1 ≤ s)
    (hcat' : D + (m : TensorClass K) + (matrixClass (K := K)) d * s ≤ D + (k : TensorClass K) * s) :
    (d : ℝ) ^ (exactRankExponent K) ≤ k := by
  let ν := exactRankExponent K
  have hνpos : 0 < ν := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (exactRankExponent_lower (K := K))
  have hcat : D + (matrixClass (K := K)) d * s ≤ D + (k : TensorClass K) * s :=
    (add_mono (le_add_left D _) le_rfl).trans hcat'
  have hD : D ≤ (rank D : TensorClass K) * s :=
    (mul_one (rank D : TensorClass K) ▸ le_rank D).trans (mul_mono le_rfl hs1)
  apply spectral_coefficient_le_of_all_nat hνpos (D := (rank D : ℝ))
  intro n hn δ hδ
  let B := n * k + rank D
  have habsorb : (n : TensorClass K) * (matrixClass (K := K)) d * s ≤ (B : TensorClass K) * s := calc
    (n : TensorClass K) * (matrixClass (K := K)) d * s ≤
        D + (n : TensorClass K) * ((matrixClass (K := K)) d * s) := by
      rw [mul_assoc]; exact le_add_right D _
    _ ≤ D + (n : TensorClass K) * ((k : TensorClass K) * s) := add_nsmul_le_of_add_le hcat n
    _ ≤ (rank D : TensorClass K) * s + (n : TensorClass K) * ((k : TensorClass K) * s) :=
      add_mono hD le_rfl
    _ = (B : TensorClass K) * s := by dsimp [B]; push_cast; ring
  have hpow (j : ℕ) : (n : TensorClass K) ^ j * (matrixClass (K := K)) d ^ j * s ≤
      (B : TensorClass K) ^ j * s := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc (n : TensorClass K) ^ (j + 1) * (matrixClass (K := K)) d ^ (j + 1) * s =
            ((n : TensorClass K) ^ j * (matrixClass (K := K)) d ^ j) *
              ((n : TensorClass K) * (matrixClass (K := K)) d * s) := by ring
        _ ≤ ((n : TensorClass K) ^ j * (matrixClass (K := K)) d ^ j) * ((B : TensorClass K) * s) :=
          mul_mono le_rfl habsorb
        _ = (B : TensorClass K) * ((n : TensorClass K) ^ j * (matrixClass (K := K)) d ^ j * s) := by ring
        _ ≤ (B : TensorClass K) * ((B : TensorClass K) ^ j * s) := mul_mono le_rfl ih
        _ = (B : TensorClass K) ^ (j + 1) * s := by ring
  let τ := ν + δ
  have hτ : 0 < τ := add_pos hνpos hδ
  obtain ⟨u, hu, huR⟩ := exists_exactMatrixRank_lt_rpow (K := K) (lt_add_of_pos_right _ hδ)
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hu0 : (0 : ℝ) < u := zero_lt_one.trans hu1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (u : ℝ) ^ Real.logb (u : ℝ) (n : ℝ) = n :=
    Real.rpow_logb hu0 (ne_of_gt hu1) (zero_lt_one.trans_le hn1)
  simpa only [B, Nat.cast_add, Nat.cast_mul] using
    le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * rank s) (Nat.cast_nonneg B)
      (by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with j _
        let x := (j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ
        let l := ⌊x⌋₊
        let g := u ^ l
        have hg : 0 < g := pow_pos (by omega) l
        have hx : 0 ≤ x := div_nonneg (mul_nonneg (Nat.cast_nonneg j) (Real.logb_nonneg hu1 hn1)) hτ.le
        have hbudget : ((exactMatrixRank K) u) ^ l ≤ n ^ j := by
          exact_mod_cast (calc
            (((exactMatrixRank K) u : ℝ) ^ l) ≤ ((u : ℝ) ^ τ) ^ l :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) huR.le l
            _ = (u : ℝ) ^ (τ * (l : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
            _ ≤ (u : ℝ) ^ (τ * x) :=
              Real.rpow_le_rpow_of_exponent_le hu1.le (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hτ.le)
            _ = (n : ℝ) ^ j := by
              rw [show τ * x = Real.logb (u : ℝ) (n : ℝ) * (j : ℝ) by dsimp [x]; field_simp,
                Real.rpow_mul hu0.le, hlog, Real.rpow_natCast])
        have hsize : (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * g := by
          simpa only [g, Nat.cast_pow] using (calc
            (n : ℝ) ^ ((j : ℝ) / τ) = (u : ℝ) ^ x := by
              rw [← hlog, ← Real.rpow_mul hu0.le]; congr 1; dsimp [x]; ring
            _ ≤ (u : ℝ) ^ ((l : ℝ) + 1) :=
              Real.rpow_le_rpow_of_exponent_le hu1.le (Nat.lt_floor_add_one x).le
            _ = (u : ℝ) * (u : ℝ) ^ l := by
              rw [Real.rpow_add hu0, Real.rpow_natCast, Real.rpow_one, mul_comm])
        have hMg : (matrixClass (K := K)) g ≤ (n : TensorClass K) ^ j := by
          rw [show g = u ^ l from rfl, matrixClass_pow, ← Nat.cast_pow]
          exact (pow_mono (rank_matrixClass (K := K) u ▸ le_rank _) l).trans
            (by simpa only [Nat.cast_pow] using natCast_mono (K := K) hbudget)
        have hcompare : (matrixClass (K := K)) (d ^ j * g) ≤ ((B ^ j : ℕ) : TensorClass K) * s := calc
          (matrixClass (K := K)) (d ^ j * g) = (matrixClass (K := K)) d ^ j * (matrixClass (K := K)) g := by
            rw [matrixClass_mul, matrixClass_pow]
          _ ≤ (matrixClass (K := K)) d ^ j * (n : TensorClass K) ^ j := mul_mono le_rfl hMg
          _ ≤ (n : TensorClass K) ^ j * (matrixClass (K := K)) d ^ j * s := by
            rw [mul_comm ((matrixClass (K := K)) d ^ j)]
            simpa using mul_mono (le_refl ((n : TensorClass K) ^ j * (matrixClass (K := K)) d ^ j)) hs1
          _ ≤ (B : TensorClass K) ^ j * s := hpow j
          _ = ((B ^ j : ℕ) : TensorClass K) * s := by rw [Nat.cast_pow]
        have hrank : (exactMatrixRank K) (d ^ j * g) ≤ rank s * B ^ j := by
          rw [Nat.mul_comm (rank s), ← rank_matrixClass]
          exact (rank_mono hcompare).trans
            (by simpa only [rank_natCast] using rank_mul_le ((B ^ j : ℕ) : TensorClass K) s)
        have hlow := exactMatrixRank_rpow_lower_of_pos (K := K) (mul_pos (pow_pos hd j) hg)
        have hpow_n : ((n : ℝ) ^ (ν / τ)) ^ j = ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_mul (Nat.cast_nonneg n)]
          congr 1; ring
        calc
          ((d : ℝ) ^ ν * (n : ℝ) ^ (ν / τ)) ^ j =
              (((d ^ j : ℕ) : ℝ) ^ ν) * ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
            rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), hpow_n, Nat.cast_pow]
          _ ≤ (((d ^ j : ℕ) : ℝ) ^ ν) * ((u : ℝ) * g) ^ ν :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsize hνpos.le)
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          _ = (u : ℝ) ^ ν * (((d ^ j * g : ℕ) : ℝ) ^ ν) := by
            rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg u) (Nat.cast_nonneg g),
              Real.mul_rpow (Nat.cast_nonneg (d ^ j)) (Nat.cast_nonneg g)]; ring
          _ ≤ (u : ℝ) ^ ν * ((exactMatrixRank K) (d ^ j * g) : ℝ) :=
            mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (Nat.cast_nonneg u) _)
          _ ≤ (u : ℝ) ^ ν * ((rank s : ℝ) * (B : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hrank) (Real.rpow_nonneg (Nat.cast_nonneg u) _)
          _ = ((u : ℝ) ^ ν * rank s) * (B : ℝ) ^ j := by ring)

theorem classOf_directSum_option {X Y Z ι : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype ι] [di : DecidableEq ι] [dopt : DecidableEq (Option ι)]
    (T : Option ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) =
      classOf (T none) + classOf (Tensor.directSum (fun i => T (some i))) := by
  rw [← classOf_sum]
  symm
  apply classOf_eq_of_reindex optionProdEquiv.symm optionProdEquiv.symm optionProdEquiv.symm
  funext x y z
  cases x <;> cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]

theorem classOf_directSum {X Y Z ι : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype ι] [dec : DecidableEq ι] (T : ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  have hdec : dec = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst dec
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ T : ι → Tensor K X Y Z,
      classOf (Tensor.directSum T) = ∑ i, classOf (T i)) ?_ ?_ ?_ ι T
  · intro α β _ e ih S
    let : Fintype α := Fintype.ofEquiv β e.symm
    have hre : classOf (Tensor.directSum (fun i => S (e i))) = classOf (Tensor.directSum S) := by
      apply classOf_eq_of_reindex (Equiv.prodCongr e (Equiv.refl X))
        (Equiv.prodCongr e (Equiv.refl Y)) (Equiv.prodCongr e (Equiv.refl Z))
      funext x y z
      simp [Tensor.pullback, Tensor.directSum, e.injective.eq_iff]
    rw [← hre, ih]
    exact e.sum_comp (fun i => classOf (S i))
  · intro S
    rw [Finset.sum_eq_zero (fun i _ => i.elim)]
    exact (congrArg classOf (funext fun x : PEmpty × X => x.1.elim)).trans classOf_zero
  · intro α _ ih S
    rw [classOf_directSum_option (di := fun a b => Classical.propDecidable (a = b))
      (dopt := fun a b => Classical.propDecidable (a = b)), ih, Fintype.sum_option]

def PrimitiveClass (K : Type*) [CommSemiring K] [Nontrivial K] :
    Subsemiring (TensorClass K) where
  carrier := {x | x = 0 ∨ 1 ≤ x}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr le_rfl
  add_mem' := by
    rintro a b (rfl | ha) hb
    · simpa only [zero_add] using hb
    · exact Or.inr (ha.trans (le_add_left a b))
  mul_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl (zero_mul 0)
    · exact Or.inl (zero_mul b)
    · exact Or.inl (mul_zero a)
    · exact Or.inr (by simpa only [one_mul] using mul_mono ha hb)

theorem exists_detecting_character {d k : ℕ} (hd : 2 ≤ d)
    (hk : (k : ℝ) < (d : ℝ) ^ (exactRankExponent K)) :
    ∃ χ : Character K, (k : ℝ) ≤ χ.value ((matrixMultiplicationTensor (K := K)) d d d) := by
  let i0 : Fin d := ⟨0, by omega⟩
  let td : PrimitiveClass K := ⟨matrixClass d, Or.inr
    (one_le_classOf_of_coefficient_one
      ⟨(i0, i0), (i0, i0), (i0, i0), by simp [matrixMultiplicationTensor]⟩)⟩
  have h1le (s : PrimitiveClass K) (hs : s ≠ 0) : (1 : PrimitiveClass K) ≤ s :=
    s.2.resolve_left fun h => hs (Subtype.ext h)
  have hno (D s : PrimitiveClass K) (m : ℕ) (hm : 0 < m)
      (hcat : D + (m : PrimitiveClass K) + td * s ≤ D + (k : PrimitiveClass K) * s) : False := by
    change (D : TensorClass K) + (m : TensorClass K) +
        matrixClass d * (s : TensorClass K) ≤
      (D : TensorClass K) + (k : TensorClass K) * (s : TensorClass K) at hcat
    by_cases hs : s = 0
    · subst s
      let n := rank (D : TensorClass K) + 1
      have h1 : ((n * m : ℕ) : TensorClass K) ≤ (D : TensorClass K) := by
        simpa [Nat.cast_mul] using (le_add_right (D : TensorClass K) ((n : TensorClass K) * m)).trans
          (add_nsmul_le_of_add_le (B := 0) (by simpa using hcat) n)
      have h2 : n * m ≤ rank (D : TensorClass K) := by simpa only [rank_natCast] using rank_mono h1
      have h3 : n * 1 ≤ n * m := Nat.mul_le_mul_left n hm
      omega
    · exact (not_lt_of_ge (tensor_catalytic_obstruction_of_scalar_gain_of_one_le
        (K := K) (D := (D : TensorClass K)) (s := (s : TensorClass K))
        (d := d) (k := k) (m := m) (by omega) (h1le s hs) hcat)) hk
  let pRank (T : PrimitiveClass K) : ℕ := rank (T : TensorClass K)
  have hnonempty := normalizedStates_nonempty_of_no_catalyst pRank td k
    (fun T => zero_le (T : TensorClass K))
    (fun T => le_rank (T : TensorClass K))
    (fun _ _ _ _ h₁ h₂ => add_mono h₁ h₂) hno
  have hdom (z x : PrimitiveClass K) : z * x ≤ (pRank x : PrimitiveClass K) * z :=
    (mul_mono (le_refl (z : TensorClass K)) (le_rank (x : TensorClass K))).trans (mul_comm _ _).le
  obtain ⟨φ, hφ, _, hdetect⟩ := exists_monotone_semiringHom_of_normalizedStates
    pRank td (k : ℝ) h1le (fun _ _ _ h => mul_mono le_rfl h) hdom hnonempty
  let stab (x : TensorClass K) : PrimitiveClass K := ⟨x + 1, Or.inr (le_add_right x 1)⟩
  let ψ : TensorClass K →+* ℝ :=
    { toFun := fun x => φ (stab x) - 1
      map_zero' := by
        rw [show stab 0 = 1 from Subtype.ext (zero_add 1), map_one, sub_self]
      map_one' := by
        rw [show stab 1 = 1 + 1 from rfl, map_add, map_one]; ring
      map_add' := fun x y => by
        have h := congrArg φ (Subtype.ext (by ring : (x + y + 1) + 1 = (x + 1) + (y + 1)) :
          stab (x + y) + 1 = stab x + stab y)
        simp only [map_add, map_one] at h
        linarith
      map_mul' := fun x y => by
        have h := congrArg φ (Subtype.ext
          (by ring : (x * y + 1) + (x + 1) + (y + 1) = (x + 1) * (y + 1) + 1 + 1) :
          stab (x * y) + stab x + stab y = stab x * stab y + 1 + 1)
        simp only [map_add, map_one, map_mul] at h
        linarith }
  have hψ : Monotone ψ := fun x y hxy =>
    sub_le_sub_right (hφ (add_mono hxy le_rfl)) 1
  refine ⟨{
    value := fun T => ψ (classOf T)
    nonneg := fun T => by simpa only [ψ.map_zero] using hψ (zero_le (classOf T))
    map_zero := by intro _ _ _ _ _ _; rw [classOf_zero, ψ.map_zero]
    map_one := ψ.map_one
    map_directSum := fun T => by rw [classOf_directSum, map_sum]
    map_product := fun T S => by rw [classOf_product, map_mul]
    monotone := fun T A B C => hψ ((classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩)
  }, ?_⟩
  change (k : ℝ) ≤ φ (stab (matrixClass d)) - 1
  rw [show stab (matrixClass d) = td + 1 from rfl, map_add, map_one]
  linarith

end

end OAI.MatrixMultiplication.AuxiliarySeparation

end
