module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

@[expose] section

namespace OAI.MatrixMultiplication.Foundation

/-! Finite coefficient tensors, local restrictions, and rank. -/

open scoped BigOperators Kronecker Matrix

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K
abbrev IntTensor := Tensor ℤ

namespace Tensor

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

/-- Three local matrices, with target coordinates indexing the rows. -/
structure Maps (K X Y Z U V W : Type*) where
  left : Matrix X U K
  middle : Matrix Y V K
  right : Matrix Z W K

variable [Fintype X] [Fintype Y] [Fintype Z]

def restrict
    (M : Maps K X' Y' Z' X Y Z) (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    M.left x' x * M.middle y' y * M.right z' z * T x y z

def diagonal (I : Type*) [DecidableEq I] : IntTensor I I I :=
  fun i j k => if i = j ∧ i = k then 1 else 0

abbrev RankAtMost (T : IntTensor X Y Z) (r : ℕ) : Prop :=
  ∃ M, T = restrict M (diagonal (Fin r))

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem restrict_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (M : Maps ℤ X Y Z I I I) :
    restrict M (diagonal I) = fun x y z => ∑ i, M.left x i * M.middle y i * M.right z i := by
  ext; simp [restrict, diagonal, mul_ite, ite_and]

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

/-- Tensor product of any finite family, with independent coordinate types. -/
def wordProduct {n : ℕ} {X Y Z : Fin n → Type*} (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor K (∀ i, X i) (∀ i, Y i) (∀ i, Z i) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

abbrev power (T : Tensor K X Y Z) (n : ℕ) := wordProduct (fun _ : Fin n => T)

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X := fun y z x => T x y z

def squareCoefficients (n : ℕ) : IntTensor (Fin n × Fin n) (Fin n × Fin n) (Fin n × Fin n) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      ⟨fun x => Pi.single (fx x) 1, fun y => Pi.single (fy y) 1, fun z => Pi.single (fz z) 1⟩ T := by
  ext; simp [pullback, restrict, Pi.single_apply, ite_mul, mul_ite]

def Maps.comp [Fintype X'] [Fintype Y'] [Fintype Z']
    (L : Maps K X'' Y'' Z'' X' Y' Z') (M : Maps K X' Y' Z' X Y Z) :
    Maps K X'' Y'' Z'' X Y Z :=
  ⟨L.left * M.left,
    L.middle * M.middle, L.right * M.right⟩

private theorem restrict_as_mulVec
    (M : Maps K X' Y' Z' X Y Z) (T : Tensor K X Y Z) (x : X') (y : Y') (z : Z') :
    restrict M T x y z = ((M.left ⊗ₖ (M.middle ⊗ₖ M.right)) *ᵥ
      (fun p => T p.1 p.2.1 p.2.2)) (x,y,z) := by
  simp [restrict, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mul_assoc]

theorem restrict_restrict
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (M : Maps K X' Y' Z' X Y Z) (L : Maps K X'' Y'' Z'' X' Y' Z')
    (T : Tensor K X Y Z) :
    restrict L (restrict M T) = restrict (L.comp M) T := by
  funext x y z
  simp_rw [restrict_as_mulVec]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

def Maps.product {U V W U' V' W' : Type*}
    (M : Maps K X' Y' Z' X Y Z) (L : Maps K U' V' W' U V W) :
    Maps K (X' × U') (Y' × V') (Z' × W') (X × U) (Y × V) (Z × W) :=
  ⟨M.left ⊗ₖ L.left, M.middle ⊗ₖ L.middle, M.right ⊗ₖ L.right⟩

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype U] [Fintype V] [Fintype W]
    (M : Maps K X' Y' Z' X Y Z) (L : Maps K U' V' W' U V W)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (M.product L) (product T S) = product (restrict M T) (restrict L S) := by
  ext x y z
  simp only [product, restrict_as_mulVec, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  apply Fintype.sum_equiv (((Equiv.refl _).prodCongr (Equiv.prodProdProdComm _ _ _ _)).trans
    (Equiv.prodProdProdComm _ _ _ _))
  intro p
  simp [Maps.product, Matrix.kroneckerMap_apply, Equiv.prodProdProdComm]
  ring

end Tensor
end OAI.MatrixMultiplication.Foundation
