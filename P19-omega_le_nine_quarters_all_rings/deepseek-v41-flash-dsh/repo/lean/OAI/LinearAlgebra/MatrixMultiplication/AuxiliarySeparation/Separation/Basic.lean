module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.FiniteProjection
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic

public section

@[expose] section

namespace OAI

/-!
# The tensor map with an arbitrary Fourier period

The branches have a common first coordinate space and common sizes on the other
two legs. Their second and third coordinates carry a matching sector label.
The three maps below are independent linear substitutions on the three legs of
`L` complete copies of the source tensor.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]
variable {M L : ℕ} {X Y Z : Type*}

/-- The paper numbers sectors from one, while `Fin M` numbers them from zero. -/
def sectorNumber (i : Fin M) : ℤ := (i.val : ℤ) + 1

theorem sectorNumber_bounds (i : Fin M) :
    1 ≤ sectorNumber i ∧ sectorNumber i ≤ M := by
  have hi := i.isLt
  unfold sectorNumber
  omega

theorem sectorNumber_injective : Function.Injective (@sectorNumber M) := by
  intro i j hij
  apply Fin.ext
  unfold sectorNumber at hij
  omega

/-- Branches sharing X, with matching and disjoint Y and Z sectors. -/
def sharedFirstTensor {K : Type*} [CommSemiring K] (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

theorem restrict_constantCopies
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    (T : Tensor K A B C)
    (a : A' → R × A → K) (b : B' → R × B → K) (c : C' → R × C → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict a b c (Tensor.directSum (fun _ : R => T)) x y z =
      ∑ r : R, ∑ i, ∑ j, ∑ k, a x (r, i) * b y (r, j) * c z (r, k) * T i j k := by
  classical
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, mul_ite, ite_and]

theorem restrict_constantCopies_delta
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor K A B C) (fa : A' → A) (fb : B' → B) (fc : C' → C)
    (a : A' → R → K) (b : B' → R → K) (c : C' → R → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict
        (fun x r => if r.2 = fa x then a x r.1 else 0)
        (fun y r => if r.2 = fb y then b y r.1 else 0)
        (fun z r => if r.2 = fc z then c z r.1 else 0)
        (Tensor.directSum (fun _ : R => T)) x y z =
      (∑ r : R, a x r * b y r * c z r) * T (fa x) (fb y) (fc z) := by
  rw [restrict_constantCopies]
  simp [ite_mul, mul_ite, Finset.sum_mul]

/-- The surviving tensor: sector labels match on all three legs, while the
additional second/third coordinates form a dot product. -/
def separationTarget {K : Type*} [CommSemiring K] (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then
    B y.1.1 x.1 y.1.2 z.1.2 else 0

/-- The first-leg relabeling adds the trivial first coordinate of the dot product. -/
def separationFirstEquiv : (X × Fin M) ≃ (Fin M × (X × Unit)) where
  toFun x := (x.2, (x.1, ()))
  invFun x := (x.2.1, x.1)
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨h, x, u⟩; cases u; rfl

/-- The other two relabelings merely reassociate their coordinates. -/
def separationSideEquiv (A : Type*) : ((Fin M × A) × Fin M) ≃
    (Fin M × (A × Fin M)) := Equiv.prodAssoc _ _ _

/-- The separated target, expressed as a genuine full direct sum of products. -/
theorem separationTarget_eq_directSum {K : Type*} [CommSemiring K]
    (B : Fin M → Tensor K X Y Z) :
    separationTarget B =
      Tensor.pullback
        separationFirstEquiv (separationSideEquiv Y) (separationSideEquiv Z)
        (Tensor.directSum (fun h => Tensor.product (B h)
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin M)))))) := by
  classical
  funext x y z
  simp only [separationTarget, Tensor.pullback, Tensor.directSum, Tensor.product,
    Tensor.cyclic, Tensor.dotPairing, separationFirstEquiv, separationSideEquiv,
    Equiv.coe_fn_mk, Equiv.prodAssoc_apply]
  by_cases hxy : x.2 = y.1.1
  · by_cases hyz : y.1.1 = z.1.1
    · simp [hxy, hyz]
    · simp [hxy, hyz]
  · simp [hxy]

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
