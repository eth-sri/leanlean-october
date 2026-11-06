module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import Mathlib.Tactic

public section

@[expose] section

namespace OAI

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [CommSemiring K]

open MatrixMultiplication.Foundation

/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem convolution_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

@[simp] theorem convolution_ne_zero_iff [Nontrivial K] {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k ≠ 0 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_one_iff [Nontrivial K] {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = 1 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

/-- Every pair of input monomials has a valid output coordinate. -/
def convolutionOutput {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b - 1) :=
  ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩

@[simp] theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution (K := K) a b i j (convolutionOutput i j) = 1 := by
  simp [convolutionOutput]

/-- Commuting the two inputs only casts the equal output dimensions. -/
theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k =
      convolution (K := K) b a j i (Fin.cast (by omega) k) := by
  simp only [convolution, Fin.val_cast, Nat.add_comm]

/-- Relabel the output of `C(1,b)` by its actual dimension `b`. -/
def convolutionOneOutputEquiv (b : ℕ) : Fin b ≃ Fin (1 + b - 1) :=
  finCongr (by omega)

/-- Relabel the single input coordinate of `C(1,b)` by `Unit`. -/
def convolutionOneInputEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _i := Subsingleton.elim _ _

/-- `C(1,b)` is the dot-product tensor with the singleton on the first leg. -/
theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback convolutionOneInputEquiv (Equiv.refl (Fin b))
      (convolutionOneOutputEquiv b) (convolution (K := K) 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]

end MatrixMultiplication.AuxiliarySeparation

end OAI
