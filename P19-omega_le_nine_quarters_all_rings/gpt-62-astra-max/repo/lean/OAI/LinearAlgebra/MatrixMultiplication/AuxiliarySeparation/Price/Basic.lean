module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Rank
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Comparison

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation TensorResource
variable {K : Type*} [CommSemiring K] {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

namespace TensorResource

/-- Product of all six leg permutations, as a single monotone multiplicative map. -/
def symmProduct : TensorClass K →*o TensorClass K := triple * triple.comp (permuteHom true)

theorem six_apply (a : TensorClass K) : symmProduct a = a*rotate a*rotate (rotate a) *
    (let b := permuteHom true a; b*rotate b*rotate (rotate b)) := rfl

@[simp] theorem rotate_class (T : Tensor K X Y Z) : rotate (classOf T) = classOf T.cyclic := rfl
@[simp] theorem flip_class (T : Tensor K X Y Z) : permuteHom true (classOf T) = classOf (fun x z y => T x y z) := rfl

theorem symm_dot (m : ℕ) : symmProduct (dotClass (K := K) m) = matrixClass m ^ 2 := by
  have h : permuteHom true (dotClass m) = dotClass (K := K) m := by
    apply congrArg classOf; funext; simp [Tensor.dotPairing, eq_comm]
  simp [six_apply, h, matrix_factors, triple, sq]

theorem symm_scalar (n : ℕ) : symmProduct (scalars (K := K) n) = scalars n ^ 6 := by
  simp [six_apply, rotate, permute_scalar, pow_succ, mul_assoc]

end TensorResource

/-- Normalize the logarithmic price at the square of size four:
the sixfold symmetrized dot pairing of size two then has price two. -/
structure Price (K : Type*) [CommSemiring K] where
  raw : TensorClass K →*o ℝ
  nonnegative (a) : 0 ≤ raw a
  unit : raw (matrixClass 4) = 2

namespace Price
variable (χ : Price K)

abbrev eval := χ.raw.comp symmProduct
def value (T : Tensor K X Y Z) := χ.eval (classOf T)

theorem nonneg (T : Tensor K X Y Z) : 0 ≤ χ.value T := χ.nonnegative _

theorem copies {I : Type} [Fintype I] [DecidableEq I] (T : I → Tensor K X Y Z) {b : TensorClass K}
    (h : ∀ i, classOf (T i) = b) : χ.value (Tensor.directSum T) = χ.eval (scalars (Fintype.card I)) * χ.eval b := by
  simp [value, classOf_copies _ h]

theorem map_product (T : Tensor K X Y Z) (S : Tensor K U V W) :
    χ.value (Tensor.product T S) = χ.value T * χ.value S := map_mul χ.eval (classOf T) (classOf S)

theorem value_restrict (T : Tensor K X Y Z) (f : U → X → K) (g : V → Y → K) (h : W → Z → K) :
    χ.value (Tensor.restrict f g h T) ≤ χ.value T := χ.eval.monotone' ((classOf_le_iff ..).mpr ⟨_,_,_,rfl⟩)

theorem value_pullback_le (T : Tensor K X Y Z) (f : U → X) (g : V → Y) (h : W → Z) :
    χ.value (Tensor.pullback f g h T) ≤ χ.value T := χ.eval.monotone' ((classOf_le_iff ..).mpr (IsRestriction.pullback ..))

@[simp] theorem value_scalarTensor (r : ℕ) : χ.value (scalarTensor (Fin r)) = χ.eval (scalars r) := rfl

theorem value_dot {m : ℕ} (hm : 0 < m) : χ.value (Tensor.dotPairing m) = m := by
  let f := χ.eval.comp dotClass
  have h : f 2 = 2 := by
    change χ.raw (symmProduct (dotClass 2)) = 2
    rw [symm_dot, ← matrixClass_pow]; exact χ.unit
  exact nat_price f h hm

/-- A comparison of raw prices bounds the symmetric scalar price by the
cube of the matrix size. In particular the diagonal restriction supplies a
polynomial bound on coefficient splitting. -/
theorem scalar_le_cube {k d : ℕ} (hd : 0 < d) (h : χ.raw (scalars k) ≤ χ.raw (matrixClass d)) :
    χ.eval (scalars k) ≤ (d:ℝ)^3 := by
  have he : χ.raw (matrixClass d)^2 = d := by
    rw [← map_pow, ← symm_dot]; exact χ.value_dot hd
  change χ.raw (symmProduct (scalars k)) ≤ _
  rw [symm_scalar, map_pow, ← he, ← pow_mul]
  exact pow_le_pow_left₀ (χ.nonnegative _) h _

theorem value_swap23 (T : Tensor K X Y Z) : χ.value (fun x z y => T x y z) = χ.value T := by
  apply congrArg χ.raw
  change symmProduct (classOf (fun x z y => T x y z)) = symmProduct (classOf T)
  simp [six_apply]; ac_rfl

theorem value_swap12 (T : Tensor K X Y Z) : χ.value (fun y x z => T x y z) = χ.value T := by
  apply congrArg χ.raw
  change symmProduct (classOf (fun y x z => T x y z)) = symmProduct (classOf T)
  simp [six_apply]; ac_rfl

end Price

/-- Forming a word of tensors multiplies their classes, by splitting off
one coordinate of each index function at a time. -/
@[simp] theorem classOf_wordTensor {n : ℕ} (T : Fin n → Tensor K X Y Z) :
    classOf (Tensor.word T) = ∏ i, classOf (T i) := by
  induction n with
  | zero =>
    tensor_relabel Equiv.equivPUnit _
    funext; simp [Tensor.word, Tensor.pullback, unitTensor]
  | succ n ih =>
    rw [Fin.prod_univ_succ, ← ih (fun i => T i.succ)]
    let split (I : Type) := (Fin.consEquiv (fun _ : Fin (n+1) => I)).symm
    tensor_relabel split _
    funext; simp [split, Tensor.word, Tensor.product, Tensor.pullback, Fin.prod_univ_succ, Fin.tail]

@[simp] theorem Price.value_power (χ : Price K) (T : Tensor K X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  simp [Price.value, Tensor.power]

end OAI.MatrixMultiplication.AuxiliarySeparation
