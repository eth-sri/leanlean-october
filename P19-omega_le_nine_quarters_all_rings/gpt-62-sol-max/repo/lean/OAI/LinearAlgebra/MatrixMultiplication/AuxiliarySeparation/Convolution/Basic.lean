module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Basis.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Vandermonde

public section

@[expose] section

namespace OAI.MatrixMultiplication.Foundation.Tensor

section

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Polynomial local maps whose degree-`k` leading residue is the target. -/
structure PolynomialRestrictionDegeneration (T : IntTensor X Y Z) (S : IntTensor U V W) (k : ℕ) where
  maps : Maps (Polynomial ℤ) U V W X Y Z
  factor : ∀ u v w, ∃ q : Polynomial ℤ,
    restrict maps (fun x y z => Polynomial.C (T x y z)) u v w = Polynomial.X^k * q ∧ q.coeff 0 = S u v w

end

open Polynomial

section

variable {I J L : Type*}
variable [Fintype I] [Fintype J] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq L]

/-- Pull back coordinates and multiply them by prescribed monomials. -/
noncomputable def weightedDegeneration {A B C' : Type*}
    (T : IntTensor I J L) (S : IntTensor A B C') (d : ℕ)
    (f : A → I) (g : B → J) (h : C' → L) (a : A → ℕ) (b : B → ℕ) (c : C' → ℕ)
    (H : ∀ x y z j, j ≤ d →
      (if j = a x + b y + c z then T (f x) (g y) (h z) else 0) = (if j = d then S x y z else 0)) :
    PolynomialRestrictionDegeneration T S d := by
  let M : Maps ℤ[X] A B C' I J L := ⟨fun x => Pi.single (f x) (X ^ a x),
    fun y => Pi.single (g y) (X ^ b y), fun z => Pi.single (h z) (X ^ c z)⟩
  refine ⟨M, fun x y z => ?_⟩
  let P := restrict M (fun i j k => C (T i j k)) x y z
  have hc (j : ℕ) (hj : j ≤ d) : P.coeff j = if j = d then S x y z else 0 := by
    simpa [P, M, restrict, Pi.single_apply, ite_mul, mul_ite, ← pow_add, X_pow_mul_C, coeff_monomial, eq_comm] using H x y z j hj
  obtain ⟨q,hq⟩ : X^d ∣ P := X_pow_dvd_iff.mpr fun j hj => by simpa [hj.ne] using hc j hj.le
  exact ⟨q, hq, by simpa [hq, coeff_X_pow_mul'] using hc d le_rfl⟩

end

open AuxiliarySeparation.TensorSemiring Finset

variable {X Y Z U V W : Type*}

private theorem coeff_expand (p q : ℤ[X]) (d : ℕ) :
    (p*q).coeff d = ∑ i : Fin (d+1), p.coeff i * (Polynomial.X^i.val*q).coeff d := by
  simp only [coeff_X_pow_mul',
    Nat.le_of_lt_succ (Fin.isLt _), ↓reduceIte]
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact (Fin.sum_univ_eq_sum_range (fun i => p.coeff i * q.coeff (d-i)) _).symm

/-- The coefficient at `d` uses only the degrees in `0, ..., d` on each input map. -/
private theorem restrict_coeff [Fintype U] [Fintype V] [Fintype W] (d : ℕ) (T : IntTensor U V W)
    (M : Tensor.Maps ℤ[X] X Y Z U V W) :
    IsRestriction (fun x y z => (Tensor.restrict M (fun u v w => C (T u v w)) x y z).coeff d)
      (Tensor.product (Tensor.diagonal (Fin (d+1) × Fin (d+1))) T) := by
  refine ⟨⟨fun x q => (M.left x q.2).coeff q.1.1, fun y q => (M.middle y q.2).coeff q.1.2,
    fun z q => (Polynomial.X ^ (q.1.1.val+q.1.2.val) * M.right z q.2).coeff d⟩, ?_⟩
  funext x y z
  simp only [Tensor.restrict, finsetSum_coeff, coeff_mul_C]
  simp_rw [mul_assoc (M.left x _), coeff_expand (M.left x _), mul_left_comm (Polynomial.X ^ _),
    coeff_expand (M.middle y _), ← mul_assoc (Polynomial.X ^ _), ← pow_add,
    mul_sum, sum_mul, ← mul_assoc, Nat.add_comm]
  simp_rw [← Fintype.sum_prod_type' (α₁ := Fin (d+1)) (α₂ := Fin (d+1)),
    Finset.sum_comm (t := (Finset.univ : Finset (Fin (d+1) × Fin (d+1))))]
  simp [Tensor.product, Tensor.diagonal, Fintype.sum_prod_type, ite_and, ite_mul]

namespace PolynomialRestrictionDegeneration

variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : IntTensor X Y Z} {S : IntTensor U V W}

/-- The leading coefficient of each tensor power uses only quadratically
many copies, by expanding the first two local maps. -/
theorem extractPowers {k : ℕ}
    (D : PolynomialRestrictionDegeneration T S k) (n : ℕ) :
    IsRestriction (Tensor.power S n) (Tensor.product (Tensor.diagonal (Fin (k*n+1) × Fin (k*n+1))) (Tensor.power T n)) := by
  choose Q hQ hQ₀ using D.factor
  let M : Tensor.Maps (Polynomial ℤ) (Fin n → U) (Fin n → V) (Fin n → W) (Fin n → X) (Fin n → Y) (Fin n → Z) :=
    ⟨fun u x => ∏ i, D.maps.left (u i) (x i), fun v y => ∏ i, D.maps.middle (v i) (y i),
      fun w z => ∏ i, D.maps.right (w i) (z i)⟩
  convert restrict_coeff (k*n) (Tensor.power T n) M using 1
  funext u v w
  have h : Tensor.restrict M (fun x y z => Polynomial.C (Tensor.power T n x y z)) u v w =
      ∏ i, Tensor.restrict D.maps (fun x y z => Polynomial.C (T x y z)) (u i) (v i) (w i) := by
    simp only [M, Tensor.restrict, Tensor.power, Tensor.wordProduct, map_prod, Fintype.prod_sum, Finset.prod_mul_distrib]
  rw [h]
  simp only [Tensor.power, Tensor.wordProduct, hQ]
  simp [Finset.prod_mul_distrib, ← pow_mul,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_zero_prod, hQ₀]

end PolynomialRestrictionDegeneration
end OAI.MatrixMultiplication.Foundation.Tensor

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open Foundation TensorSemiring
open scoped NNReal

/-! Polynomial convolution and its character values. -/

/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : IntTensor (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0


namespace Character

open Polynomial Matrix

noncomputable section

section

variable (χ : Character)
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

/-- The polynomial overhead of extracting coefficients of tensor powers
has no effect on a character, even over the integers. -/
theorem value_polynomialRestrictionDegeneration_le_ring
    {T : IntTensor X Y Z} {S : IntTensor U V W} {k : ℕ}
    (D : Tensor.PolynomialRestrictionDegeneration T S k) : χ.value S ≤ χ.value T := by
  refine NNReal.coe_le_coe.mp (le_of_pow_le_polynomial_mul_pow (C := 1) (d := 2) (k := k) (by positivity) ?_)
  norm_cast
  intro n
  rw [← χ.value_power]
  apply (χ.value_le_of_restriction (D.extractPowers n)).trans
  simp only [χ.map_product, χ.value_power]
  simp [Character.value, Fintype.card_prod, pow_two]

end

section

variable (χ : Character)

/-- The polynomial profile `P(a,b)` normalized by the actual mean exponent. -/
def convolutionProfile (a b : ℕ) : ℝ≥0 :=
  χ.symmetrizedProfile (convolution a b)

/-- Swapping the two polynomial inputs preserves the normalized profile. -/
theorem convolutionProfile_comm (a b : ℕ) :
    χ.convolutionProfile a b = χ.convolutionProfile b a := by
  unfold convolutionProfile
  rw [← χ.symmetrizedProfile_swap12 (convolution a b)]
  apply congrArg χ.classProfile
  apply classOf_eq_of_reindex (Equiv.refl _) (Equiv.refl _)
    (finCongr (by omega : a + b - 1 = b + a - 1))
  ext; simp [Tensor.pullback, convolution, add_comm]

@[simp] theorem convolutionProfile_one : χ.convolutionProfile 1 1 = 1 := by
  change χ.classProfile (classOf (convolution 1 1)) = 1
  rw [show convolution 1 1 = 1 by trivial,
    (classOf_const_one (Z := Fin 1)), map_one]

end

/-- Evaluation at descending powers of the parameter gives a Vandermonde
whose determinant is a power of the parameter times a polynomial with
constant coefficient one. The adjugate interpolates without division. -/
theorem value_convolution_le (χ : Character) (a b : ℕ) :
    χ.value (convolution a b) ≤ (a+b-1 : ℕ) := by
  let m := a+b-1
  let e (i : Fin m) := m-i.val
  let v (i : Fin m) : ℤ[X] := X ^ e i
  let V := vandermonde v
  let d := ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, e j
  let Q := ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - (X : ℤ[X]) ^ (j.val-i.val))
  have hv : V.det = X^d * Q := by
    rw [det_vandermonde]
    calc
      _ = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (X : ℤ[X]) ^ e j * (1 - X ^ (j.val-i.val)) := by
        refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
        have hij : i < j := Finset.mem_Ioi.mp hj
        have he : e i = e j + (j.val-i.val) := by lia
        grind
      _ = _ := by simp [d, Q, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hQ : Q.coeff 0 = 1 := by
    simp_rw [Q, coeff_zero_prod]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    simp; omega
  rw [← χ.value_scalarTensor]
  refine χ.value_polynomialRestrictionDegeneration_le_ring (k := d)
    ⟨⟨fun i q => v q ^ i.val, fun j q => v q ^ j.val, V.adjugate⟩, ?_⟩
  intro i j k
  let p : Fin m := ⟨i.val+j.val, by omega⟩
  have h := congrArg (fun W : Matrix (Fin m) (Fin m) ℤ[X] => W k p) V.adjugate_mul
  refine ⟨if i.val+j.val = k.val then Q else 0, ?_, by split <;> simp_all [convolution]⟩
  rw [mul_ite, mul_zero, ← hv]
  simp [Tensor.restrict, Tensor.diagonal, apply_ite C, ite_and, mul_ite, Finset.sum_ite_irrel]
  simpa [V, p, mul_apply, Matrix.one_apply, smul_eq_mul,
    ← pow_add, mul_assoc, mul_left_comm, mul_comm, Fin.ext_iff, eq_comm] using h

end
end Character
end OAI.MatrixMultiplication.AuxiliarySeparation
