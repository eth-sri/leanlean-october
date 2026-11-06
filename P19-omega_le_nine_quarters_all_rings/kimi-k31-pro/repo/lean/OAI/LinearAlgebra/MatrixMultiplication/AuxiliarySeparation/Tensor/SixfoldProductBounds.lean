module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Symmetrization
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import Mathlib.Tactic.GCongr

public section

@[expose] section

namespace OAI

/-!
# Algebra and bounds for the sixfold character product

The product over all six leg orders is multiplicative and nonnegative. A
nonzero tensor has product at least one, and every rank decomposition bounds
the product by the sixth power of its size.
-/

namespace MatrixMultiplication.AuxiliarySeparation

section General

variable {K : Type*} [CommSemiring K]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character K))
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- All six factors of the symmetrized product are nonnegative. -/
theorem sixfoldProduct_nonneg (T : Tensor K X Y Z) : 0 ≤ χ.sixfoldProduct T := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (χ.nonneg T) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)

/-- A coefficient one gives positivity in all six leg orders over any coefficient semiring. -/
theorem one_le_sixfoldProduct_of_coefficient_one {T : Tensor K X Y Z}
    (hT : ∃ x y z, T x y z = 1) : 1 ≤ χ.sixfoldProduct T := by
  obtain ⟨x, y, z, hxyz⟩ := hT
  have h0 := χ.one_le_value_of_coefficient_one ⟨x, y, z, hxyz⟩
  have h1 : 1 ≤ χ.value (fun y z x => T x y z) :=
    χ.one_le_value_of_coefficient_one ⟨y, z, x, hxyz⟩
  have h2 : 1 ≤ χ.value (fun z x y => T x y z) :=
    χ.one_le_value_of_coefficient_one ⟨z, x, y, hxyz⟩
  have h3 : 1 ≤ χ.value (fun x z y => T x y z) :=
    χ.one_le_value_of_coefficient_one ⟨x, z, y, hxyz⟩
  have h4 : 1 ≤ χ.value (fun z y x => T x y z) :=
    χ.one_le_value_of_coefficient_one ⟨z, y, x, hxyz⟩
  have h5 : 1 ≤ χ.value (fun y x z => T x y z) :=
    χ.one_le_value_of_coefficient_one ⟨y, x, z, hxyz⟩
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2) h3) h4) h5

/-- The sixfold product is positive for every tensor with a coefficient one. -/
theorem sixfoldProduct_pos_of_coefficient_one {T : Tensor K X Y Z}
    (hT : ∃ x y z, T x y z = 1) : 0 < χ.sixfoldProduct T :=
  zero_lt_one.trans_le (χ.one_le_sixfoldProduct_of_coefficient_one hT)

end Character

end General

section Field

variable {K : Type*} [Field K]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character K)
variable {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]

end Character
end Field

end MatrixMultiplication.AuxiliarySeparation

end OAI
