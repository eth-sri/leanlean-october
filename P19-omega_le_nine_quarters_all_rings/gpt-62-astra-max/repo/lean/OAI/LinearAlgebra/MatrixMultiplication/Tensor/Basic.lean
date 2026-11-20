module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import Mathlib

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.Foundation
abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

/-! `tensor_sums` matches the outermost finite sum on the right by pulling its
index out through the sums on the left. It then descends under the binder;
products in different orders are identified by associativity and commutativity. -/
section
open Finset
variable {R A B : Type*} [AddCommMonoid R] [Fintype A] [Fintype B]
theorem collect_fintype_sum {f : A → B → R} {g : A → R} (h : ∀ a, g a = ∑ b, f a b) :
    ∑ a, g a = ∑ b, ∑ a, f a b := by simp_rw [h]; exact sum_comm
theorem align_fintype_sum {a : R} {f g : B → R} (e : a = ∑ b, f b) (h : ∀ b, f b = g b) :
    a = ∑ b, g b := by simp_all
syntax "tensor_collect" : tactic
macro_rules | `(tactic| tensor_collect) => `(tactic| first | rfl | apply collect_fintype_sum; intro; tensor_collect)
syntax "tensor_sums" : tactic
macro_rules | `(tactic| tensor_sums) => `(tactic| first | rfl | ac_rfl | (apply align_fintype_sum; · tensor_collect); intro; tensor_sums)
end

namespace Tensor
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

/-- A scheme is an identity of coefficients, with no quantification over
input values and no commutativity assumption on later input rings. -/
def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    ∀ x y z, T x y z = ∑ i, a i x * b i y * c i z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def word {n : ℕ} (T : Fin n → Tensor K X Y Z) : Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

abbrev power (T : Tensor K X Y Z) (n : ℕ) := word (fun _ : Fin n => T)

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

def dotPairing (n : ℕ) : Tensor K Unit (Fin n) (Fin n) :=
  fun _ i j => if i = j then 1 else 0

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

end Tensor
end OAI.MatrixMultiplication.Foundation

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation
variable {K X Y Z U V W : Type*} [CommSemiring K]

/-- The scalar multiplication tensor, the multiplicative unit. -/
def unitTensor : Tensor K PUnit PUnit PUnit := fun _ _ _ => 1

/-- The direct sum of scalar multiplication tensors, in diagonal coordinates. -/
def scalarTensor (I : Type*) [DecidableEq I] : Tensor K I I I :=
  fun i j k => if i = j ∧ i = k then 1 else 0

/-- Square matrix multiplication in coefficient coordinates. -/
def squareTensor (K : Type*) [CommSemiring K] (n : ℕ) :
    Tensor K (Fin n × Fin n) (Fin n × Fin n) (Fin n × Fin n) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

end OAI.MatrixMultiplication.AuxiliarySeparation
