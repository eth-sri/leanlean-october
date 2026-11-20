module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.Convolution
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Price.Basic

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation TensorResource

def sharedFirstTensor {K I X Y Z : Type*} [CommSemiring K] [DecidableEq I] (B : I → Tensor K X Y Z) : Tensor K X (I × Y) (I × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

namespace Integral
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- On the convolution support the excess weight is `(g-h)^2`. -/
private theorem tag_weight {g h u v : ℕ} (he : g+u = h+v) :
    h^2+2*h*v ≤ g^2+2*h*u ∧ (g^2+2*h*u = h^2+2*h*v ↔ g = h ∧ u = v) := by
  zify at *
  have eqn : (g:ℤ)^2+2*h*u = h^2+2*h*v+(g-h)^2 := by linear_combination 2 * h * he
  have := sq_nonneg ((g:ℤ)-h)
  rw [eqn]; simp; omega

/-- Match the linear phase by convolution and keep the diagonal weights. The
filtered tensor is the full direct sum of the branches, each tensored with a
first-leg dot pairing. Cancel the branch count when all values agree. -/
theorem separate {K : Type*} [CommRing K] (χ : Price K) {m : ℕ} (hm : 0 < m)
    (B : Fin m → Tensor K X Y Z) {v : TensorClass K} (hv : ∀ i, classOf (B i) = v) :
    (m:ℝ) * χ.eval v ≤ χ.eval (scalars 2) * χ.value (sharedFirstTensor B) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let m := n+1
  let S := Tensor.product (sharedFirstTensor B) (convolution (K := K) n n)
  let a (x : Fin m × (X × Unit)) := (x.2.1,x.1)
  let b (y : Fin m × (Y × Fin m)) := ((y.1,y.2.1),y.2.2)
  let c (z : Fin m × (Z × Fin m)) := ((z.1,z.2.1),shift z.1 z.2.2)
  let H := Tensor.directSum fun i => Tensor.product (B i) (Tensor.dotPairing m)
  have hh := χ.value_weighted S H a b c (fun x => x.1.val^2) (fun y => 2*y.1.val*y.2.2.val)
    (fun z => z.1.val^2+2*z.1.val*z.2.2.val) (by
      intro x y z
      have hw := @tag_weight x.1.val z.1.val y.2.2.val z.2.2.val
      simp [H, a, b, c, S, Tensor.directSum, Tensor.product, Tensor.dotPairing, sharedFirstTensor, convolution, shift, Fin.ext_iff]
      split_ifs <;> grind)
  have he i : classOf (Tensor.product (B i) (Tensor.dotPairing m)) = v * dotClass m := congrArg (· * dotClass m) (hv i)
  rw [χ.copies _ he, map_mul] at hh
  change _ * (χ.eval v * χ.value (Tensor.dotPairing m)) ≤ χ.value S at hh
  rw [χ.value_dot hm, χ.map_product] at hh
  have hc : χ.value (convolution n n) ≤ χ.eval (scalars 2 * scalars m) := (χ.value_convolution_le ..).trans
    (χ.eval.monotone' (by rw [← map_mul]; exact scalars.monotone' (by omega)))
  rw [map_mul] at hc
  have hp : 0 < χ.eval (scalars m) := zero_lt_one.trans_le (by
    simpa [m] using χ.eval.monotone' ((scalars (K := K)).monotone' hm))
  apply le_of_mul_le_mul_left (a := χ.eval (scalars m)) _ hp
  simp only [Fintype.card_fin] at hh
  nlinarith only [hh, mul_le_mul_of_nonneg_left hc (χ.nonneg (sharedFirstTensor B))]

end Integral

end OAI.MatrixMultiplication.AuxiliarySeparation
