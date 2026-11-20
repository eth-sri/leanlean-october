module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Basic

@[expose] public noncomputable section

/-! The ordered multiplicative monoid of finite tensors modulo mutual linear restriction. -/

namespace OAI.MatrixMultiplication.AuxiliarySeparation.TensorResource
open Foundation
open scoped Kronecker

variable {K : Type*} [CommSemiring K]
variable {X Y Z U V W I J L A B C : Type}
variable [Fintype I] [Fintype J] [Fintype L]

/-- Restriction order on finite coordinate presentations. -/
def IsRestriction (T : Tensor K X Y Z) (S : Tensor K I J L) : Prop :=
  ∃ f g h, T = Tensor.restrict f g h S

theorem IsRestriction.pullback (T : Tensor K I J L) (f : X → I) (g : Y → J) (h : Z → L) :
    IsRestriction (Tensor.pullback f g h T) T := by
  classical
  let δ {A B : Type} (u : A → B) (a : A) (b : B) : K := if b = u a then 1 else 0
  exact ⟨δ f, δ g, δ h, by ext; simp [Tensor.pullback, Tensor.restrict, δ, mul_ite]⟩

variable {T : Tensor K X Y Z} {S : Tensor K U V W} {P : Tensor K I J L} {Q : Tensor K A B C}

theorem IsRestriction.trans [Fintype U] [Fintype V] [Fintype W] : IsRestriction T S → IsRestriction S P → IsRestriction T P := by
  rintro ⟨f,g,h,rfl⟩ ⟨a,b,c,rfl⟩
  refine ⟨Matrix.of f * Matrix.of a, Matrix.of g * Matrix.of b, Matrix.of h * Matrix.of c, ?_⟩
  funext
  simp only [Tensor.restrict, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]; tensor_sums

variable [Fintype A] [Fintype B] [Fintype C]

theorem IsRestriction.product : IsRestriction T P → IsRestriction S Q →
    IsRestriction (Tensor.product T S) (Tensor.product P Q) := by
  rintro ⟨f,g,h,rfl⟩ ⟨a,b,c,rfl⟩
  refine ⟨f ⊗ₖ a, g ⊗ₖ b, h ⊗ₖ c, ?_⟩
  funext
  simp only [Tensor.restrict, Tensor.product, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]; tensor_sums

/-- Keep the finite index types in the representative. Binary operations then
compute directly on coefficients, without repeated conversions to `Fin`. -/
structure FiniteTensor (K : Type*) where
  {X Y Z : Type}
  [fx : Fintype X]
  [fy : Fintype Y]
  [fz : Fintype Z]
  coeff : Tensor K X Y Z

attribute [instance] FiniteTensor.fx FiniteTensor.fy FiniteTensor.fz

instance : Preorder (FiniteTensor K) where
  le a b := IsRestriction a.coeff b.coeff
  le_refl a := IsRestriction.pullback a.coeff id id id
  le_trans _ _ _ := IsRestriction.trans

abbrev TensorClass (K : Type*) [CommSemiring K] := Antisymmetrization (FiniteTensor K) (· ≤ ·)

variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

def classOf (T : Tensor K X Y Z) : TensorClass K := toAntisymmetrization (· ≤ ·) (.mk T)

theorem classOf_le_iff (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := Iff.rfl

theorem classOf_eq_of_reindex (f : X ≃ U) (g : Y ≃ V) (h : Z ≃ W)
    (e : Tensor.pullback f g h S = T) : classOf T = classOf S := by
  subst T
  apply le_antisymm (IsRestriction.pullback ..)
  apply (classOf_le_iff ..).mpr
  convert IsRestriction.pullback (Tensor.pullback f g h S) f.symm g.symm h.symm using 1
  funext; simp [Tensor.pullback]

instance : Mul (TensorClass K) := ⟨Quotient.map₂ (fun a b : FiniteTensor K => .mk (Tensor.product a.coeff b.coeff))
  fun _ _ h _ _ g => ⟨IsRestriction.product h.1 g.1, IsRestriction.product h.2 g.2⟩⟩

instance : One (TensorClass K) := ⟨classOf (unitTensor (K := K))⟩

macro "tensor_relabel " e:term : tactic => `(tactic| refine classOf_eq_of_reindex $e $e $e ?_)
local macro "class_law " e:term : tactic => `(tactic| (
  repeat' rintro ⟨_⟩
  tensor_relabel $e
  funext x y z
  simp [Tensor.pullback, Tensor.product, unitTensor, mul_comm, mul_assoc]))

instance : CommMonoid (TensorClass K) where
  mul_assoc := by class_law Equiv.prodAssoc ..
  mul_comm := by class_law Equiv.prodComm ..
  mul_one := by class_law Equiv.prodPUnit _
  one_mul := by class_law Equiv.punitProd _

instance : IsOrderedMonoid (TensorClass K) where
  mul_le_mul_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact IsRestriction.product h (le_refl c)

end OAI.MatrixMultiplication.AuxiliarySeparation.TensorResource
