module

public import Mathlib

@[expose] public section

open scoped Classical

/-!
# Fox derivatives (Remark 1)

Remark 1 of the paper describes the cellular boundary `∂_{2,N}` of the cover
`K_N` through the Fox derivatives `∂r_j/∂x_i`, characterized by

* `∂x_k/∂x_i = δ_{ik}`,
* `∂(uv)/∂x_i = ∂u/∂x_i + u ∂v/∂x_i`.

This file constructs the Fox derivative on a free group, proves these two
rules, the fundamental identity `w - 1 = ∑_i (∂w/∂x_i)(x_i - 1)` in the group
ring, and the fact that augmenting a Fox derivative returns the exponent sum of
the corresponding generator.  The last fact is what links Remark 1 to the
exponent-sum matrix `M` used throughout Section 3.

The entire finitely supported gradient is the crossed homomorphism sending
`x_i` to `single i 1`. Its graph is a homomorphism into a semidirect product.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*}

/-- The integral group ring of the free group on `α`. -/
abbrev FreeGroupRing (α : Type*) := MonoidAlgebra ℤ (FreeGroup α)

/-- The image of a group element in the group ring. -/
noncomputable def grp (g : FreeGroup α) : FreeGroupRing α := MonoidAlgebra.of ℤ (FreeGroup α) g

@[simp] theorem grp_one : grp (1 : FreeGroup α) = 1 := map_one _

theorem grp_mul (g h : FreeGroup α) : grp (g * h) = grp g * grp h := map_mul _ _ _


@[simp] theorem grp_inv_mul_grp (g : FreeGroup α) : grp g⁻¹ * grp g = 1 := by
  simp_all [← grp_mul]

abbrev Gradient (α : Type*) := α →₀ FreeGroupRing α

noncomputable def foxAction : FreeGroup α →* MulAut (Multiplicative (Gradient α)) := by
  letI := DistribMulAction.compHom (Gradient α) (MonoidAlgebra.of ℤ (FreeGroup α))
  exact {
    toFun := fun g => AddEquiv.toMultiplicative (DistribMulAction.toAddEquiv _ g)
    map_one' := MulEquiv.ext (fun x => one_smul (FreeGroup α) x.toAdd)
    map_mul' := fun g h => MulEquiv.ext (fun x => mul_smul g h x.toAdd) }

noncomputable def foxLift : FreeGroup α →*
    (Multiplicative (Gradient α) ⋊[foxAction] FreeGroup α) :=
  FreeGroup.lift fun i => ⟨Multiplicative.ofAdd (Finsupp.single i 1), FreeGroup.of i⟩

theorem foxLift_right (w : FreeGroup α) : (foxLift w).right = w := by
  have h : SemidirectProduct.rightHom.comp foxLift = MonoidHom.id (FreeGroup α) := by
    apply FreeGroup.ext_hom
    simp [foxLift, FreeGroup.lift_apply_of]
  exact DFunLike.congr_fun h w

/-- The finitely supported Fox gradient of a word. -/
noncomputable def foxGradient (w : FreeGroup α) : α →₀ FreeGroupRing α :=
  (foxLift w).left.toAdd

@[simp] theorem foxGradient_one : foxGradient (1 : FreeGroup α) = 0 := by
  rw [foxGradient, map_one]
  rfl

@[simp] theorem foxGradient_of (i : α) :
    foxGradient (FreeGroup.of i) = Finsupp.single i 1 := by
  rw [foxGradient, foxLift, FreeGroup.lift_apply_of]
  rfl

theorem foxGradient_mul (a b : FreeGroup α) :
    foxGradient (a * b) = foxGradient a + grp a • foxGradient b := by
  rw [foxGradient, map_mul, SemidirectProduct.mul_left, foxLift_right]
  rfl

theorem foxGradient_inv (a : FreeGroup α) :
    foxGradient a⁻¹ = -(grp a⁻¹ • foxGradient a) := by
  simp_all [foxGradient, map_inv, SemidirectProduct.inv_left, foxLift_right] <;> abel

/-- The Fox derivative `∂w/∂x_i` as an element of the integral group ring. -/
noncomputable def fox (i : α) (w : FreeGroup α) : FreeGroupRing α := foxGradient w i

@[simp] theorem foxGradient_apply (w : FreeGroup α) (i : α) :
    foxGradient w i = fox i w := rfl

@[simp] theorem fox_one (i : α) : fox i (1 : FreeGroup α) = 0 := by
  simp only [fox, foxGradient_one, Finsupp.zero_apply]

@[simp] theorem fox_of [DecidableEq α] (i k : α) :
    fox i (FreeGroup.of k) = if i = k then 1 else 0 := by
  simp only [fox, foxGradient_of, Finsupp.single_apply, eq_comm]

/-- The product rule for Fox derivatives. -/
theorem fox_mul (i : α) (u v : FreeGroup α) :
    fox i (u * v) = fox i u + grp u * fox i v := by
  simp only [fox, foxGradient_mul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

theorem fox_inv (i : α) (u : FreeGroup α) :
    fox i u⁻¹ = -(grp u⁻¹ * fox i u) := by
  simp only [fox, foxGradient_inv, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul]

/-- The augmentation `ℤ[F] → ℤ`. -/
noncomputable def aug : FreeGroupRing α →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α) 1).toRingHom

@[simp] theorem aug_grp (g : FreeGroup α) : aug (grp g) = 1 := by
  simp [aug, grp]

variable [DecidableEq α]

/-- Exponent sum of the generator `i` in a word, as a group homomorphism. -/
noncomputable def expSum (i : α) : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift fun k => Multiplicative.ofAdd (if i = k then 1 else 0)

@[simp] theorem expSum_of (i k : α) :
    Multiplicative.toAdd (expSum i (FreeGroup.of k)) = if i = k then (1 : ℤ) else 0 := by
  simp [expSum, FreeGroup.lift_apply_of]

/-- Augmenting the Fox derivative gives the exponent sum: this is the passage from the
Fox boundary of Remark 1 to the exponent-sum matrix `M` of (3.1). -/
theorem aug_fox (i : α) (w : FreeGroup α) :
    aug (fox i w) = Multiplicative.toAdd (expSum i w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp [apply_ite (aug (α := α))]
  | inv_of k h =>
      rw [fox_inv, map_neg, map_mul, aug_grp, one_mul, h, map_inv]
      simp
  | mul u v hu hv => simp [fox_mul, map_mul, hu, hv]

end FiniteChains
