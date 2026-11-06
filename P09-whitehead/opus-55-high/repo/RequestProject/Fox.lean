import Mathlib
noncomputable section


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

The construction is the standard one: `w ↦ ![![w, ∂w/∂x_i], ![0, 1]]` is a
homomorphism into the units of `2 × 2` matrices over the integral group ring.
-/

namespace FiniteChains


variable {α : Type*} [DecidableEq α]

/-- The integral group ring of the free group on `α`. -/
abbrev FreeGroupRing (α : Type*) := MonoidAlgebra ℤ (FreeGroup α)

/-- The image of a group element in the group ring. -/
def grp (g : FreeGroup α) : FreeGroupRing α := MonoidAlgebra.of ℤ _ g

omit [DecidableEq α] in
@[simp] theorem grp_one : grp (1 : FreeGroup α) = 1 := map_one _

omit [DecidableEq α] in
theorem grp_mul (g h : FreeGroup α) : grp (g * h) = grp g * grp h := map_mul _ _ _

omit [DecidableEq α] in
@[simp] theorem grp_mul_grp_inv (g : FreeGroup α) : grp g * grp g⁻¹ = 1 := by
  rw [← grp_mul]; simp

omit [DecidableEq α] in
@[simp] theorem grp_inv_mul_grp (g : FreeGroup α) : grp g⁻¹ * grp g = 1 := by
  rw [← grp_mul]; simp

/-- The `2 × 2` matrix attached to a generator in the construction of the `i`-th Fox
derivative: `![![x_k, δ_{ik}], ![0, 1]]`, as a unit of the matrix ring. -/
def foxGen (i : α) (k : α) :
    (Matrix (Fin 2) (Fin 2) (FreeGroupRing α))ˣ where
  val := !![grp (FreeGroup.of k), if i = k then 1 else 0; 0, 1]
  inv := !![grp (FreeGroup.of k)⁻¹, -(grp (FreeGroup.of k)⁻¹ * (if i = k then 1 else 0)); 0, 1]
  val_inv := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The homomorphism computing the `i`-th Fox derivative. -/
def foxHom (i : α) :
    FreeGroup α →* (Matrix (Fin 2) (Fin 2) (FreeGroupRing α))ˣ :=
  FreeGroup.lift (foxGen i)

/-- The Fox derivative `∂w/∂x_i` as an element of the integral group ring. -/
def fox (i : α) (w : FreeGroup α) :=
  ((foxHom i w : Matrix (Fin 2) (Fin 2) (FreeGroupRing α))) 0 1

theorem foxHom_entries i w :
    (foxHom i w : Matrix (Fin 2) (Fin 2) (FreeGroupRing α)) 0 0 = grp w ∧
    (foxHom i w) 1 0 = 0 ∧
    (foxHom i w) 1 1 = 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp [foxHom, foxGen, FreeGroup.lift_apply_of]
  | inv_of k _ =>
      have : foxHom i (FreeGroup.of k)⁻¹ = (foxGen i k)⁻¹ := by
        simp [foxHom, FreeGroup.lift_apply_of]
      rw [this]
      tauto
  | mul u v hu hv =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hu.1, hu.2.1, hu.2.2, hv.1, hv.2.1, hv.2.2, grp_mul]

@[simp] theorem fox_one i : fox i (1 : FreeGroup α) = 0 := by
  rfl

/-- `∂x_k/∂x_i = δ_{ik}`. -/
@[simp] theorem fox_of (i k : α) : fox i (FreeGroup.of k) = if i = k then 1 else 0 := by
  simp [fox, foxHom, foxGen, FreeGroup.lift_apply_of]

/-- The product rule `∂(uv)/∂x_i = ∂u/∂x_i + u · ∂v/∂x_i`. -/
theorem fox_mul i (u v : FreeGroup α) :
    fox i (u * v) = fox i u + grp u * fox i v := by
  obtain ⟨h00, h10, h11⟩ := foxHom_entries i u
  have : fox i (u * v)
      = (foxHom i u) 0 0 * fox i v +
        (foxHom i u) 0 1 *
        (foxHom i v) 1 1 := by
    simp [fox, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, h00, (foxHom_entries i v).2.2, mul_one, add_comm]
  rfl

theorem fox_inv i (u : FreeGroup α) :
    fox i u⁻¹ = -(grp u⁻¹ * fox i u) := by
  have h : (0) = fox i u + grp u * fox i u⁻¹ := by
    rw [← fox_mul i u _]; simp
  have h' := eq_neg_of_add_eq_zero_right h.symm
  calc fox i u⁻¹ = grp u⁻¹ * (grp u * fox i u⁻¹) := by
        rw [← mul_assoc, grp_inv_mul_grp, one_mul]
    _ = -(grp u⁻¹ * fox i u) := by simp_all

/-- The augmentation `ℤ[F] → ℤ`. -/
def aug : FreeGroupRing α →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α) 1).toRingHom

omit [DecidableEq α] in
@[simp] theorem aug_grp (g : FreeGroup α) : aug (grp g) = 1 := by
  simp [aug, grp]

/-- Exponent sum of the generator `i` in a word, as a group homomorphism. -/
def expSum (i : α) : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift fun k => Multiplicative.ofAdd (if i = k then (1 : ℤ) else 0)

@[simp] theorem expSum_of (i k : α) :
    Multiplicative.toAdd (expSum i (FreeGroup.of k)) = if i = k then (1 : ℤ) else 0 := by
  simp [expSum, FreeGroup.lift_apply_of]

/-- Augmenting the Fox derivative gives the exponent sum: this is the passage from the
Fox boundary of Remark 1 to the exponent-sum matrix `M` of (3.1). -/
theorem aug_fox i (w : FreeGroup α) :
    aug (fox i w) = Multiplicative.toAdd (expSum i w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp
  | inv_of k h =>
      rw [fox_inv, map_neg, map_mul, aug_grp, one_mul, h, map_inv]
      simp
  | mul u v hu hv => simp [fox_mul, map_mul, hu, hv]
