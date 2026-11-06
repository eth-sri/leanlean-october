import RequestProject.Cockcroft
import RequestProject.FoxNaturality
import RequestProject.Tac


/-!
# Adding one generator and one relator: no new elements of `π₂`

Rule 1 of the structural operation `T` of Section 3.3 replaces an extra generator `z` by a
commutator `[a_z,b_z]`.  The paper performs this in three steps: freely adjoin `b_z`, adjoin
`a_z` together with the relator `a_z b_z a_z^{-1} = z b_z` (an HNN extension along infinite
cyclic subgroups), and finally eliminate `z` by the defining relation.  What the paper needs
of these steps is the generation statement (3.3): the second homotopy group of the enlarged
complex is generated, over the group ring of the enlarged group, by the image of the old one.

This file proves the combinatorial heart of that statement for a one-generator,
one-relator extension of a presentation.  In the model of
`RequestProject/UniversalCoverPi2.lean`, `π₂` of a presentation complex is the module of Fox
cycles, and the result is:

* `FiniteChains.extCycle_new_eq_zero` — a Fox cycle of the extended presentation has
  coefficient `0` on the new two-cell, as soon as the Fox derivative of the new relator with
  respect to the new generator is right-regular in the group ring;
* `FiniteChains.extCycle_old` — consequently its remaining coefficients form a Fox cycle of
  the *old* Fox matrix, read in the group ring of the enlarged group.

The two cases used in the paper are covered by the two regularity criteria proved here:

* `FiniteChains.foxNew_tietze` — for a defining relator `z = s` the derivative is `1`
  (elimination of the pairs `z = [a_z,b_z]`, a Tietze transformation);
* `FiniteChains.foxNew_hnn` and `FiniteChains.mul_one_sub_single_eq_zero` — for a stable
  letter relator `z u z^{-1} = v` the derivative is `1 - v`, which is right-regular exactly
  by the argument that `v` has infinite order (the hypothesis of the HNN step).

Thus, in the combinatorial model, the two extension steps of rule 1 create no new elements
of `π₂` at all: every Fox cycle of the enlarged presentation is a Fox cycle of the old
presentation with coefficients in the bigger group ring.
-/

bwd

namespace FiniteChains

open MonoidAlgebra

section Regular

variable {k G : Type*} [Ring k] [Group G]

/-- **`1 - t` is right-regular when `t` has infinite order.**  If `x (1 - t) = 0` then `x` is
invariant under right translation by `t`, so its support is a union of infinite `t`-orbits,
hence empty.  This is the algebraic form of the paper's remark that the associated elements
of the HNN extension have infinite order. -/
theorem mul_one_sub_single_eq_zero (ht : ¬ IsOfFinOrder t)
    (x : MonoidAlgebra k G) (hx : x * (1 - single t 1) = 0) : x = 0 := by
  have hstep : ∀ h, x.coeff h = x.coeff (h * t⁻¹) := by
    intro h
    have hxt := (sub_eq_zero.mp (by simpa [mul_sub] using hx)).symm
    have h2 := DFunLike.congr_fun (congrArg (·.coeff) hxt) h
    simpa using h2.symm
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (MonoidAlgebra.coeff_injective (Finsupp.ext hall))
  have key : ∀ n, x.coeff (g * (t ^ n)⁻¹) ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ m ih =>
        have hrw : g * (t ^ (m + 1))⁻¹ = g * (t ^ m)⁻¹ * t⁻¹ := by group
        grind
  have hsub : Set.range (fun n => g * (t ^ n)⁻¹) ⊆ x.coeff.support := by
    grind
  have hinj : Function.Injective (fun n => g * (t ^ n)⁻¹) := by
    intro a b hab
    simp [mul_right_inj, inv_inj] at hab
    exact injective_pow_iff_not_isOfFinOrder.mpr ht hab
  exact (Set.infinite_range_of_injective hinj) (Set.Finite.subset x.coeff.support.finite_toSet hsub)

end Regular

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))







/-! ### The two relators used in rule 1 -/
