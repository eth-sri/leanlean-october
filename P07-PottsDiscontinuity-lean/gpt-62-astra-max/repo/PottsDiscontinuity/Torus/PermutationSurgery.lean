module

public import PottsDiscontinuity.Torus.PermutationInvariantSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Exact split-and-join counts

A transposition splits one cyclic orbit if its ends lie on that orbit, and joins
two orbits otherwise. The proof uses invariant-function dimensions and sign parity.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Equiv Equiv.Perm Module

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem permutationCycleCount_swap_ne (p : Perm α) {a b : α} (hab : a ≠ b) :
    permutationCycleCount (swap a b * p) ≠ permutationCycleCount p := by
  intro hc
  have hs : (swap a b * p).sign = -p.sign := by
    rw [map_mul, sign_swap hab, neg_one_mul]
  simp_all [sign_eq_pow_permutationCycleCount, hc]

omit [DecidableEq α] in
theorem cycleDifference_eq_zero_of_sameCycle (p : Perm α) {a b : α}
    (h : p.SameCycle a b) : cycleDifference p a b = 0 := by
  apply LinearMap.ext
  intro f
  exact sub_eq_zero.mpr (sameCycle_invariant f.property h)

variable (p : Perm α) {a b : α} (h : ¬p.SameCycle a b)

include h in
theorem cycleDifference_ne_zero_of_not_sameCycle : cycleDifference p a b ≠ 0 := by
  let f : cycleFunctions p := ⟨fun x => if p.SameCycle a x then 1 else 0, by
    intro x
    simp⟩
  intro hz
  have he := LinearMap.congr_fun hz f
  change (if p.SameCycle a a then (1 : ℚ) else 0) -
    (if p.SameCycle a b then 1 else 0) = 0 at he
  simp_all [SameCycle.rfl, h, ite_true, ite_false, sub_zero, one_ne_zero]

/-- Two distinct marked ends on one boundary cycle split that cycle into two. -/
theorem permutationCycleCount_swap_split
    (hab : a ≠ b) (h : p.SameCycle a b) :
    permutationCycleCount (swap a b * p) = permutationCycleCount p + 1 := by
  have hz := cycleDifference_eq_zero_of_sameCycle p h
  have hp : finrank ℚ (LinearMap.ker (cycleDifference p a b)) = permutationCycleCount p := by
    rw [hz, LinearMap.ker_zero, finrank_top, finrank_cycleFunctions]
  have hq := LinearMap.finrank_range_add_finrank_ker (cycleDifference (swap a b * p) a b)
  have he := (cycleDifferenceKernelEquiv p a b).finrank_eq
  have hb := permutationCycleCount_swap_bounds p a b
  have hn := permutationCycleCount_swap_ne p hab
  rw [finrank_cycleFunctions] at hq
  omega

include h in
/-- Marked ends on different boundary cycles join those cycles into one. -/
theorem permutationCycleCount_swap_join :
    permutationCycleCount (swap a b * p) + 1 = permutationCycleCount p := by
  have hz := cycleDifference_ne_zero_of_not_sameCycle p h
  have hp := Module.Dual.finrank_ker_add_one_of_ne_zero hz
  have hq := LinearMap.finrank_range_add_finrank_ker (cycleDifference (swap a b * p) a b)
  have he := (cycleDifferenceKernelEquiv p a b).finrank_eq
  have hn := permutationCycleCount_swap_ne p (fun he => h (he.sameCycle p))
  have hr := finrank_cycleDifference_range_le (swap a b * p) a b
  rw [finrank_cycleFunctions] at hp hq
  omega

end PottsDiscontinuity.Torus
