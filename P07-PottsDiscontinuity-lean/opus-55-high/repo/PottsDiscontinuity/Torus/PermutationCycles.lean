module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Counting all permutation cycles, including fixed points

The cyclic-orbit quotient is the disjoint union of fixed points and nontrivial
cycle factors. In particular its cardinality controls the sign of a permutation.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.Torus

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

section
variable (p : Perm α)
/-- All cyclic orbits of a permutation, including the singleton orbits. -/
abbrev PermutationCycle  := Quotient (SameCycle.setoid p)

/-- The actual number of cyclic orbits. -/
def permutationCycleCount  : ℕ := Nat.card (PermutationCycle p)

/-- A point records either its singleton orbit or its nontrivial cycle factor. -/
def permutationCycleTag (x : α) :
    Function.fixedPoints p ⊕ {c // c ∈ p.cycleFactorsFinset} :=
  if hx : p x = x then Sum.inl ⟨x, hx⟩
  else Sum.inr ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩

theorem permutationCycleTag_eq_iff (x y : α) :
    permutationCycleTag p x = permutationCycleTag p y ↔ p.SameCycle x y := by
  by_cases hx : p x = x
  · have hs : p.SameCycle x y ↔ x = y :=
      ⟨fun h => h.eq_of_left hx, fun h => h.sameCycle p⟩
    grind [permutationCycleTag]
  · by_cases hy : p y = y
    · have hs : ¬p.SameCycle x y := by
        intro h
        exact hx ((h.apply_eq_self_iff).mpr hy)
      simp_all [permutationCycleTag]
    · simpa only [permutationCycleTag, hx, hy, dite_false, Sum.inr.injEq,
        Subtype.mk.injEq] using
        (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr hx)
          (mem_support.mpr hy)).symm

theorem permutationCycleTag_surjective  :
    Function.Surjective (permutationCycleTag p) := by
  intro z
  rcases z with x | ⟨c, hc⟩
  · have hx : p x.val = x.val := x.property
    exact ⟨x.val, by simp_all [permutationCycleTag]⟩
  · obtain ⟨x, hx⟩ := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    refine ⟨x, ?_⟩
    simp only [permutationCycleTag, (mem_support.mp (mem_cycleFactorsFinset_support_le hc hx)), dite_false, Sum.inr.injEq, Subtype.mk.injEq]
    exact (cycle_is_cycleOf hx hc).symm

/-- The inverse is unique at the level of cyclic orbits; no cycle representative is selected. -/
def permutationCycleEquiv  :
    PermutationCycle p ≃ Function.fixedPoints p ⊕ {c // c ∈ p.cycleFactorsFinset} :=
  Equiv.ofBijective
    (Quotient.lift (permutationCycleTag p)
      (fun x y h => (permutationCycleTag_eq_iff p x y).mpr h)) (by
    constructor
    · intro x y h
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      exact Quotient.sound ((permutationCycleTag_eq_iff p _ _).mp h)
    simp [permutationCycleTag_surjective])

theorem permutationCycleCount_eq  :
    permutationCycleCount p = Fintype.card (Function.fixedPoints p) +
      p.cycleFactorsFinset.card := by
  rw [permutationCycleCount, Nat.card_congr (permutationCycleEquiv p), Nat.card_sum,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Sign parity for the complete cycle count, with singleton cycles included. -/
theorem sign_eq_pow_permutationCycleCount  :
    p.sign = (-1 : ℤˣ) ^ (Fintype.card α + permutationCycleCount p) := by
  have hc : p.cycleType.card = p.cycleFactorsFinset.card := by
    simp only [cycleType_def, Multiset.card_map, Finset.card_def]
  have hf := card_fixedPoints p
  have hn := sum_cycleType_le p
  rw [permutationCycleCount_eq]
  have he : Fintype.card α +
      (Fintype.card (Function.fixedPoints p) + p.cycleFactorsFinset.card) =
      (p.cycleType.sum + p.cycleType.card) +
        2 * Fintype.card (Function.fixedPoints p) := by omega
  rw [he, pow_add, pow_mul]
  norm_num
  exact sign_of_cycleType p
end

end PottsDiscontinuity.Torus
