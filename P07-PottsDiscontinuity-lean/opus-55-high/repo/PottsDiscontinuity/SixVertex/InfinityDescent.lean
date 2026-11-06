module

public import PottsDiscontinuity.SixVertex.InfinityMoves

/-! # Finite descent for independent row states -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- The ordinary sum of occupied positions, used only as a finite descent function. -/
def positionSum (x : Finset (Fin N)) : ℕ := ∑ i ∈ x, i.val

section
variable (i : Fin N)
theorem nxt_val_of_lt (hi : i.val + 1 < N) : (nxt i).val = i.val + 1 := by
  cases N with
  | zero => omega
  | succ k =>
    exact congrArg Fin.val (finRotate_of_lt (show i.val < k by omega))

theorem prv_val_of_pos (hi : 0 < i.val) : (prv i).val = i.val - 1 := by
  let j : Fin N := ⟨i.val - 1, by omega⟩
  have hj : nxt j = i := by
    grind [nxt_val_of_lt]
  grind
end

/-- Rotation one site to the left. -/
def rotateDown (x : Finset (Fin N)) : Finset (Fin N) := x.image prv

@[simp] theorem mem_rotateDown (x : Finset (Fin N)) (i : Fin N) :
    i ∈ rotateDown x ↔ nxt i ∈ x := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    simpa only [prv, nxt, Equiv.apply_symm_apply] using hj
  · intro hi
    exact mem_image.mpr ⟨nxt i, hi, (finRotate N).symm_apply_apply i⟩

theorem NoConsecutiveUp.rotateDown {x : Finset (Fin N)} (hx : NoConsecutiveUp x) :
    NoConsecutiveUp (rotateDown x) := by
  intro i hi hni
  aesop

def unrotateIndependent (x : IndependentState N n) : IndependentState N n :=
  ⟨⟨rotateDown x.1.1, (card_image_of_injective _ (finRotate N).symm.injective).trans x.1.2⟩,
    x.2.rotateDown⟩

@[simp] theorem rotateIndependent_unrotate (x : IndependentState N n) :
    rotateIndependent (unrotateIndependent x) = x := by
  ext i
  simp only [rotateIndependent, unrotateIndependent, mem_rotateUp, mem_rotateDown,
    nxt, prv, Equiv.apply_symm_apply]

theorem unrotateIndependent_reachable (hn : 0 < n) (x : IndependentState N n) :
    Relation.ReflTransGen (fun a b : IndependentState N n =>
      0 < infinityRestriction N n a b) x (unrotateIndependent x) := by
  apply Relation.ReflTransGen.single
  rw [infinityRestriction_symm]
  have he := infinityRestriction_rotate hn (unrotateIndependent x)
  simp_all

/-- If the row does not contain zero, moving every particle left strictly lowers the sum. -/
theorem positionSum_rotateDown_lt (x : Finset (Fin N)) (hne : x.Nonempty)
    (h0 : ∀ i ∈ x, 0 < i.val) : positionSum (rotateDown x) < positionSum x := by
  unfold positionSum rotateDown
  rw [sum_image (fun i _ j _ he => (finRotate N).symm.injective he)]
  apply sum_lt_sum <;> grind [prv_val_of_pos]

section
variable {x : Finset (Fin N)}
/-- Moving one particle to a strictly smaller vacant coordinate lowers the sum. -/
theorem positionSum_jump_lt {i j : Fin N}
    (hi : i ∈ x) (hj : j ∉ x) (hji : j.val < i.val) :
    positionSum (jump x i j) < positionSum x := by
  unfold positionSum jump
  rw [sum_insert (fun h => hj (mem_of_mem_erase h))]
  have he := sum_erase_add x (fun a : Fin N => a.val) hi
  omega

/-- A row closed under subtracting two and containing zero consists of even positions. -/
theorem even_of_closed_two (hx : NoConsecutiveUp x)
    (h0 : ∀ i : Fin N, i.val = 0 → i ∈ x)
    (hc : ∀ i ∈ x, ∀ j : Fin N, 2 ≤ i.val → j.val + 2 = i.val → j ∈ x) :
    ∀ i ∈ x, i.val % 2 = 0 := by
  have hall : ∀ k : ℕ, ∀ i : Fin N, i.val = k → i ∈ x → k % 2 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik hi
      by_cases hk0 : k = 0
      · omega
      by_cases hk1 : k = 1
      · let z : Fin N := ⟨0, by omega⟩
        have hnz : nxt z = i := by
          grind [nxt_val_of_lt]
        exact (hx z (h0 z rfl) (hnz ▸ hi)).elim
      · let j : Fin N := ⟨k - 2, by omega⟩
        have hj := hc i hi j (by omega) (by grind)
        grind
  grind

/-- Closure by two also gives every smaller even coordinate below an occupied coordinate. -/
theorem even_prefix_of_closed_two (he : ∀ i ∈ x, i.val % 2 = 0)
    (hc : ∀ i ∈ x, ∀ j : Fin N, 2 ≤ i.val → j.val + 2 = i.val → j ∈ x) :
    ∀ i ∈ x, ∀ j : Fin N, j.val ≤ i.val → j.val % 2 = 0 → j ∈ x := by
  have hall : ∀ k : ℕ, ∀ i : Fin N, i.val = k → i ∈ x →
      ∀ j : Fin N, j.val ≤ k → j.val % 2 = 0 → j ∈ x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik hi j hj hje
      by_cases hji : j = i
      · simp_all
      have hei := he i hi
      let l : Fin N := ⟨k - 2, by omega⟩
      have hl := hc i hi l (by omega) (by grind)
      grind
  grind
end

/-- Two even initial segments of equal cardinality are identical. -/
theorem eq_of_even_prefix {x y : Finset (Fin N)} (hcard : x.card = y.card)
    (hex : ∀ i ∈ x, i.val % 2 = 0) (hey : ∀ i ∈ y, i.val % 2 = 0)
    (hpx : ∀ i ∈ x, ∀ j : Fin N, j.val ≤ i.val → j.val % 2 = 0 → j ∈ x)
    (hpy : ∀ i ∈ y, ∀ j : Fin N, j.val ≤ i.val → j.val % 2 = 0 → j ∈ y) : x = y := by
  by_cases hsub : x ⊆ y
  · exact eq_of_subset_of_card_le hsub hcard.ge
  · have hyx : y ⊆ x := by
      grind
    have heq := eq_of_subset_of_card_le hyx hcard.le
    grind

end PottsDiscontinuity.SixVertex
