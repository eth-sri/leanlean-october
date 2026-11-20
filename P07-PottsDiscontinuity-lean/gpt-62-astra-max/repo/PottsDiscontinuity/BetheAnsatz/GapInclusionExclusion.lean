module

public import PottsDiscontinuity.BetheAnsatz.GapGeometry

/-!
# Inclusion-exclusion for the finite cyclic gap sum

Companion paper, equation `eq:RS`. Collision events include the last/first pair.
This step is independent of the Bethe equations and of the absence of zero roots.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Pointwise finite inclusion-exclusion, with complex scalar coefficients. -/
theorem no_events_indicator_eq_powerset {ι : Type*} [Fintype ι] (C : ι → Prop) :
    (if ∀ i, ¬ C i then (1 : ℂ) else 0) =
      ∑ S ∈ (univ : Finset ι).powerset, (-1 : ℂ) ^ S.card *
        (if ∀ i ∈ S, C i then 1 else 0) := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun i => if C i then (1 : ℂ) else 0) univ
  have he : (∏ i : ι, (1 - (if C i then (1 : ℂ) else 0))) =
      if ∀ i, ¬ C i then (1 : ℂ) else 0 := by
    have hlocal : ∀ i, (1 - (if C i then (1 : ℂ) else 0)) =
        if ¬ C i then (1 : ℂ) else 0 := by
      grind
    simp_rw [hlocal]
    rw [Finset.prod_ite_zero]
    simp
  rw [he] at hp
  simpa only [Finset.prod_const_one, mul_one, Finset.prod_ite_zero] using hp

/-- Inclusion-exclusion on an arbitrary finite summation domain, without requiring a finite carrier. -/
theorem sum_no_events_eq_powerset {ι α : Type*} [Fintype ι] (s : Finset α)
    (C : ι → α → Prop) (F : α → ℂ) :
    (∑ a ∈ s.filter (fun a => ∀ i, ¬ C i a), F a) =
      ∑ S ∈ (univ : Finset ι).powerset, (-1 : ℂ) ^ S.card *
        ∑ a ∈ s.filter (fun a => ∀ i ∈ S, C i a), F a := by
  rw [Finset.sum_filter]
  have hi : ∀ a, (if ∀ i, ¬ C i a then F a else 0) =
      (if ∀ i, ¬ C i a then (1 : ℂ) else 0) * F a := by
    simp
  simp_rw [hi, no_events_indicator_eq_powerset, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_filter, Finset.mul_sum]
  simp

variable {N n : ℕ}

/-- Collision constraints expressed at each individual coordinate. -/
theorem gapCollision_constraints_iff (x y : Fin (n + 1) → ℤ)
    (S : Finset (Fin (n + 1))) :
    (∀ k ∈ S, gapCollision N x y k) ↔
      ∀ k, (k ∈ S → y k = x k) ∧
        ((finRotate (n + 1)).symm k ∈ S → y k = cyclicPredecessorPositions N x k) := by
  constructor
  · intro h k
    refine ⟨fun hk => (h k hk).1, ?_⟩
    intro hk
    simpa only [gapCollision, Equiv.apply_symm_apply] using (h _ hk).2
  · intro h k hk
    exact ⟨(h k).1 hk, (h _).2 (by grind)⟩

/-- Product domain for a collision set, including the empty domain when constraints conflict. -/
theorem restricted_gapTuples_eq_pi (x : Fin (n + 1) → ℤ)
    (S : Finset (Fin (n + 1))) :
    (gapTuples N x).filter (fun y => ∀ k ∈ S, gapCollision N x y k) =
      Fintype.piFinset (fun k => (Icc (cyclicPredecessorPositions N x k) (x k)).filter
        (fun u => (k ∈ S → u = x k) ∧
          ((finRotate (n + 1)).symm k ∈ S → u = cyclicPredecessorPositions N x k))) := by
  ext y
  simp only [mem_filter, mem_gapTuples, gapCollision_constraints_iff,
    Fintype.mem_piFinset, mem_Icc]
  grind

/-- Strictly positive lengths of the predecessor gaps. -/
theorem cyclicPredecessorPositions_lt {x : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (k : Fin (n + 1)) :
    cyclicPredecessorPositions N x k < x k := by
  induction k using Fin.cases with
  | zero => rw [cyclicPredecessorPositions_zero]; omega
  | succ k =>
    rw [cyclicPredecessorPositions_succ]
    exact hx (by change k.val < k.val + 1; omega)

end PottsDiscontinuity.BetheAnsatz
