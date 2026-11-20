module

public import PottsDiscontinuity.BetheAnsatz.GapGeometry
public import PottsDiscontinuity.BetheAnsatz.GapGeometric

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
      intro i
      by_cases hi : C i <;> simp [hi]
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
  apply Finset.sum_congr rfl
  simp

/-- Finite gap sums with a common choice of endpoint weights. -/
noncomputable def weightedGapWeight {N n : ℕ} (b d : ℂ) (x y : Fin (n+1) → ℤ) : ℂ :=
  ∏ k, gapPointWeight b d (cyclicPredecessorPositions N x k) (x k) (y k)

noncomputable def weightedGapSum {N n : ℕ} (b d : ℂ) (x : Fin (n+1) → ℤ)
    (p : Fin (n+1) → ℝ) (σ : Equiv.Perm (Fin (n+1))) : ℂ :=
  ∑ y ∈ distinctGapTuples N x, weightedGapWeight (N := N) b d x y * planeWave p σ y

lemma weightedGapSum_eq_cyclicGapSum {N n : ℕ} (c : ℝ) (x : Fin (n+1) → ℤ)
    (p : Fin (n+1) → ℝ) (σ : Equiv.Perm (Fin (n+1))) :
    weightedGapSum (N := N) 1 ((c:ℂ)^2) x p σ = cyclicGapSum c N x p σ := by
  simp [weightedGapSum, weightedGapWeight, cyclicGapSum, gapWeight, gapPointWeight, ite_or]

/-- The source's `R_σ(S)`, with every collision in S imposed. -/
noncomputable def restrictedGapSum {N n : ℕ} (B D : ℂ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin (n + 1))) : ℂ :=
  ∑ y ∈ (gapTuples N x).filter (fun y => ∀ k ∈ S, gapCollision N x y k),
    weightedGapWeight (N := N) B D x y * planeWave p σ y

/-- Equation `eq:RS`, retaining exactly the modulo-N exclusion of the source gap sum. -/
theorem weightedGapSum_inclusion_exclusion {N n : ℕ} (B D : ℂ) (x : Fin (n + 2) → ℤ)
    (p : Fin (n + 2) → ℝ) (σ : Equiv.Perm (Fin (n + 2)))
    (hx : StrictMono x) (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ)) :
    weightedGapSum (N := N) B D x p σ =
      ∑ S ∈ (univ : Finset (Fin (n + 2))).powerset,
        (-1 : ℂ) ^ S.card * restrictedGapSum (N := N) B D x p σ S := by
  have he : distinctGapTuples N x =
      (gapTuples N x).filter (fun y => ∀ k, ¬ gapCollision N x y k) := by
    ext y
    simp only [distinctGapTuples, mem_filter]
    constructor
    · rintro ⟨hy, hi⟩
      exact ⟨hy, (distinct_residues_iff_no_gapCollision hx hspan hy).mp hi⟩
    · rintro ⟨hy, hi⟩
      exact ⟨hy, (distinct_residues_iff_no_gapCollision hx hspan hy).mpr hi⟩
  unfold weightedGapSum restrictedGapSum
  rw [he]
  convert sum_no_events_eq_powerset (gapTuples N x) (fun k y => gapCollision N x y k)
    (fun y => weightedGapWeight (N := N) B D x y * planeWave p σ y) using 1
  · apply Finset.sum_congr
    · ext y
      simp
    simp
  · apply Finset.sum_congr rfl
    intro S _
    congr 1
    apply Finset.sum_congr
    · ext y
      simp
    simp

end PottsDiscontinuity.BetheAnsatz
