module

public import PottsDiscontinuity.Bethe.Theorem23MeanValue
public import PottsDiscontinuity.Bethe.Theorem23StabilityEstimate

/-! # Comparing the step density with the derivative of the counting function -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section
variable {k : ℕ} {p : Fin (k + 1) → ℝ} (hp : p ∈ S_n (k + 1))
include hp

include hp in
theorem rootPartitionPoint_mem_large (i : Fin (k + 3)) :
    rootPartitionPoint p (by omega) i ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
  unfold rootPartitionPoint
  split
  · have hb := hp.1 ⟨k + 1 - 1, by omega⟩
    grind
  · split
    · have hb := hp.1 ⟨0, by omega⟩
      grind
    · have hb := hp.1 ⟨i.val - 1, by omega⟩
      grind

include hp in
theorem exists_rootPartition_cell {t : ℝ} (ht : t ∈ Icc (-Real.pi) Real.pi) :
    ∃ j : Fin (k + 2), rootPartitionPoint p (by omega) j.castSucc ≤ t ∧
      t < rootPartitionPoint p (by omega) j.succ := by
  let q := rootPartitionPoint p (by omega)
  have hleft : q 0 ≤ t := by
    have heq : q 0 = p (Fin.last k) - 2 * Real.pi := by
      rfl
    linarith [ht.1, (hp.1 (Fin.last k)).2]
  have hright : t < q (Fin.last (k + 2)) := by
    have heq : q (Fin.last (k + 2)) = p 0 + 2 * Real.pi := by
      convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
    linarith [ht.2, (hp.1 0).1]
  by_contra h
  have hstep (j : Fin (k + 2)) (hj : q j.castSucc ≤ t) : q j.succ ≤ t := by
    by_contra hlt
    exact h ⟨j, hj, lt_of_not_ge hlt⟩
  have hall (i : Fin (k + 3)) : q i ≤ t := Fin.induction (by
    have heq : q 0 = p (Fin.last k) - 2 * Real.pi := by
      rfl
    linarith [ht.1, (hp.1 (Fin.last k)).2]) hstep i
  exact (not_le.mpr hright) (hall _)

end

variable {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
include hΔ₀

include hΔ₀ in
theorem exists_uniform_countingDerivative_lipschitz :
    ∃ L, 0 < L ∧ ∀ Δ ≤ Δ₀, ∀ N n, 0 < N →
      ∀ p, p ∈ S_n n → 2 * n ≤ N →
      ∀ x ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
      ∀ y ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
        |betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y| ≤ L * |x - y| := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_d1Theta_box_bounds hΔ₀ _
  refine ⟨C / (2 * Real.pi), by positivity, fun Δ hΔ N n hN p hp hs x hx y hy => ?_⟩
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  let diff (j) := d1Theta Δ x (p j) - d1Theta Δ y (p j)
  have hterm (j : Fin n) : |(diff j)| ≤ C * |x - y| := by
    have hpj : p j ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
      constructor <;> linarith [(hp.1 j).1, (hp.1 j).2, Real.pi_pos]
    simpa using (hkernel Δ hΔ).2 x hx (p j) hpj y hy (p j) hpj
  have hsum : |∑ j, ((diff j))| ≤
      N * (C * |x - y|) := by
    calc
      _ ≤ ∑ j, |(diff j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j, C * |x - y| := Finset.sum_le_sum (fun j _ => hterm j)
      _ = n * (C * |x - y|) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show n ≤ N by omega)) (by positivity)
  have hid : betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y =
      (∑ j, ((diff j))) / (N * (2 * Real.pi)) := by
    rw [Finset.sum_sub_distrib]
    unfold betheCountingDerivative
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hNc (by positivity))]
  apply (div_le_iff₀ (mul_pos hNc (by positivity))).2
  apply hsum.trans_eq
  field_simp

include hΔ₀ in
/-- Step-density error is bounded by the counting derivative error plus a mesh
term. Comparing `f_p'(ξ)` directly with `f_p'(t)` avoids evaluating the density
or the weighted norm outside the physical interval. -/
theorem exists_uniform_step_counting_comparison :
    ∃ A, 0 < A ∧ ∀ Δ (hΔ : Δ ≤ Δ₀),
      ∀ N k (p : Fin (k+1) → ℝ) (hp : p ∈ S_n (k+1))
        (hs : 2*(k+1) ≤ N), DiscreteBetheEquation Δ N (k + 1) p →
      ∀ D, 0 ≤ D →
      ∀ (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
        |Xi (lamOf Δ) α *
          (rootStepDensity N p (by omega) (kMap (lamOf Δ) α) -
            rho Δ (kMap (lamOf Δ) α))|)),
      (∀ j : Fin (k + 2),
        rootPartitionPoint p (by omega) j.succ -
          rootPartitionPoint p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ
        (fun x => rootStepDensity N p (by omega) x - rho Δ x) ≤
      densityNorm Δ
        (fun x => betheCountingDerivative Δ N (k + 1) p x - rho Δ x) + A * D / N := by
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ₀
  obtain ⟨X, hX, hupper⟩ := exists_uniform_Xi_upper_bound hΔ₀
  refine ⟨X * L, mul_pos hX hL, fun Δ hΔ N k p hp hs hBE D hD hbdd hmesh => ?_⟩
  have hNnat : 0 < N := by omega
  have hΔvalid := lt_of_le_of_lt hΔ hΔ₀
  let s := rootStepDensity N p (by omega)
  let Sf := densityNorm Δ
    (fun x => betheCountingDerivative Δ N _ p x - rho Δ x)
  have hpoint (α : ℝ) (hα : α ∈ Icc (-Real.pi) Real.pi) :
      |Xi (lamOf Δ) α * (s (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))| ≤
        Sf + (X * L) * D / N := by
    let t := kMap (lamOf Δ) α
    have ht := kMap_mem_Icc (lamOf_pos hΔvalid) hα
    obtain ⟨j, hcell⟩ := exists_rootPartition_cell hp ht
    obtain ⟨ξ, hξ, hmean⟩ := exists_betheCountingDerivative_cell_mean hΔvalid hNnat p hp hs hBE j
    have hξlarge : ξ ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) :=
      ⟨(rootPartitionPoint_mem_large hp j.castSucc).1.trans hξ.1.le,
        hξ.2.le.trans (rootPartitionPoint_mem_large hp j.succ).2⟩
    have htlarge : t ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
    have hdist : |ξ - t| ≤ rootPartitionPoint p (by omega) j.succ -
        rootPartitionPoint p (by omega) j.castSucc := by
      apply abs_le.2
      grind
    have hstep : s t = betheCountingDerivative Δ N (k + 1) p ξ :=
      (rootStepDensity_on_cell hp hs hcell).trans hmean.symm
    have herr : |s t - betheCountingDerivative Δ N (k + 1) p t| ≤ L * (D / (N : ℝ)) := by
      rw [hstep]
      apply (hLip Δ hΔ N (k + 1) hNnat p hp hs ξ ⟨(rootPartitionPoint_mem_large hp j.castSucc).1.trans hξ.1.le,
        hξ.2.le.trans (rootPartitionPoint_mem_large hp j.succ).2⟩ t (by constructor <;> linarith [ht.1, ht.2, Real.pi_pos])).trans
      exact mul_le_mul_of_nonneg_left (hdist.trans (hmesh j)) hL.le
    have hfpoint :=
      densityNorm_pointwise_le (hΔ := hΔvalid) (f := _) (hbounded := (countingError_bddAbove hΔvalid N (k + 1) p)) Sf le_rfl hα
    have hid : Xi (lamOf Δ) α * (s t - rho Δ t) =
        Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N _ p t) +
          Xi (lamOf Δ) α * (betheCountingDerivative Δ N _ p t - rho Δ t) := by ring
    rw [hid]
    calc
      _ ≤ |Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N _ p t)| +
          |Xi (lamOf Δ) α * (betheCountingDerivative Δ N _ p t - rho Δ t)| := abs_add_le _ _
      _ ≤ X * (L * (D / N)) + Sf := add_le_add (by
        rw [abs_mul, abs_of_pos (Xi_pos (lamOf_pos hΔvalid) α)]
        exact mul_le_mul (hupper Δ hΔ α) herr (abs_nonneg _) hX.le) hfpoint
      _ = _ := by ring
  apply csSup_le
  · exact ⟨_, ⟨⟨0, (by constructor <;> linarith [Real.pi_pos])⟩, rfl⟩⟩
  · rintro _ ⟨α, rfl⟩
    exact hpoint α α.property

end PottsDiscontinuity.Bethe
