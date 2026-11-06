module

public import PottsDiscontinuity.Bethe.Theorem23MeanValue
public import PottsDiscontinuity.Bethe.Theorem23StabilityEstimate

/-! # Comparing the step density with the derivative of the counting function -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem rootPartitionPoint_mem_large {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (i : Fin (k + 3)) :
    rootPartitionPoint (k + 1) p (by omega) i ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
  unfold rootPartitionPoint
  split
  · have hb := hp.1 ⟨k + 1 - 1, by omega⟩; constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
  · split
    · have hb := hp.1 ⟨0, by omega⟩; constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
    · have hb := hp.1 ⟨i.val - 1, by omega⟩; constructor <;> linarith [hb.1, hb.2, Real.pi_pos]

theorem exists_rootPartition_cell {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) {t : ℝ} (ht : t ∈ Icc (-Real.pi) Real.pi) :
    ∃ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ t ∧
      t < rootPartitionPoint (k + 1) p (by omega) j.succ := by
  let q := rootPartitionPoint (k + 1) p (by omega)
  have hleft : q 0 ≤ t := by
    rw [show q 0 = p (Fin.last k) - 2 * Real.pi by convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1]
    linarith [ht.1, (hp.1 (Fin.last k)).2]
  have hright : t < q (Fin.last (k + 2)) := by
    rw [show q (Fin.last (k + 2)) = p 0 + 2 * Real.pi by convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1]
    linarith [ht.2, (hp.1 0).1]
  by_contra h
  exact (not_le.mpr hright) (Fin.induction (motive := fun i => q i ≤ t) hleft
    (fun j hj => by_contra fun hlt => h ⟨j, hj, lt_of_not_ge hlt⟩) _)

theorem exists_uniform_countingDerivative_lipschitz {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ L : ℝ, 0 < L ∧ ∀ Δ ≤ Δ₀, ∀ (N n : ℕ), 0 < N →
      ∀ (p : Fin n → ℝ), p ∈ S_n n → 2 * n ≤ N →
      ∀ x ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
      ∀ y ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
        |betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y| ≤ L * |x - y| := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_d1Theta_box_bounds hΔ₀ (3 * Real.pi)
  refine ⟨C / (2 * Real.pi), by positivity, fun Δ hΔ N n hN p hp hs x hx y hy => ?_⟩
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hsize : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
  have hsum : |∑ j : Fin n, (d1Theta Δ x (p j) - d1Theta Δ y (p j))| ≤
      (N : ℝ) * (C * |x - y|) :=
    (Finset.abs_sum_le_sum_abs _ _).trans <|
      (Finset.sum_le_sum fun j _ => by
        have hpj : p j ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) :=
          ⟨by linarith [(hp.1 j).1, Real.pi_pos], by linarith [(hp.1 j).2, Real.pi_pos]⟩
        simpa using (hkernel Δ hΔ).2 x hx (p j) hpj y hy (p j) hpj).trans <|
        by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
           exact mul_le_mul_of_nonneg_right hsize (by positivity)
  rw [show betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y =
      (∑ j : Fin n, (d1Theta Δ x (p j) - d1Theta Δ y (p j))) / ((N : ℝ) * (2 * Real.pi)) by
    rw [Finset.sum_sub_distrib]; unfold betheCountingDerivative; ring,
    abs_div, abs_of_pos (mul_pos hNc (by positivity)),
    div_le_iff₀ (mul_pos hNc (by positivity))]
  exact hsum.trans_eq (by field_simp)

/-- Step-density error is bounded by the counting derivative error plus a mesh
term. Comparing `f_p'(ξ)` directly with `f_p'(t)` avoids evaluating the density
or the weighted norm outside the physical interval. -/
theorem exists_uniform_step_counting_comparison {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀),
      ∀ (N k : ℕ) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
        (hs : 2 * (k + 1) ≤ N), DiscreteBetheEquation Δ N (k + 1) p →
      ∀ (D : ℝ), 0 ≤ D →
      ∀ (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
        |Xi (lamOf Δ) α *
          (rootStepDensity N (k + 1) p hp (by omega) hs (kMap (lamOf Δ) α) -
            rho Δ (kMap (lamOf Δ) α))|)),
      (∀ j : Fin (k + 2),
        rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x) hbdd ≤
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => betheCountingDerivative Δ N (k + 1) p x - rho Δ x)
        (countingError_bddAbove (lt_of_le_of_lt hΔ hΔ₀) N (k + 1) p) + A * D / N := by
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ₀
  obtain ⟨X, hX, hupper⟩ := exists_uniform_Xi_upper_bound hΔ₀
  refine ⟨X * L, mul_pos hX hL, fun Δ hΔ N k p hp hs hBE D hD hbdd hmesh => ?_⟩
  have hNnat : 0 < N := by omega
  have hΔvalid := lt_of_le_of_lt hΔ hΔ₀
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let Sf := densityNorm Δ hΔvalid
    (fun x => betheCountingDerivative Δ N (k + 1) p x - rho Δ x)
    (countingError_bddAbove hΔvalid N (k + 1) p)
  refine csSup_le ⟨_, ⟨⟨0, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, rfl⟩⟩ ?_
  rintro _ ⟨⟨α, hα⟩, rfl⟩
  let t := kMap (lamOf Δ) α
  have ht : t ∈ Icc (-Real.pi) Real.pi := kMap_mem_Icc (lamOf_pos hΔvalid) hα
  obtain ⟨j, hcell⟩ := exists_rootPartition_cell hp ht
  obtain ⟨ξ, hξ, hmean⟩ := exists_betheCountingDerivative_cell_mean hΔvalid hNnat p hp hs hBE j
  have herr : |s t - betheCountingDerivative Δ N (k + 1) p t| ≤ L * (D / (N : ℝ)) := by
    rw [show s t = betheCountingDerivative Δ N (k + 1) p ξ from
      (rootStepDensity_on_cell hp (by omega) hs j hcell).trans hmean.symm]
    exact (hLip Δ hΔ N (k + 1) hNnat p hp hs ξ
      ⟨(rootPartitionPoint_mem_large hp j.castSucc).1.trans hξ.1.le,
        hξ.2.le.trans (rootPartitionPoint_mem_large hp j.succ).2⟩
      t ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩).trans
      (mul_le_mul_of_nonneg_left ((abs_le.2 ⟨by linarith [hcell.1, hcell.2, hξ.1, hξ.2],
        by linarith [hcell.1, hcell.2, hξ.1, hξ.2]⟩).trans (hmesh j)) hL.le)
  have hweighted : |Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N (k + 1) p t)| ≤
      X * (L * (D / (N : ℝ))) := by
    rw [abs_mul, abs_of_pos (Xi_pos (lamOf_pos hΔvalid) α)]
    exact mul_le_mul (hupper Δ hΔ α) herr (abs_nonneg _) hX.le
  have hfpoint : |Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p t - rho Δ t)| ≤ Sf :=
    densityNorm_pointwise_le hΔvalid _ (countingError_bddAbove hΔvalid N (k + 1) p) Sf le_rfl hα
  change |Xi (lamOf Δ) α * (s t - rho Δ t)| ≤ Sf + (X * L) * D / N
  rw [show Xi (lamOf Δ) α * (s t - rho Δ t) =
    Xi (lamOf Δ) α * (s t - betheCountingDerivative Δ N (k + 1) p t) +
      Xi (lamOf Δ) α * (betheCountingDerivative Δ N (k + 1) p t - rho Δ t) by ring]
  exact (abs_add_le _ _).trans ((add_le_add hweighted hfpoint).trans_eq (by ring))

end PottsDiscontinuity.Bethe
