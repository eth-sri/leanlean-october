module

public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Quantitative quadrature against the root step density -/

public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section
variable {N n : ℕ}
theorem intervalIntegrable_mul_rootStepDensity (p : Fin n → ℝ)
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * rootStepDensity N n p hp hn hs x) volume a b := by
  let c := fun j => rootGapMultiplicity N n hs j /
    ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
  have heq : (fun x => g x * rootStepDensity N n p hp hn hs x) =
      ∑ j : Fin (n + 1),
        (Ico (rootPartitionPoint n p hn j.castSucc) (rootPartitionPoint n p hn j.succ)).indicator
          (fun x => g x * c j) := by
    funext x
    simp [rootStepDensity, Finset.mul_sum, c, Set.indicator, Set.mem_Ico, mul_ite]
  rw [heq]
  apply IntervalIntegrable.sum
  intro j _
  rw [intervalIntegrable_iff]
  exact ((hg.mul continuous_const).intervalIntegrable a b).def'.indicator measurableSet_Ico

theorem rootGapMultiplicity_nonneg (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    0 ≤ rootGapMultiplicity N n hs j := by
  grind [rootGapMultiplicity]
end

section
variable {N n : ℕ} {p : Fin n → ℝ} (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
/-- The integral over any subinterval of one cell is bounded by its full cell
mass times a bound for the test function. -/
theorem root_step_cell_integral_bound {a b G : ℝ} (hG : 0 ≤ G)
    (hab : a ≤ b) (ha : rootPartitionPoint n p hn j.castSucc ≤ a)
    (hb : b ≤ rootPartitionPoint n p hn j.succ)
    {g : ℝ → ℝ} (hbound : ∀ x ∈ Icc a b, |g x| ≤ G) :
    |∫ x in a..b, g x * rootStepDensity N n p hp hn hs x| ≤
      G * rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hgap := rootPartition_gap_pos hp hn j
  let d := rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc
  let c := rootGapMultiplicity N n hs j / ((N : ℝ) * d)
  have hc : 0 ≤ c := div_nonneg (rootGapMultiplicity_nonneg hs j) (by positivity)
  have hpoint : ∀ᵐ x : ℝ, x ∈ uIoc a b →
      ‖g x * rootStepDensity N n p hp hn hs x‖ ≤ G * c := by
    filter_upwards [volume.ae_ne b] with x hne hx
    rw [uIoc_of_le hab] at hx
    rw [rootStepDensity_on_cell hp hn hs j (by grind), Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (hbound x ⟨hx.1.le, hx.2⟩) hc
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    hpoint
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left (show b - a ≤ d by linarith) (mul_nonneg hG hc)).trans_eq (by grind))

theorem root_step_full_cell_mass  :
    (∫ x in rootPartitionPoint n p hn j.castSucc..rootPartitionPoint n p hn j.succ,
      rootStepDensity N n p hp hn hs x) = rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hgap := rootPartition_gap_pos hp hn j
  have heq := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (sub_pos.mp hgap).le
   
    (g := fun _ : ℝ => rootGapMultiplicity N n hs j /
      ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)))
    (fun x hx => rootStepDensity_on_cell hp hn hs j ⟨hx.1.le, hx.2⟩)
  rw [heq, intervalIntegral.integral_const, smul_eq_mul]
  grind

theorem root_step_full_cell_error {g : ℝ → ℝ} (hg : Continuous g) {w : ℝ} (hw : 0 ≤ w)
    (hmod : ∀ x ∈ Icc (rootPartitionPoint n p hn j.castSucc)
      (rootPartitionPoint n p hn j.succ),
      |g x - g (rootPartitionPoint n p hn j.castSucc)| ≤ w) :
    |(∫ x in rootPartitionPoint n p hn j.castSucc..rootPartitionPoint n p hn j.succ,
        g x * rootStepDensity N n p hp hn hs x) -
      g (rootPartitionPoint n p hn j.castSucc) * rootGapMultiplicity N n hs j / (N : ℝ)| ≤
      w * rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hi := root_step_cell_integral_bound hp hn hs j hw (sub_pos.1 (rootPartition_gap_pos hp hn j)).le le_rfl le_rfl hmod
  simp only [sub_mul] at hi
  rwa [intervalIntegral.integral_sub (intervalIntegrable_mul_rootStepDensity p hp hn hs hg _ _) (intervalIntegrable_mul_rootStepDensity p hp hn hs continuous_const _ _), intervalIntegral.integral_const_mul, root_step_full_cell_mass, ← mul_div_assoc] at hi
end

section
variable {N k r : ℕ} {p : Fin (k + 1) → ℝ} (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ((k + 1) + r)) {g : ℝ → ℝ}
include hcount
theorem root_step_boundary_integral_bounds {G : ℝ} (hG : 0 ≤ G)
    (hbound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G) :
    |∫ x in (-Real.pi)..p 0, g x * rootStepDensity N (k + 1) p hp (by omega) hs x| ≤
        G * (2 * r + 1 : ℝ) / (N : ℝ) ∧
      |∫ x in p (Fin.last k)..Real.pi,
        g x * rootStepDensity N (k + 1) p hp (by omega) hs x| ≤
        G * (2 * r + 1 : ℝ) / (N : ℝ) := by
  have hzero : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := rfl
  have hlast : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc =
      p (Fin.last k) := rootPartitionPoint_root p _ (Fin.last k)
  have hend : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
      p 0 + 2 * Real.pi := rootPartitionPoint_end p _
  have hm j := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount j) hG) (Nat.cast_nonneg N)
  exact ⟨(root_step_cell_integral_bound hp (by omega) hs 0 hG (hp.1 0).1.le (by linarith [(hp.1 (Fin.last k)).2]) le_rfl
      fun x hx => hbound x ⟨hx.1, hx.2.trans (hp.1 0).2.le⟩).trans (hm _),
    (root_step_cell_integral_bound hp (by omega) hs (Fin.last (k + 1)) hG (hp.1 _).2.le (by linarith) (by linarith [(hp.1 0).1])
      fun x hx => hbound x ⟨(hp.1 (Fin.last k)).1.le.trans hx.1, hx.2⟩).trans (hm _)⟩

/-- Finite quadrature for the actual step density. No closeness to `ρ` is
assumed. The two boundary masses are retained in the error term. -/
theorem root_step_quadrature_error (hg : Continuous g)
    {G L d : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hbound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G)
    (hLip : ∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
      |g x - g y| ≤ L * |x - y|)
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d) :
    |(∫ x in (-Real.pi)..Real.pi,
        g x * rootStepDensity N (k + 1) p hp (by omega) hs x) -
      (∑ j, g (p j)) / (N : ℝ)| ≤
        L * d + (2 * G * (2 * r + 1 : ℝ) + G) / (N : ℝ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  obtain ⟨_, _, hinterior⟩ := root_mesh_consequences hp hmesh
  obtain ⟨hleft, hright⟩ := root_step_boundary_integral_bounds hp hs hcount hG hbound
  refine (quadrature_split (fun _ => L * d / N) (intervalIntegrable_mul_rootStepDensity p hp _ hs hg) (fun j => ?_) hleft hright).trans ?_
  · obtain ⟨ha, hb⟩ := rootPartitionPoint_cell p j
    have hm : rootGapMultiplicity N (k + 1) hs ⟨j + 1, by omega⟩ = 1 := by grind [rootGapMultiplicity]
    have hi := root_step_full_cell_error hp (by omega) hs _ hg (mul_nonneg hL hd) (by
      rw [ha, hb]
      intro x hx
      refine (hLip x ⟨(hp.1 j.castSucc).1.le.trans hx.1, hx.2.trans (hp.1 j.succ).2.le⟩ _ ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩).trans ?_
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      gcongr
      exact (sub_le_sub_right hx.2 _).trans (hinterior j))
    rwa [ha, hb, hm, mul_one, mul_one] at hi
  · have : |g (p (Fin.last k))| / N ≤ G / N := by gcongr; exact hbound _ ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
    have : (k : ℝ) * (L * d / N) ≤ L * d := by
      rw [mul_div_assoc', div_le_iff₀ hN, mul_comm]; gcongr; exact_mod_cast (by omega : k ≤ N)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_div, Nat.abs_cast]
    linarith [show 2 * (G * (2 * r + 1) / N) + G / N = (2 * G * (2 * r + 1) + G) / N by ring]
end

/-- The Bethe derivative kernel has quadrature error `O(1/N)` against the
step density, uniformly in the first coordinate and in `Δ ≤ Δ₀`. -/
theorem exists_uniform_step_kernel_quadrature {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀, ∀ x ∈ Icc (-Real.pi) Real.pi,
      ∀ (N k r : ℕ) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
        (hs : 2 * (k + 1) ≤ N), N = 2 * ((k + 1) + r) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ j : Fin (k + 2),
        rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      |(∫ y in (-Real.pi)..Real.pi,
          d1Theta Δ x y * rootStepDensity N (k + 1) p hp (by omega) hs y) -
        (∑ j, d1Theta Δ x (p j)) / (N : ℝ)| ≤
          (C * D + 2 * C * (2 * r + 1 : ℝ) + C) / (N : ℝ) := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_d1Theta_bounds hΔ₀
  refine ⟨C, hC, fun Δ hΔ x hx N k r p hp hs hcount D hD hmesh => ?_⟩
  exact (root_step_quadrature_error hp hs hcount (continuous_d1Theta_right (lt_of_le_of_lt hΔ hΔ₀) x)
    hC.le hC.le (div_nonneg hD (Nat.cast_nonneg _)) (by grind) (fun y hy z hz => by simpa using (hkernel Δ hΔ).2 x hx y hy x hx z hz) hmesh).trans_eq (by ring)

end PottsDiscontinuity.Bethe
