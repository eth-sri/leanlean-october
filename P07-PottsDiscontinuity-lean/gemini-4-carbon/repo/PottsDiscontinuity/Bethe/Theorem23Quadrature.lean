module

public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Quantitative quadrature against the root step density -/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem intervalIntegrable_mul_rootStepDensity {N n : ℕ} (p : Fin n → ℝ)
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * rootStepDensity N n p hp hn hs x) volume a b := by
  classical
  let c (j : Fin (n + 1)) := rootGapMultiplicity N n hs j /
    ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
  rw [show (fun x => g x * rootStepDensity N n p hp hn hs x) =
      ∑ j : Fin (n + 1), (Ico (rootPartitionPoint n p hn j.castSucc) (rootPartitionPoint n p hn j.succ)).indicator
        (fun x => g x * c j) from funext fun x => by
    simp [rootStepDensity, Finset.mul_sum, c, Set.indicator, Set.mem_Ico, mul_ite]]
  exact IntervalIntegrable.sum _ fun j _ =>
    intervalIntegrable_iff.mpr (((hg.mul continuous_const).intervalIntegrable a b).def'.indicator measurableSet_Ico)

private theorem root_step_cell_integral_bound {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    (j : Fin (n + 1)) {a b G : ℝ} (hG : 0 ≤ G)
    (hab : a ≤ b) (ha : rootPartitionPoint n p hn j.castSucc ≤ a)
    (hb : b ≤ rootPartitionPoint n p hn j.succ)
    {g : ℝ → ℝ} (hbound : ∀ x ∈ Icc a b, |g x| ≤ G) :
    |∫ x in a..b, g x * rootStepDensity N n p hp hn hs x| ≤
      G * rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hgap := rootPartition_gap_pos hp hn j
  let d := rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc
  let c := rootGapMultiplicity N n hs j / ((N : ℝ) * d)
  have hm : 0 ≤ rootGapMultiplicity N n hs j := by unfold rootGapMultiplicity; split <;> positivity
  have hc : 0 ≤ c := div_nonneg hm (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := fun x => g x * rootStepDensity N n p hp hn hs x) (a := a) (b := b) (C := G * c) <| by
    filter_upwards [volume.ae_ne b] with x hne hx
    rw [uIoc_of_le hab] at hx
    rw [rootStepDensity_on_cell hp hn hs j ⟨ha.trans hx.1.le, (lt_of_le_of_ne hx.2 hne).trans_le hb⟩,
      Real.norm_eq_abs, abs_mul, show |rootGapMultiplicity N n hs j / ((N : ℝ) * d)| = c from abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (hbound x ⟨hx.1.le, hx.2⟩) hc
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left (by dsimp [d]; linarith : b - a ≤ d) (mul_nonneg hG hc)).trans_eq
    (by dsimp [c, d]; field_simp [hN.ne', hgap.ne']))

theorem root_step_full_cell_mass {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    (∫ x in rootPartitionPoint n p hn j.castSucc..rootPartitionPoint n p hn j.succ,
      rootStepDensity N n p hp hn hs x) = rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hgap := rootPartition_gap_pos hp hn j
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (sub_pos.mp hgap).le
    (fun x hx => rootStepDensity_on_cell hp hn hs j ⟨hx.1.le, hx.2⟩),
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp [hN.ne', hgap.ne']

theorem sum_fin_step_integrals_adjacent (k : ℕ) (p : Fin (k + 1) → ℝ)
    {F : ℝ → ℝ} (hF : ∀ a b, IntervalIntegrable F volume a b) :
    (∑ j : Fin k, ∫ x in p j.castSucc..p j.succ, F x) =
      ∫ x in p 0..p (Fin.last k), F x := by
  let P (y : ℝ) := ∫ x in p 0..y, F x
  simp_rw [show ∀ j : Fin k, (∫ x in p j.castSucc..p j.succ, F x) = P (p j.succ) - P (p j.castSucc) from
    fun _ => (intervalIntegral.integral_interval_sub_left (hF _ _) (hF _ _)).symm]
  rw [sum_fin_adjacent_sub k (fun j => P (p j))]
  simp only [P, integral_same, sub_zero]

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
  let g := d1Theta Δ x
  have hg : Continuous g := continuous_d1Theta_right (lt_of_le_of_lt hΔ hΔ₀) x
  have hbound : ∀ y ∈ Icc (-Real.pi) Real.pi, |g y| ≤ C := fun y hy => ((hkernel Δ hΔ).1 x hx y hy).1
  have hLip : ∀ y ∈ Icc (-Real.pi) Real.pi, ∀ z ∈ Icc (-Real.pi) Real.pi, |g y - g z| ≤ C * |y - z| :=
    fun y hy z hz => by simpa [g] using (hkernel Δ hΔ).2 x hx y hy x hx z hz
  let d := D / (N : ℝ)
  have hd : 0 ≤ d := div_nonneg hD (Nat.cast_nonneg _)
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkc : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let F := fun y => g y * s y
  have hF : ∀ a b, IntervalIntegrable F volume a b := intervalIntegrable_mul_rootStepDensity p hp (by omega) hs hg
  obtain ⟨_, _, hinterior⟩ := root_mesh_consequences hp hmesh
  have hcell (j : Fin k) : |(∫ y in p j.castSucc..p j.succ, F y) - g (p j.castSucc) / (N : ℝ)| ≤ C * d / (N : ℝ) := by
    let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
    have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
      convert rootPartitionPoint_root p (by omega) j.castSucc using 1; congr 1
    have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
      convert rootPartitionPoint_root p (by omega) j.succ using 1; congr 1
    have hm : rootGapMultiplicity N (k + 1) hs cell = 1 := by
      simp only [rootGapMultiplicity, cell, ite_eq_right (by omega : ¬ (j.val + 1 = 0 ∨ j.val + 1 = k + 1))]
    have hi := root_step_cell_integral_bound hp (by omega) hs cell (mul_nonneg hC.le hd) (sub_pos.mp (rootPartition_gap_pos hp (by omega) cell)).le
      le_rfl le_rfl (g := fun y => g y - g (p j.castSucc)) fun y hy => by
        rw [ha, hb] at hy
        refine (hLip y ⟨(hp.1 j.castSucc).1.le.trans hy.1, hy.2.trans (hp.1 j.succ).2.le⟩ _
          ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
        rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]; exact (sub_le_sub_right hy.2 _).trans (hinterior j)
    rw [ha, hb, hm, mul_one, show (fun y => (g y - g (p j.castSucc)) * s y) = fun y => F y - g (p j.castSucc) * s y from
      funext fun _ => by dsimp [F]; ring,
      intervalIntegral.integral_sub (hF _ _) (intervalIntegrable_mul_rootStepDensity p hp (by omega) hs continuous_const _ _),
      intervalIntegral.integral_const_mul] at hi
    have hmass := root_step_full_cell_mass hp (by omega) hs cell
    rw [ha, hb, hm] at hmass
    simpa only [s, hmass, mul_one_div] using hi
  have hmid : |(∫ y in p 0..p (Fin.last k), F y) - (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)| ≤ C * d := by
    rw [← sum_fin_step_integrals_adjacent k p hF, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hcell j).trans <| by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc, div_le_iff₀ hN]
      nlinarith [mul_le_mul_of_nonneg_right hkc (mul_nonneg hC.le hd)])
  have hleft : |∫ y in (-Real.pi)..p 0, F y| ≤ C * (2 * r + 1 : ℝ) / (N : ℝ) := by
    have h0 : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc = p (Fin.last k) - 2 * Real.pi := by
      convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1
    have h1 : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := by
      convert rootPartitionPoint_root p (by omega) (0 : Fin (k + 1)) using 1; congr 1
    exact (root_step_cell_integral_bound hp (by omega) hs (0 : Fin (k + 2)) hC.le (hp.1 0).1.le
      (by rw [h0]; linarith [(hp.1 (Fin.last k)).2]) (by rw [h1])
      (fun y hy => hbound y ⟨hy.1, hy.2.trans (hp.1 0).2.le⟩)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount _) hC.le) hN.le)
  have hright : |∫ y in p (Fin.last k)..Real.pi, F y| ≤ C * (2 * r + 1 : ℝ) / (N : ℝ) := by
    have h0 : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc = p (Fin.last k) := by
      convert rootPartitionPoint_root p (by omega) (Fin.last k) using 1; congr 1
    have h1 : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ = p 0 + 2 * Real.pi := by
      convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
    exact (root_step_cell_integral_bound hp (by omega) hs (Fin.last (k + 1)) hC.le (hp.1 (Fin.last k)).2.le
      (by rw [h0]) (by rw [h1]; linarith [(hp.1 0).1])
      (fun y hy => hbound y ⟨(hp.1 (Fin.last k)).1.le.trans hy.1, hy.2⟩)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount _) hC.le) hN.le)
  have hlast : |g (p (Fin.last k)) / (N : ℝ)| ≤ C / (N : ℝ) := by
    rw [abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right (hbound _ ⟨(hp.1 (Fin.last k)).1.le, (hp.1 (Fin.last k)).2.le⟩) hN.le
  change |(∫ y in (-Real.pi)..Real.pi, F y) - (∑ j, g (p j)) / (N : ℝ)| ≤ _
  rw [← integral_add_adjacent_intervals (hF (-Real.pi) (p 0)) (hF (p 0) Real.pi),
    ← integral_add_adjacent_intervals (hF (p 0) (p (Fin.last k))) (hF (p (Fin.last k)) Real.pi),
    Fin.sum_univ_castSucc, add_div]
  have htri (a b c u v : ℝ) : |a + (b + c) - (u + v)| ≤ |a| + |b - u| + |c| + |v| := by
    rw [show a + (b + c) - (u + v) = a + (b - u) + c - v by ring]
    linarith [abs_sub (a + (b - u) + c) v, abs_add_le (a + (b - u)) c, abs_add_le a (b - u)]
  calc _ ≤ |∫ y in (-Real.pi)..p 0, F y| + |(∫ y in p 0..p (Fin.last k), F y) - (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)| +
        |∫ y in p (Fin.last k)..Real.pi, F y| + |g (p (Fin.last k)) / (N : ℝ)| := htri _ _ _ _ _
    _ ≤ C * (2 * r + 1 : ℝ) / (N : ℝ) + C * d + C * (2 * r + 1 : ℝ) / (N : ℝ) + C / (N : ℝ) := by gcongr
    _ = (C * D + 2 * C * (2 * r + 1 : ℝ) + C) / (N : ℝ) := by dsimp [d]; ring

end PottsDiscontinuity.Bethe
