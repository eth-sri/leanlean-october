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
  let c : Fin (n + 1) → ℝ := fun j => rootGapMultiplicity N n hs j /
    ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
  rw [show (fun x => g x * rootStepDensity N n p hp hn hs x) =
      ∑ j : Fin (n + 1),
        (Ico (rootPartitionPoint n p hn j.castSucc) (rootPartitionPoint n p hn j.succ)).indicator
          (fun x => g x * c j) by
    funext x; simp [rootStepDensity, Finset.mul_sum, c, Set.indicator, Set.mem_Ico, mul_ite]]
  exact IntervalIntegrable.sum _ fun j _ => intervalIntegrable_iff.mpr <|
    ((hg.mul continuous_const).intervalIntegrable a b).def'.indicator measurableSet_Ico

theorem rootGapMultiplicity_nonneg {N n : ℕ} (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    0 ≤ rootGapMultiplicity N n hs j := by
  unfold rootGapMultiplicity; split <;> positivity

/-- The integral over any subinterval of one cell is bounded by its full cell
mass times a bound for the test function. -/
theorem root_step_cell_integral_bound {N n : ℕ} {p : Fin n → ℝ}
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
  have hc : 0 ≤ c := div_nonneg (rootGapMultiplicity_nonneg hs j) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b)
    (f := fun x => g x * rootStepDensity N n p hp hn hs x) (C := G * c) <| by
      filter_upwards [volume.ae_ne b] with x hne hx
      rw [uIoc_of_le hab] at hx
      rw [rootStepDensity_on_cell hp hn hs j ⟨ha.trans hx.1.le, (lt_of_le_of_ne hx.2 hne).trans_le hb⟩,
        Real.norm_eq_abs, abs_mul]
      change |g x| * |c| ≤ G * c
      rw [abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right (hbound x ⟨hx.1.le, hx.2⟩) hc
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  refine (hi.trans (mul_le_mul_of_nonneg_left (by dsimp [d]; linarith : b - a ≤ d)
    (mul_nonneg hG hc))).trans_eq ?_
  dsimp [c, d]; field_simp [hN.ne', hgap.ne']

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

theorem root_step_full_cell_error {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
    {g : ℝ → ℝ} (hg : Continuous g) {w : ℝ} (hw : 0 ≤ w)
    (hmod : ∀ x ∈ Icc (rootPartitionPoint n p hn j.castSucc)
      (rootPartitionPoint n p hn j.succ),
      |g x - g (rootPartitionPoint n p hn j.castSucc)| ≤ w) :
    |(∫ x in rootPartitionPoint n p hn j.castSucc..rootPartitionPoint n p hn j.succ,
        g x * rootStepDensity N n p hp hn hs x) -
      g (rootPartitionPoint n p hn j.castSucc) * rootGapMultiplicity N n hs j / (N : ℝ)| ≤
      w * rootGapMultiplicity N n hs j / (N : ℝ) := by
  let a := rootPartitionPoint n p hn j.castSucc
  let b := rootPartitionPoint n p hn j.succ
  let s := rootStepDensity N n p hp hn hs
  have hi := root_step_cell_integral_bound hp hn hs j hw (sub_pos.mp (rootPartition_gap_pos hp hn j)).le
    le_rfl le_rfl (g := fun x => g x - g a) hmod
  rwa [show (fun x => (g x - g a) * s x) = fun x => g x * s x - g a * s x by funext; ring,
    intervalIntegral.integral_sub (intervalIntegrable_mul_rootStepDensity p hp hn hs hg a b)
      (intervalIntegrable_mul_rootStepDensity p hp hn hs continuous_const a b),
    intervalIntegral.integral_const_mul,
    show ∫ x in a..b, s x = rootGapMultiplicity N n hs j / (N : ℝ) from
      root_step_full_cell_mass hp hn hs j, ← mul_div_assoc] at hi

theorem sum_fin_step_integrals_adjacent (k : ℕ) (p : Fin (k + 1) → ℝ)
    {F : ℝ → ℝ} (hF : ∀ a b, IntervalIntegrable F volume a b) :
    (∑ j : Fin k, ∫ x in p j.castSucc..p j.succ, F x) =
      ∫ x in p 0..p (Fin.last k), F x := by
  simp_rw [fun j : Fin k => (intervalIntegral.integral_interval_sub_left (a := p 0)
    (b := p j.succ) (c := p j.castSucc) (hF _ _) (hF _ _)).symm]
  rw [sum_fin_adjacent_sub k (fun j => ∫ x in p 0..p j, F x), integral_same, sub_zero]

theorem root_step_boundary_integral_bounds {N k r : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    (hcount : N = 2 * ((k + 1) + r)) {g : ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hbound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G) :
    |∫ x in (-Real.pi)..p 0, g x * rootStepDensity N (k + 1) p hp (by omega) hs x| ≤
        G * (2 * r + 1 : ℝ) / (N : ℝ) ∧
      |∫ x in p (Fin.last k)..Real.pi,
        g x * rootStepDensity N (k + 1) p hp (by omega) hs x| ≤
        G * (2 * r + 1 : ℝ) / (N : ℝ) := by
  have hzero : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := by
    convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1
  have hfirst : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := by
    convert rootPartitionPoint_root p (by omega) (0 : Fin (k + 1)) using 1; congr 1
  have hlast : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc =
      p (Fin.last k) := by
    convert rootPartitionPoint_root p (by omega) (Fin.last k) using 1; congr 1
  have hend : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
      p 0 + 2 * Real.pi := by
    convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
  exact ⟨(root_step_cell_integral_bound hp (by omega) hs 0 hG (hp.1 0).1.le
      (by rw [hzero]; linarith [(hp.1 (Fin.last k)).2]) (by rw [hfirst])
      (fun x hx => hbound x ⟨hx.1, hx.2.trans (hp.1 0).2.le⟩)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount _) hG) (by positivity)),
    (root_step_cell_integral_bound hp (by omega) hs (Fin.last (k + 1)) hG (hp.1 (Fin.last k)).2.le
      (by rw [hlast]) (by rw [hend]; linarith [(hp.1 0).1])
      (fun x hx => hbound x ⟨(hp.1 (Fin.last k)).1.le.trans hx.1, hx.2⟩)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount _) hG) (by positivity))⟩

/-- Finite quadrature for the actual step density. No closeness to `ρ` is
assumed. The two boundary masses are retained in the error term. -/
theorem root_step_quadrature_error {N k r : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    (hcount : N = 2 * ((k + 1) + r)) {g : ℝ → ℝ} (hg : Continuous g)
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
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkc : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let F := fun x => g x * s x
  have hF : ∀ a b, IntervalIntegrable F volume a b :=
    intervalIntegrable_mul_rootStepDensity p hp (by omega) hs hg
  obtain ⟨_, _, hinterior⟩ := root_mesh_consequences hp hmesh
  have hcell (j : Fin k) :
      |(∫ x in p j.castSucc..p j.succ, F x) - g (p j.castSucc) / (N : ℝ)| ≤
        L * d / (N : ℝ) := by
    let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
    have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
      convert rootPartitionPoint_root p (by omega) j.castSucc using 1; congr 1
    have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
      convert rootPartitionPoint_root p (by omega) j.succ using 1; congr 1
    have hm : rootGapMultiplicity N (k + 1) hs cell = 1 := by
      simp only [rootGapMultiplicity, cell,
        ite_eq_right (by omega : ¬ (j.val + 1 = 0 ∨ j.val + 1 = k + 1))]
    have hi := root_step_full_cell_error hp (by omega) hs cell hg (mul_nonneg hL hd) <| by
      rw [ha, hb]; intro x hx
      refine (hLip x ⟨(hp.1 j.castSucc).1.le.trans hx.1, hx.2.trans (hp.1 j.succ).2.le⟩
        _ ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      exact (sub_le_sub_right hx.2 _).trans (hinterior j)
    rwa [ha, hb, hm, mul_one, mul_one] at hi
  have hmiddle : |(∫ x in p 0..p (Fin.last k), F x) -
      (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)| ≤ L * d := by
    rw [← sum_fin_step_integrals_adjacent k p hF, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans <|
      (Finset.sum_le_sum fun j _ => hcell j).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc, div_le_iff₀ hN]
    nlinarith [mul_le_mul_of_nonneg_right hkc (mul_nonneg hL hd)]
  obtain ⟨hleft, hright⟩ := root_step_boundary_integral_bounds hp hs hcount hG hbound
  have hlast : |g (p (Fin.last k)) / (N : ℝ)| ≤ G / (N : ℝ) := by
    rw [abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right
      (hbound _ ⟨(hp.1 (Fin.last k)).1.le, (hp.1 (Fin.last k)).2.le⟩) hN.le
  change |(∫ x in (-Real.pi)..Real.pi, F x) - _| ≤ _
  rw [← integral_add_adjacent_intervals (b := p (Fin.last k)) (hF _ _) (hF _ _),
    ← integral_add_adjacent_intervals (b := p 0) (hF _ _) (hF _ _),
    Fin.sum_univ_castSucc, add_div]
  have h1 := abs_sub ((∫ x in (-Real.pi)..p 0, F x) +
    ((∫ x in p 0..p (Fin.last k), F x) - (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)) +
    (∫ x in p (Fin.last k)..Real.pi, F x)) (g (p (Fin.last k)) / (N : ℝ))
  have h2 := abs_add_le ((∫ x in (-Real.pi)..p 0, F x) +
    ((∫ x in p 0..p (Fin.last k), F x) - (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)))
    (∫ x in p (Fin.last k)..Real.pi, F x)
  have h3 := abs_add_le (∫ x in (-Real.pi)..p 0, F x)
    ((∫ x in p 0..p (Fin.last k), F x) - (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ))
  rw [show (∫ x in (-Real.pi)..p 0, F x) + (∫ x in p 0..p (Fin.last k), F x) +
      (∫ x in p (Fin.last k)..Real.pi, F x) -
      ((∑ j : Fin k, g (p j.castSucc)) / (N : ℝ) + g (p (Fin.last k)) / (N : ℝ)) =
    (∫ x in (-Real.pi)..p 0, F x) +
      ((∫ x in p 0..p (Fin.last k), F x) - (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)) +
      (∫ x in p (Fin.last k)..Real.pi, F x) - g (p (Fin.last k)) / (N : ℝ) by ring]
  dsimp only [F, s] at h1 h2 h3 ⊢
  rw [show L * d + (2 * G * (2 * r + 1 : ℝ) + G) / (N : ℝ) =
      G * (2 * r + 1 : ℝ) / (N : ℝ) + L * d + G * (2 * r + 1 : ℝ) / (N : ℝ) + G / (N : ℝ) by ring]
  linarith

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
  refine (root_step_quadrature_error hp hs hcount (continuous_d1Theta_right (lt_of_le_of_lt hΔ hΔ₀) x)
    hC.le hC.le (div_nonneg hD (Nat.cast_nonneg _))
    (fun y hy => ((hkernel Δ hΔ).1 x hx y hy).1)
    (fun y hy z hz => by simpa using (hkernel Δ hΔ).2 x hx y hy x hx z hz)
    hmesh).trans_eq (by ring)

end PottsDiscontinuity.Bethe
