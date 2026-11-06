module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23FiniteQuadrature

/-! # Quadrature on the interior root cells

The boundary intervals are estimated separately. This avoids the incorrect
boundary correction in the printed proof of Theorem 2.6 and does not require
periodic boundary values of a continuous test function.
-/

public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section
variable (k : ℕ)
theorem sum_fin_integrals_adjacent (p : Fin (k + 1) → ℝ)
    {F : ℝ → ℝ} (hF : ∀ a b, IntervalIntegrable F volume a b) :
    (∑ j : Fin k, ∫ x in p j.castSucc..p j.succ, F x) =
      ∫ x in p 0..p (Fin.last k), F x := by
  simpa [integral_interval_sub_left (hF _ _) (hF _ _)] using fin_sum_consecutive_sub fun j => ∫ x in p 0..p j, F x
end

theorem rootPartitionPoint_cell {k : ℕ} (p : Fin (k + 1) → ℝ) (j : Fin k) :
    rootPartitionPoint (k + 1) p (by omega) (⟨j + 1, by omega⟩ : Fin (k + 2)).castSucc = p j.castSucc ∧
    rootPartitionPoint (k + 1) p (by omega) (⟨j + 1, by omega⟩ : Fin (k + 2)).succ = p j.succ :=
  ⟨rootPartitionPoint_root p _ j.castSucc, rootPartitionPoint_root p _ j.succ⟩

section
variable {N k : ℕ} {p : Fin (k + 1) → ℝ} (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
theorem rootStepDensity_interior (j : Fin k)
    {x : ℝ} (hx : p j.castSucc ≤ x ∧ x < p j.succ) :
    rootStepDensity N (k + 1) p hp (by omega) hs x =
      1 / ((N : ℝ) * (p j.succ - p j.castSucc)) := by
  obtain ⟨ha, hb⟩ := rootPartitionPoint_cell p j
  rw [rootStepDensity_on_cell hp (by omega) hs _ (by rwa [ha, hb]), ha, hb]
  grind [rootGapMultiplicity]

/-- A local quadrature estimate. `w` is any modulus bound for the test
function on this cell; `E` is the actual uniform error of its density. -/
theorem root_cell_quadrature_error {Δ : ℝ} (hΔ : Δ < -1) {g : ℝ → ℝ} (hg : Continuous g)
    {G M E w : ℝ} (hG : 0 ≤ G)
    (hw : 0 ≤ w) (hgBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G)
    (hρBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |rho Δ x| ≤ M)
    (herror : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x| ≤ E)
    (j : Fin k)
    (hmod : ∀ x ∈ Icc (p j.castSucc) (p j.succ), |g x - g (p j.castSucc)| ≤ w) :
    |(∫ x in p j.castSucc..p j.succ, g x * rho Δ x) - g (p j.castSucc) / (N : ℝ)| ≤
      (w * M + G * E) * (p j.succ - p j.castSucc) := by
  have hgap := sub_pos.mpr
    (hp.2.1 (show j.castSucc < j.succ from by simp))
  let c := 1 / ((N : ℝ) * (p j.succ - p j.castSucc))
  have hF : Continuous (fun x => g x * rho Δ x) := hg.mul (continuous_rho hΔ)
  have hrewrite : (∫ x in p j.castSucc..p j.succ,
      (g x * rho Δ x - g (p j.castSucc) * c)) =
      (∫ x in p j.castSucc..p j.succ, g x * rho Δ x) - g (p j.castSucc) / (N : ℝ) := by
    rw [integral_sub (hF.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const]
    simp
    grind
  rw [← hrewrite, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := p j.castSucc) (b := p j.succ) (C := w * M + G * E)
    (f := fun x => g x * rho Δ x - g (p j.castSucc) * c) ?_
  · grind
  · filter_upwards [volume.ae_ne (p j.succ)] with x hne hx
    have hxi : x ∈ Icc (p j.castSucc) (p j.succ) := by grind
    have hxpi : x ∈ Icc (-Real.pi) Real.pi :=
      ⟨(hp.1 j.castSucc).1.le.trans hxi.1, hxi.2.trans (hp.1 j.succ).2.le⟩
    have he := herror x hxpi
    rw [(rootStepDensity_interior hp hs j ⟨hxi.1, lt_of_le_of_ne hxi.2 hne⟩), abs_sub_comm] at he
    rw [Real.norm_eq_abs, show g x * rho Δ x - g (p j.castSucc) * c = (g x - g (p j.castSucc)) * rho Δ x + g (p j.castSucc) * (rho Δ x - c) by ring]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    gcongr
    exacts [hmod x hxi, hρBound x hxpi, hgBound _ ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩]
end

theorem root_mesh_consequences {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) {d : ℝ}
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d) :
    p 0 + Real.pi ≤ d ∧ Real.pi - p (Fin.last k) ≤ d ∧
      ∀ j : Fin k, p j.succ - p j.castSucc ≤ d := by
  have h0 : p 0 - (p (Fin.last k) - 2 * Real.pi) ≤ d := hmesh 0
  refine ⟨by linarith [(hp.1 (Fin.last k)).2], by linarith [(hp.1 0).1], fun j => ?_⟩
  have := hmesh ⟨j + 1, by omega⟩
  rwa [(rootPartitionPoint_cell p j).1, (rootPartitionPoint_cell p j).2] at this

theorem quadrature_split {k : ℕ} {p : Fin (k + 1) → ℝ} {F g : ℝ → ℝ} {N A : ℝ} (e : Fin k → ℝ)
    (hF : ∀ a b, IntervalIntegrable F volume a b)
    (hcell : ∀ j : Fin k, |(∫ x in p j.castSucc..p j.succ, F x) - g (p j.castSucc) / N| ≤ e j)
    (h1 : |∫ x in (-Real.pi)..p 0, F x| ≤ A) (h3 : |∫ x in p (Fin.last k)..Real.pi, F x| ≤ A) :
    |(∫ x in (-Real.pi)..Real.pi, F x) - (∑ j, g (p j)) / N| ≤
      ∑ j, e j + 2 * A + |g (p (Fin.last k)) / N| := by
  have h2 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hcell j)
  rw [Finset.sum_sub_distrib, sum_fin_integrals_adjacent k p hF, ← Finset.sum_div] at h2
  rw [← integral_add_adjacent_intervals (hF _ (p 0)) (hF _ _), ← integral_add_adjacent_intervals (hF (p 0) (p (Fin.last k))) (hF _ _), Fin.sum_univ_castSucc, add_div]
  have := le_abs_self (g (p (Fin.last k)) / N)
  have := neg_abs_le (g (p (Fin.last k)) / N)
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith

/-- Finite quadrature with both endpoint tails explicitly controlled. -/
theorem root_quadrature_error {N k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    {Δ : ℝ} (hΔ : Δ < -1) {g : ℝ → ℝ} (hg : Continuous g)
    {G M E w d : ℝ} (hG : 0 ≤ G) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hw : 0 ≤ w)
    (hgBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G)
    (hρBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |rho Δ x| ≤ M)
    (herror : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x| ≤ E)
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d)
    (hmod : ∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
      |x - y| ≤ d → |g x - g y| ≤ w) :
    |(∫ x in (-Real.pi)..Real.pi, g x * rho Δ x) - (∑ j, g (p j)) / (N : ℝ)| ≤
      2 * Real.pi * (w * M + G * E) + 2 * G * M * d + G / (N : ℝ) := by
  have hF := hg.mul (continuous_rho hΔ)
  obtain ⟨hleft, hright, hinterior⟩ := root_mesh_consequences hp hmesh
  have hb {a b : ℝ} (hab : a ≤ b) (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) (hd : b - a ≤ d) :
      |∫ x in a..b, g x * rho Δ x| ≤ G * M * d := by
    have := norm_integral_le_of_norm_le_const (C := G * M) (f := fun x => g x * rho Δ x) (a := a) (b := b) fun x hx => ?_
    · rw [abs_of_nonneg (sub_nonneg.2 hab)] at this
      exact this.trans (by gcongr)
    · rw [uIoc_of_le hab] at hx
      exact (norm_mul _ _).trans_le (mul_le_mul (hgBound x ⟨by linarith [hx.1], by linarith [hx.2]⟩) (hρBound x ⟨by linarith [hx.1], by linarith [hx.2]⟩) (norm_nonneg _) hG)
  refine (quadrature_split _ (fun _ _ => hF.intervalIntegrable _ _) (fun j => root_cell_quadrature_error hp hs hΔ hg hG hw hgBound hρBound herror j fun x hx => ?_) (hb (hp.1 0).1.le le_rfl (hp.1 0).2.le (by linarith)) (hb (hp.1 _).2.le (hp.1 _).1.le le_rfl hright)).trans ?_
  · apply hmod x ⟨(hp.1 j.castSucc).1.le.trans hx.1, hx.2.trans (hp.1 j.succ).2.le⟩ (p j.castSucc) ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact (sub_le_sub_right hx.2 _).trans (hinterior j)
  · have h1 : |g (p (Fin.last k))| / N ≤ G / N := by gcongr; exact hgBound _ ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
    have : (w * M + G * E) * (p (Fin.last k) - p 0) ≤ (w * M + G * E) * (2 * Real.pi) := by
      gcongr; linarith [(hp.1 0).1, (hp.1 (Fin.last k)).2]
    rw [← Finset.mul_sum, fin_sum_consecutive_sub, abs_div, Nat.abs_cast]
    linarith

end PottsDiscontinuity.Bethe
