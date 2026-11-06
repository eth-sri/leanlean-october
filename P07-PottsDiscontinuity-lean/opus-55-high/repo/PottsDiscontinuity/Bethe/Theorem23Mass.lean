module

public import PottsDiscontinuity.Bethe.Theorem23Quadrature

/-! # Exact physical masses of the discrete and continuous densities -/

public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem root_step_subcell_mass {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
    {a b : ℝ} (hab : a ≤ b) (ha : rootPartitionPoint n p hn j.castSucc ≤ a)
    (hb : b ≤ rootPartitionPoint n p hn j.succ) :
    (∫ x in a..b, rootStepDensity N n p hp hn hs x) =
      (b - a) * rootGapMultiplicity N n hs j /
        ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)) := by
  have heq := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hab
   
    (g := fun _ : ℝ => rootGapMultiplicity N n hs j /
      ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)))
    (fun x hx => rootStepDensity_on_cell hp hn hs j ⟨ha.trans hx.1.le, hx.2.trans_le hb⟩)
  simp_all

theorem root_step_physical_mass {N k r : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    (hcount : N = 2 * ((k + 1) + r)) :
    (∫ x in (-Real.pi)..Real.pi, rootStepDensity N (k + 1) p hp (by omega) hs x) =
      1 / 2 + (r : ℝ) / N := by
  have hNnat : 0 < N := by omega
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  have hi : ∀ a b, IntervalIntegrable s volume a b := fun a b => by
    simpa [s] using intervalIntegrable_mul_rootStepDensity p hp (by omega) hs
      (g := fun _ => (1 : ℝ)) continuous_const a b
  have hsym : p (Fin.last k) = -p 0 := by simpa using hp.2.2 0
  have hfirstpos : 0 < p 0 + Real.pi := by linarith [(hp.1 0).1]
  have hzero : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := rfl
  have hfirst : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := rfl
  have hlast : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc =
      p (Fin.last k) := rootPartitionPoint_root p _ (Fin.last k)
  have hend : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
      p 0 + 2 * Real.pi := rootPartitionPoint_end p _
  have hnat : N + 1 - 2 * (k + 1) = 2 * r + 1 := by omega
  have hmult (j : Fin (k + 2)) (hj : j.val = 0 ∨ j.val = k + 1) :
      rootGapMultiplicity N (k + 1) hs j = (2 * r + 1 : ℝ) := by
    simp_all [rootGapMultiplicity]
  have hleft : (∫ x in (-Real.pi)..p 0, s x) = (2 * r + 1 : ℝ) / (2 * (N : ℝ)) := by
    have h := root_step_subcell_mass hp (by omega) hs (0 : Fin (k + 2))
      (hp.1 0).1.le (by linarith) (by rfl)
    rw [hzero, hfirst, hmult _ (by simp), hsym] at h
    rw [h, show p 0 - (-p 0 - 2 * Real.pi) = 2 * (p 0 + Real.pi) by ring]
    field_simp
    ring
  have hright : (∫ x in p (Fin.last k)..Real.pi, s x) =
      (2 * r + 1 : ℝ) / (2 * (N : ℝ)) := by
    have h := root_step_subcell_mass hp (by omega) hs (Fin.last (k + 1))
      (hp.1 (Fin.last k)).2.le (by linarith)
      (by linarith)
    rw [hlast, hend, hmult _ (by simp), hsym] at h
    rw [hsym, h, show p 0 + 2 * Real.pi - -p 0 = 2 * (p 0 + Real.pi) by ring]
    field_simp
    ring
  have hcell (j : Fin k) : (∫ x in p j.castSucc..p j.succ, s x) = 1 / (N : ℝ) := by
    obtain ⟨ha, hb⟩ := rootPartitionPoint_cell p j
    have hm : rootGapMultiplicity N (k + 1) hs ⟨j + 1, by omega⟩ = 1 := by grind [rootGapMultiplicity]
    simpa only [ha, hb, hm] using root_step_full_cell_mass hp (by omega) hs ⟨j + 1, by omega⟩
  rw [← integral_add_adjacent_intervals (hi _ (p 0)) (hi _ _), ← integral_add_adjacent_intervals (hi (p 0) (p (Fin.last k))) (hi _ _), ← sum_fin_integrals_adjacent k p hi, hleft, hright]
  simp only [hcell, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcountc : (N : ℝ) = 2 * ((k : ℝ) + 1 + (r : ℝ)) := by exact_mod_cast hcount
  field_simp
  nlinarith

theorem integral_Rsech {lam : ℝ} (hlam : 0 < lam) :
    (∫ α in (-Real.pi)..Real.pi, Rsech lam α) = Real.pi := by
  have h := cosCoeff_trigSeries_zero (summable_secCoeff hlam) summable_zero (1 / 2)
  rw [← (funext (Rsech_eq_trigSeries hlam)), cosCoeff_zero] at h
  linarith

theorem integral_rho_mass {Δ : ℝ} (hΔ : Δ < -1) :
    (∫ x in (-Real.pi)..Real.pi, rho Δ x) = 1 / 2 := by
  have hlam := lamOf_pos hΔ
  rw [integral_Icc_comp_kMap hlam]
  have heq : (fun α => Xi (lamOf Δ) α * rho Δ (kMap (lamOf Δ) α)) =
      fun α => (2 * Real.pi)⁻¹ * Rsech (lamOf Δ) α := by
    funext α
    have h := Rtrans_rho hΔ α
    rw [Rtrans_eq hΔ] at h
    field_simp
    linarith
  rw [heq, intervalIntegral.integral_const_mul, integral_Rsech hlam]
  field_simp

end PottsDiscontinuity.Bethe
