module

public import PottsDiscontinuity.Bethe.AsymptoticOffsetControl
public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Interior-cell quadrature for varying root tests

Unlike Theorem 2.6's continuous fixed tests, the values attached to the
roots here may vary arbitrarily. The integral identity is exact; the last
root is omitted and will be estimated separately in applications.
-/

public section

open Set MeasureTheory Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The piecewise constant interior quadrature test, zero off the interior
root cells. Its integral is the sum of the first `k` values divided by `N`. -/
noncomputable def ratioInteriorTest {k : ℕ} (N : ℕ) (p : Fin (k + 1) → ℝ)
    (_hp : p ∈ S_n (k + 1)) (v : Fin (k + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin k, (Ico (p j.castSucc) (p j.succ)).indicator
    (fun _ => v j.castSucc / ((N : ℝ) * (p j.succ - p j.castSucc))) x

section
variable {k N : ℕ}
theorem ratio_interiorTest_integrable {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (v : Fin (k + 1) → ℝ) :
    Integrable (ratioInteriorTest N p hp v) := by
  apply integrable_finsetSum
  intro j hj
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  simp

theorem ratio_integral_interiorTest (hN : 0 < N)
    {p : Fin (k + 1) → ℝ} (hp : p ∈ S_n (k + 1)) (v : Fin (k + 1) → ℝ) :
    (∫ x, ratioInteriorTest N p hp v x) = (∑ j : Fin k, v j.castSucc) / N := by
  unfold ratioInteriorTest
  rw [integral_finsetSum]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul,
      max_eq_left (sub_pos.mpr (hp.2.1 (show j.castSucc < j.succ by simp))).le]
    have hgap := (sub_pos.mpr (hp.2.1 (show j.castSucc < j.succ by simp))).ne'
    grind
  · intro j hj
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    simp
end

section
variable {k N : ℕ} {p : Fin (k + 1) → ℝ} (hp : p ∈ S_n (k + 1))
theorem ratio_interiorTest_on_cell (v : Fin (k + 1) → ℝ)
    (j : Fin k) {x : ℝ} (hx : p j.castSucc ≤ x ∧ x < p j.succ) :
    ratioInteriorTest N p hp v x = v j.castSucc / ((N : ℝ) * (p j.succ - p j.castSucc)) := by
  unfold ratioInteriorTest
  rw [Finset.sum_eq_single j]
  · simp_all
  · intro l hl hlj
    apply indicator_of_notMem
    rcases lt_or_gt_of_ne hlj with hlt | hgt
    · have he : p l.succ ≤ p j.castSucc := hp.2.1.monotone (by
        simp_all)
      grind
    · have he : p j.succ ≤ p l.castSucc := hp.2.1.monotone (by
        simp_all)
      grind
  simp

theorem ratio_interiorTest_eq_density (hs : 2 * (k + 1) ≤ N) (v : Fin (k + 1) → ℝ)
    (j : Fin k) {x : ℝ} (hx : p j.castSucc ≤ x ∧ x < p j.succ) :
    ratioInteriorTest N p hp v x =
      v j.castSucc * rootStepDensity N (k + 1) p hp (by omega) hs x := by
  rw [ratio_interiorTest_on_cell hp v j hx, rootStepDensity_interior hp hs j hx]
  ring

theorem ratio_interiorTest_outside (v : Fin (k + 1) → ℝ) {x : ℝ}
    (hx : x < p 0 ∨ p (Fin.last k) ≤ x) : ratioInteriorTest N p hp v x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply indicator_of_notMem
  rcases hx with hleft | hright
  · have he := hp.2.1.monotone (show (0 : Fin (k + 1)) ≤ j.castSucc from Fin.zero_le _)
    grind
  · have he := hp.2.1.monotone (show j.succ ≤ Fin.last k from Fin.le_last _)
    grind

theorem ratio_interiorTest_support (v : Fin (k + 1) → ℝ) {x : ℝ}
    (hx : x ∉ Icc (-Real.pi) Real.pi) : ratioInteriorTest N p hp v x = 0 := by
  apply ratio_interiorTest_outside hp v
  by_cases hlo : x < -Real.pi
  · exact Or.inl (hlo.trans (hp.1 0).1)
  · have hhi : Real.pi < x := by
      simp_all
    exact Or.inr ((hp.1 (Fin.last k)).2.le.trans hhi.le)

/-- A bounded root test times a bounded root density has a common compactly
supported majorant. This is the domination needed for moving-test limits. -/
theorem ratio_interiorTest_bound (hs : 2 * (k + 1) ≤ N)
    (v : Fin (k + 1) → ℝ) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hv : ∀ j, |v j| ≤ B)
    (hρ : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (k + 1) p hp (by omega) hs x ≤ M) (x : ℝ) :
    |ratioInteriorTest N p hp v x| ≤ (Icc (-Real.pi) Real.pi).indicator (fun _ => B * M) x := by
  by_cases hx : x ∈ Icc (-Real.pi) Real.pi
  · rw [indicator_of_mem hx]
    by_cases hleft : x < p 0
    · rw [ratio_interiorTest_outside hp v (Or.inl hleft), abs_zero]
      positivity
    by_cases hright : p (Fin.last k) ≤ x
    · rw [ratio_interiorTest_outside hp v (Or.inr hright), abs_zero]
      positivity
    obtain ⟨j, hj, hjx⟩ := exists_interior_root_cell (show 0 < k + 1 by omega) p
      (show p ⟨0, by omega⟩ ≤ x from le_of_not_gt hleft)
      (show x < p ⟨k + 1 - 1, by omega⟩ from lt_of_not_ge hright)
    let i : Fin k := ⟨j.val, by omega⟩
    have hxcell : p i.castSucc ≤ x ∧ x < p i.succ := by
      tauto
    rw [ratio_interiorTest_eq_density hp hs v i hxcell, abs_mul]
    have hrnonneg : 0 ≤ rootStepDensity N (k + 1) p hp (by omega) hs x := by
      rw [rootStepDensity_interior hp hs i hxcell]
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr
        (hp.2.1.monotone (Fin.castSucc_le_succ i))))
    rw [abs_of_nonneg hrnonneg]
    exact mul_le_mul (hv _) (hρ x hx) hrnonneg hB
  simp_all [ratio_interiorTest_support]
end

end PottsDiscontinuity.Bethe
