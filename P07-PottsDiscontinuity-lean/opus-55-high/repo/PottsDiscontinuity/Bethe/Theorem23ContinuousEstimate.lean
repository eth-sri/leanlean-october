module

public import PottsDiscontinuity.Bethe.Theorem23Contraction
public import PottsDiscontinuity.Bethe.Theorem23Density
public import PottsDiscontinuity.Bethe.Theorem23Mass

/-! # Continuous contraction applied to the discrete density -/

public section

open Set MeasureTheory intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem intervalIntegrable_weighted_comp_kMap {lam : ℝ} (hlam : 0 < lam)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    IntervalIntegrable (fun β => Xi lam β * f (kMap lam β)) volume (-Real.pi) Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])] at hf ⊢
  exact integrableOn_Xi_mul_comp hlam hf

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
theorem weighted_cBEop_difference {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi) (α : ℝ) :
    Xi (lamOf Δ) α *
        ((cBEop Δ f (kMap (lamOf Δ) α) - cBEop Δ g (kMap (lamOf Δ) α)) / (2 * Real.pi)) =
      -xiConv (2 * lamOf Δ)
        (fun β => Xi (lamOf Δ) β * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β))) α := by
  have hX := Xi_pos (lamOf_pos hΔ) α
  have hc := continuous_d1Theta_right hΔ (kMap (lamOf Δ) α)
  have hdiff : cBEop Δ f (kMap (lamOf Δ) α) - cBEop Δ g (kMap (lamOf Δ) α) =
      cBEop Δ (fun y => f y - g y) (kMap (lamOf Δ) α) - 1 := by
    unfold cBEop
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hf.continuousOn_mul hc.continuousOn)
      (hg.continuousOn_mul hc.continuousOn)]
    ring
  have hscale : (∫ β in (-Real.pi)..Real.pi,
        Xi (2 * lamOf Δ) (α - β) *
          (2 * Real.pi * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β)) * Xi (lamOf Δ) β)) =
      (2 * Real.pi) * ∫ β in (-Real.pi)..Real.pi,
        Xi (2 * lamOf Δ) (α - β) *
          (Xi (lamOf Δ) β * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β))) := by
    rw [← intervalIntegral.integral_const_mul]
    grind
  rw [hdiff, cBEop_kMap hΔ, hscale, xiConv]
  grind

/-- Applying the continuous map to the step density contracts its weighted
distance to `ρ`, up to the exact mass-defect contribution. -/
theorem root_step_continuous_contraction {N k r : ℕ} (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
    (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ((k + 1) + r))
    {m : ℝ} (hm : 0 ≤ m) (hlower : ∀ t : ℝ, m ≤ Xi (2 * lamOf Δ) t)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N (k + 1) p hp (by omega) hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α *
        (cBEop Δ (rootStepDensity N (k + 1) p hp (by omega) hs) (kMap (lamOf Δ) α) /
          (2 * Real.pi) - rho Δ (kMap (lamOf Δ) α))| ≤
      (1 - m) * densityNorm Δ hΔ
        (fun y => rootStepDensity N (k + 1) p hp (by omega) hs y - rho Δ y) hbdd +
        m * (r : ℝ) / (2 * Real.pi * (N : ℝ)) := by
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let R := fun β => Xi (lamOf Δ) β * (s (kMap (lamOf Δ) β) - rho Δ (kMap (lamOf Δ) β))
  have his : IntervalIntegrable s volume (-Real.pi) Real.pi := by
    simpa [s] using intervalIntegrable_mul_rootStepDensity p hp (by omega) hs
      (g := fun _ => (1 : ℝ)) continuous_const (-Real.pi) Real.pi
  have hiρ : IntervalIntegrable (rho Δ) volume (-Real.pi) Real.pi :=
    (continuous_rho hΔ).intervalIntegrable _ _
  have hmass : (∫ β in (-Real.pi)..Real.pi, R β) = (r : ℝ) / N := by
    rw [← integral_Icc_comp_kMap (lamOf_pos hΔ) (fun y => s y - rho Δ y), intervalIntegral.integral_sub his hiρ, integral_rho_mass hΔ, root_step_physical_mass hp hs hcount]
    ring
  have hbound : ∀ β ∈ Icc (-Real.pi) Real.pi,
      |R β| ≤ densityNorm Δ hΔ (fun y => s y - rho Δ y) hbdd := by
    intro β hβ
    exact densityNorm_pointwise_le hΔ (fun y => s y - rho Δ y) hbdd _ le_rfl hβ
  have hcontract := xiConv_abs_le_with_mass_defect (by linarith [lamOf_pos hΔ])
    hm hlower (intervalIntegrable_weighted_comp_kMap (lamOf_pos hΔ) (his.sub hiρ)) hbound α
  have hrho := rho_isCBESolution hΔ (kMap (lamOf Δ) α)
    (kMap_mem_Icc (lamOf_pos hΔ) hα)
  have hid := weighted_cBEop_difference hΔ his hiρ α
  rw [hrho.symm] at hid
  have hleft : Xi (lamOf Δ) α *
      (cBEop Δ s (kMap (lamOf Δ) α) / (2 * Real.pi) - rho Δ (kMap (lamOf Δ) α)) =
      -xiConv (2 * lamOf Δ) R α := by
    convert hid using 1
    field_simp
  rw [hleft, abs_neg]
  have hrNonneg : 0 ≤ (r : ℝ) / N := by positivity
  rw [hmass, abs_of_nonneg hrNonneg] at hcontract
  convert hcontract using 1
  ring
end

end PottsDiscontinuity.Bethe
