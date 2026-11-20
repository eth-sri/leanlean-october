module

public import PottsDiscontinuity.Bethe.Theorem23Contraction
public import PottsDiscontinuity.Bethe.Theorem23Density
public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.Theorem23Mass

/-! # Continuous contraction applied to the discrete density -/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem intervalIntegrable_weighted_comp_kMap {lam : ℝ} (hlam : 0 < lam)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    IntervalIntegrable (fun β => Xi lam β * f (kMap lam β)) volume (-Real.pi) Real.pi := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hf ⊢
  exact integrableOn_Xi_mul_comp hlam hf

theorem weighted_cBEop_difference {Δ : ℝ} (hΔ : Δ < -1)
    {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi) (α : ℝ) :
    Xi (lamOf Δ) α *
        ((cBEop Δ f (kMap (lamOf Δ) α) - cBEop Δ g (kMap (lamOf Δ) α)) / (2 * Real.pi)) =
      -xiConv (2 * lamOf Δ)
        (fun β => Xi (lamOf Δ) β * (f (kMap (lamOf Δ) β) - g (kMap (lamOf Δ) β))) α := by
  have hlam := lamOf_pos hΔ
  have hX := Xi_pos hlam α
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
    congr 1
    funext β
    ring
  rw [hdiff, cBEop_kMap hΔ, hscale, xiConv]
  field_simp [ne_of_gt hX]
  ring

/-- Applying the continuous map contracts the weighted distance to `ρ`, up
    to the contribution of the mass defect. -/
theorem counting_continuous_contraction {Δ d : ℝ} (hΔ : Δ < -1)
    {s : ℝ → ℝ} (hc : Continuous s) (hMass : (∫ y in (-Real.pi)..Real.pi, s y) = 1 / 2 + d)
    {m : ℝ} (hm : 0 ≤ m) (hlower : ∀ t : ℝ, m ≤ Xi (2 * lamOf Δ) t)
    (hbdd : BddAbove (densityValues Δ (fun y => s y - rho Δ y)))
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α * (cBEop Δ s (kMap (lamOf Δ) α) / (2 * Real.pi) - rho Δ (kMap (lamOf Δ) α))| ≤
      (1 - m) * densityNorm Δ (fun y => s y - rho Δ y) + m * |d| / (2 * Real.pi) := by
  let R := fun β => Xi (lamOf Δ) β * (s (kMap (lamOf Δ) β) - rho Δ (kMap (lamOf Δ) β))
  have his := hc.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hiρ := (continuous_rho hΔ).intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hiR := intervalIntegrable_weighted_comp_kMap (lamOf_pos hΔ) (his.sub hiρ)
  have hmass : (∫ β in (-Real.pi)..Real.pi, R β) = d := by
    rw [← integral_Icc_comp_kMap (lamOf_pos hΔ) (fun y => s y - rho Δ y),
      intervalIntegral.integral_sub his hiρ, integral_rho_mass hΔ, hMass, add_sub_cancel_left]
  have hcontract := xiConv_abs_le_with_mass_defect (by linarith [lamOf_pos hΔ])
    hm hlower (f := R) hiR (fun β hβ => densityNorm_pointwise_le _ hbdd _ le_rfl hβ) α
  have hrho := rho_isCBESolution hΔ (kMap (lamOf Δ) α) (kMap_mem_Icc (lamOf_pos hΔ) hα)
  have hid := weighted_cBEop_difference hΔ his hiρ α
  rw [← hrho] at hid
  have hleft : Xi (lamOf Δ) α *
      (cBEop Δ s (kMap (lamOf Δ) α) / (2 * Real.pi) - rho Δ (kMap (lamOf Δ) α)) =
      -xiConv (2 * lamOf Δ) R α := by
    convert hid using 1
    field_simp
  simpa [hleft, hmass] using hcontract

end PottsDiscontinuity.Bethe
