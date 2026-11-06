module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCutoffFields
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Basic
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness



/-!
# Localized reverse-time source difference-quotient fields

This module localizes the forward spatial difference quotient of smooth
reverse-time source data by a compact time--space cutoff.
-/

 public section



open Set

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}



/-- A time--space compact cutoff localizes the forward spatial difference
quotient of the reverse-time source to a continuous, compactly supported,
uniformly bounded field. -/
theorem exists_reverseTimeSource_cutoff_mul_spatialDifferenceQuotient_fields_of_smoothOnNeighborhood
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (r₀ r₁ : ℝ)
    (χ : PDE.QuantitativeSmoothCutoff inner outer K)
    (hχΩ : tsupport χ.toFun ⊆ Ω)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        Continuous (fun z  =>
          ζ z.1 * χ z.2 *
            spatialDifferenceQuotient k h
              (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z) ∧
        HasCompactSupport (fun z  =>
          ζ z.1 * χ z.2 *
            spatialDifferenceQuotient k h
              (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z) ∧
        ∀ z : TimeVelocity d, ‖ζ z.1 * χ z.2 *
          spatialDifferenceQuotient k h
            (fun w  => F (r₁ - w.1) w.2) z‖ ≤ C := by
  let S  :=
    tsupport (ζ : ℝ → ℝ) ×ˢ tsupport χ.toFun
  let β : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * χ z.2
  have hS  := ζ.hasCompactSupport.isCompact.prod χ.hasCompactSupport.isCompact
  have hβS : tsupport β ⊆ S := by
    change closure (Function.support β) ⊆ S
    apply closure_minimal _ hS.isClosed
    intro z hz
    constructor
    · apply subset_tsupport
      change ζ z.1 ≠ 0
      intro hzero
      apply hz
      simp only [β, hzero, zero_mul]
    · apply subset_tsupport
      change χ z.2 ≠ 0
      intro hzero
      apply hz
      simp only [β, hzero, mul_zero]



  rcases hFSmooth with ⟨V, hVopen, hcylV, hFV⟩




  obtain ⟨δ, C, hδ, hC, hfields⟩ :=
    IsCompact.exists_cutoff_mul_spatialFields_of_contDiffOn_one hS (by
        exact (contDiff_reverseTimeMap r₁).continuous.isOpen_preimage V hVopen) (by
        intro z hz
        have htime  :=
          ζ.tsupport_subset hz.1
        have hspace  := subset_closure (hχΩ hz.2)
        change reverseTimeMap r₁ z ∈ V
        apply hcylV
        exact (mem_scalarParabolicClosedCylinder_iff).2
          ⟨by simpa only using (show r₀ ≤ r₁ - z.1 from by linarith [htime.2]),
            by simpa only using (show r₁ - z.1 ≤ r₁ from by linarith [htime.1]),
            hspace⟩) _ (by


        simpa only [Function.comp_def, reverseTimeMap_apply] using
          (show ContDiffOn ℝ 1 (fun z : TimeVelocity d => F z.1 z.2) V from hFV.of_le (by simp)).comp (show ContDiffOn ℝ 1 (reverseTimeMap r₁ : TimeVelocity d → TimeVelocity d) (reverseTimeMap r₁ ⁻¹' V) from (contDiff_reverseTimeMap r₁).of_le (by simp) |>.contDiffOn)
            (fun w hw => hw))
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro k h hh
  exact (hfields β (by
      exact (ζ.contDiff.continuous.comp continuous_fst).mul
        (χ.smooth.continuous.comp continuous_snd)) (hS.of_isClosed_subset (isClosed_tsupport β) hβS) hβS (by
      intro z

      calc
        ‖β z‖ = ‖ζ z.1‖ * ‖χ z.2‖ := by
          simp only [β, norm_mul]
        _ ≤ 1 * 1 := mul_le_mul (hζunit z.1) (show _ by
            rw [Real.norm_eq_abs, abs_of_nonneg (χ.nonneg z.2)]
            exact χ.le_one z.2) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1) k h hh).2

end HypoellipticAleksandrov.Parabolic.Dirichlet
