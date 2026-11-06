module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCutoffFields
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Localized reverse-time source difference-quotient fields

This module localizes the forward spatial difference quotient of smooth
reverse-time source data by a compact time--space cutoff.
-/

@[expose] public section


open Function Set

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

theorem contDiff_reverseTimeMap  (r₁ : ℝ) :
    ContDiff ℝ ⊤ (reverseTimeMap r₁ : TimeVelocity d → TimeVelocity d) := (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

/-- A time--space compact cutoff localizes the forward spatial difference
quotient of the reverse-time source to a continuous, compactly supported,
uniformly bounded field. -/
theorem exists_reverseTimeSource_cutoff_mul_spatialDifferenceQuotient_fields_of_smoothOnNeighborhood
     {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (r₀ r₁ : ℝ)
    (χ : PDE.QuantitativeSmoothCutoff inner outer K)
    (hχΩ : tsupport χ.toFun ⊆ Ω)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        Continuous (fun z : TimeVelocity d =>
          ζ z.1 * χ z.2 *
            spatialDifferenceQuotient k h
              (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z) ∧
        HasCompactSupport (fun z : TimeVelocity d =>
          ζ z.1 * χ z.2 *
            spatialDifferenceQuotient k h
              (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z) ∧
        ∀ z : TimeVelocity d, ‖ζ z.1 * χ z.2 *
          spatialDifferenceQuotient k h
            (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z‖ ≤ C := by
  let S : Set (TimeVelocity d) :=
    tsupport ζ ×ˢ tsupport χ.toFun
  let β : TimeVelocity d → ℝ := fun z => ζ z.1 * χ z.2
  have hS : IsCompact S := ζ.hasCompactSupport.isCompact.prod χ.hasCompactSupport.isCompact
  have hβS : tsupport β ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro z hz
    constructor
    · apply subset_tsupport
      aesop
    · apply subset_tsupport
      aesop
  have hβcompact : HasCompactSupport β :=
    hS.of_isClosed_subset (isClosed_tsupport β) hβS
  have hβcont : Continuous β := (ζ.contDiff.continuous.comp continuous_fst).mul
      (χ.smooth.continuous.comp continuous_snd)
  have hβunit : ∀ z : TimeVelocity d, ‖β z‖ ≤ 1 := by
    intro z
    have hχunit : ‖χ z.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (χ.nonneg z.2)]
      exact χ.le_one z.2
    calc
      ‖β z‖ = ‖ζ z.1‖ * ‖χ z.2‖ := by
        aesop
      _ ≤ 1 * 1 := mul_le_mul (hζunit z.1) hχunit (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rcases hFSmooth with ⟨V, hVopen, hcylV, hFV⟩
  let U  := reverseTimeMap r₁ ⁻¹' V
  have hU : IsOpen U := (contDiff_reverseTimeMap r₁).continuous.isOpen_preimage V hVopen
  have hSU : S ⊆ U := by
    intro z hz
    have htime : z.1 ∈ Set.Ioo 0 _ :=
      ζ.tsupport_subset hz.1
    have hspace  := subset_closure (hχΩ hz.2)
    apply hcylV
    exact (mem_scalarParabolicClosedCylinder_iff).2
      ⟨by grind,
        by grind,
        by omega⟩
  have hq : ContDiffOn ℝ 1
      (fun w : TimeVelocity d => F (r₁ - w.1) w.2) U := by
    have hFVone : ContDiffOn ℝ 1 _ V :=
      hFV.of_le (by simp)
    have hrevone : ContDiffOn ℝ 1 _ U :=
      (contDiff_reverseTimeMap r₁).of_le (by simp) |>.contDiffOn
    simpa only [Function.comp_def, reverseTimeMap_apply] using
      hFVone.comp hrevone
        (fun w hw => hw)
  obtain ⟨δ, C, hδ, hC, hfields⟩ :=
    IsCompact.exists_cutoff_mul_spatialFields_of_contDiffOn_one hS hU hSU _ hq
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro k h hh
  simpa only [β, mul_assoc] using
    (hfields β hβcont hβcompact hβS hβunit k h hh).2

end HypoellipticAleksandrov.Parabolic.Dirichlet
