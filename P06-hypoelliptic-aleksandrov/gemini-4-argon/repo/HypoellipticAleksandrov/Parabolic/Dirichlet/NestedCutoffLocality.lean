module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10ValueBound

/-!
# Nested-cutoff locality for spatial difference quotients

This module identifies a cutoff-gradient quotient with multiplication of a
larger localized quotient when the latter cutoff is one on the smaller
cutoff's topological support.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

noncomputable def cutoffGradientL2Multiplier
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (i : Fin d) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y i)
    (cutoffGradient_aestronglyMeasurable η i) K η.gradient_bound_nonneg
    (cutoffGradient_norm_le η i)

private theorem norm_cutoffGradientL2Multiplier_apply_le
    {d Ω inner outer K}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (i : Fin d)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖cutoffGradientL2Multiplier (Ω := Ω) η i f‖ ≤ K * ‖f‖ := by
  simpa only [cutoffGradientL2Multiplier] using
    (norm_scalarL2Multiplier_apply_le
      (fun y => PDE.classicalGradient η.toFun y i)
      (cutoffGradient_aestronglyMeasurable η i) K η.gradient_bound_nonneg
      (cutoffGradient_norm_le η i) f)

/- The cutoff-gradient quotient factors through any larger cutoff whose
plateau contains the smaller cutoff's topological support. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_eq
    {d Ω innerη outerη innerχ outerχ Kη Kχ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ)
    (hχΩ : tsupport χ.toFun ⊆ Ω)
    (hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u) =
      cutoffGradientL2Multiplier (Ω := Ω) η i
        (valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ χ k h hχΩ hχshift u)) := by
  have _h_inl_10 : cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h = (cutoffGradientL2Multiplier (Ω := Ω) η i).comp (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet χ k h) := by
    let hΩ : MeasurableSet Ω := hΩ.measurableSet
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    have hmult :
        ⇑(cutoffGradientL2Multiplier (Ω := Ω) η i
          (localizedSpatialDifferenceQuotientL2 hΩ χ k h f)) =ᵐ[PDE.volumeOn Ω]
          fun y => PDE.classicalGradient η.toFun y i *
            localizedSpatialDifferenceQuotientL2 hΩ χ k h f y := by
      simpa only [cutoffGradientL2Multiplier] using
        (scalarL2Multiplier_apply_ae
          (fun y => PDE.classicalGradient η.toFun y i)
          (cutoffGradient_aestronglyMeasurable η i) Kη η.gradient_bound_nonneg
          (cutoffGradient_norm_le η i)
          (localizedSpatialDifferenceQuotientL2 hΩ χ k h f))
    filter_upwards [cutoffGradientSpatialDifferenceQuotientL2_apply_ae hΩ η i k h f,
      hmult, localizedSpatialDifferenceQuotientL2_apply_ae hΩ χ k h f]
        with y hleft hright hlocalized
    rw [hleft]
    change PDE.classicalGradient η.toFun y i *
        ((⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
            (y + h • PDE.basisVec k) -
          ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / h) =
      cutoffGradientL2Multiplier (Ω := Ω) η i
        (localizedSpatialDifferenceQuotientL2 hΩ χ k h f) y
    rw [hright, hlocalized, localizedSpatialDifferenceQuotient_apply]
    by_cases hy : y ∈ tsupport η.toFun
    · rw [χ.eq_one_on_inner y (hηχ hy)]
      ring
    · have _h_inl_8 : PDE.classicalGradient η.toFun y i = 0 := by
          rw [PDE.classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hy]
          exact ContinuousLinearMap.zero_apply _



      rw [_h_inl_8]
      ring
  have hfactor := congrArg
    (fun q : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) => q (valueCLM hΩ u))
    _h_inl_10
  have hvalue := congrArg
    (fun q : H10HilbertGraph hΩ →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) => q u)
    (valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM
      hΩ χ k h hχΩ hχshift)
  calc
    cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u) =
      cutoffGradientL2Multiplier (Ω := Ω) η i
        (localizedSpatialDifferenceQuotientL2
          hΩ.measurableSet χ k h (valueCLM hΩ u)) := by
        simpa only [ContinuousLinearMap.comp_apply] using hfactor
    _ = cutoffGradientL2Multiplier (Ω := Ω) η i
        (valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ χ k h hχΩ hχshift u)) := by
        apply congrArg (cutoffGradientL2Multiplier (Ω := Ω) η i)
        simpa only [ContinuousLinearMap.comp_apply] using hvalue.symm

/- The nested-cutoff gradient term is uniformly controlled by the input's
weak spatial gradient. -/
theorem norm_cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_le_gradient
    {d Ω innerη outerη innerχ outerχ Kη Kχ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ)
    (hχΩ : tsupport χ.toFun ⊆ Ω)
    (hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    ‖cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u)‖ ≤
      Kη * ‖gradientCLM hΩ u‖ := by
  rw [cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_eq
    hΩ η χ hηχ i k h hχΩ hχshift u]
  calc
    ‖cutoffGradientL2Multiplier (Ω := Ω) η i
        (valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ χ k h hχΩ hχshift u))‖ ≤
      Kη * ‖valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ χ k h hχΩ hχshift u)‖ :=
      norm_cutoffGradientL2Multiplier_apply_le η i _
    _ ≤ Kη * ‖gradientCLM hΩ u‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
          hΩ χ k h hχΩ hχshift u)
        η.gradient_bound_nonneg

end HypoellipticAleksandrov.Parabolic.Dirichlet
