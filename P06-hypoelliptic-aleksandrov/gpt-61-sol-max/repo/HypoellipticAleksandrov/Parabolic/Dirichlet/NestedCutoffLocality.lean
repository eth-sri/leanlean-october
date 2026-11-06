module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10ValueBound
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2

open private HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffGradient_eq_zero_of_not_mem_tsupport from HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2


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

variable {d : ℕ}




variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (i : Fin d)

/-- Multiplication by one coordinate of a quantitative cutoff gradient on
spatial restricted `L²`. -/
def cutoffGradientL2Multiplier
      :
    PDE.ScalarLp Ω (2 ) →L[ℝ]
      PDE.ScalarLp Ω (2 ) :=
  scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y i)
    (cutoffGradient_aestronglyMeasurable η i) K η.gradient_bound_nonneg
    (cutoffGradient_norm_le η i)

private theorem norm_cutoffGradientL2Multiplier_apply_le

    (f : PDE.ScalarLp Ω (2 )) :
    ‖cutoffGradientL2Multiplier  η i f‖ ≤ K * ‖f‖ := (id
  (norm_scalarL2Multiplier_apply_le (fun y => PDE.classicalGradient η.toFun y i)
    (cutoffGradient_aestronglyMeasurable η i) K (PDE.QuantitativeSmoothCutoff.gradient_bound_nonneg η)
    (cutoffGradient_norm_le η i) f))

variable {Ω innerη outerη innerχ outerχ : PDE.VelocityRegion d} {Kη Kχ : ℝ}

/-- The cutoff-gradient quotient factors through any larger cutoff whose
plateau contains the smaller cutoff's topological support. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_eq_comp_of_tsupport_subset


    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ) :
    cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h =
      (cutoffGradientL2Multiplier (Ω := Ω) η i).comp
        (localizedSpatialDifferenceQuotientL2 hΩ χ k h) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hmult :
      ⇑(cutoffGradientL2Multiplier  η i
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
    cutoffGradientL2Multiplier  η i
      (localizedSpatialDifferenceQuotientL2 hΩ χ k h f) y
  rw [hright, hlocalized, localizedSpatialDifferenceQuotient_apply]
  by_cases hy : y ∈ tsupport η.toFun
  · rw [χ.eq_one_on_inner y (hηχ hy)]
    ring
  · rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffGradient_eq_zero_of_not_mem_tsupport η i hy]
    ring

variable (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη) (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ) (hηχ : tsupport η.toFun ⊆ innerχ) (i k : Fin d) (h : ℝ) (hχΩ : tsupport χ.toFun ⊆ Ω) (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω) (u : H10HilbertGraph hΩ)

include hηχ in
/-- On arbitrary `H¹₀`, the cutoff-gradient quotient is multiplication of
the larger localized quotient's value by the smaller cutoff gradient. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_eq


     :
    cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u) =
      cutoffGradientL2Multiplier  η i
        (valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ χ k h hχΩ hχshift u)) := (Trans.trans
  (congrArg (fun q => q ((valueCLM hΩ) u))
    (cutoffGradientSpatialDifferenceQuotientL2_eq_comp_of_tsupport_subset (IsOpen.measurableSet hΩ) η χ hηχ i k h))
  (congrArg (⇑(cutoffGradientL2Multiplier η i))
    (id
      (Eq.symm
        (congrArg (fun q => q u) (valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM hΩ χ k h hχΩ hχshift))))))

include hηχ hχΩ hχshift in
/-- The nested-cutoff gradient term is uniformly controlled by the input's
weak spatial gradient. -/
theorem norm_cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_le_gradient


     :
    ‖cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u)‖ ≤
      Kη * ‖gradientCLM hΩ u‖ := by
  let sharedTerm_98fa102036 := ((valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ χ k h hχΩ hχshift u)))
  rw [cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_eq
    hΩ η χ hηχ i k h hχΩ hχshift u]
  calc
    ‖cutoffGradientL2Multiplier  η i
        sharedTerm_98fa102036‖ ≤
      Kη * ‖sharedTerm_98fa102036‖ :=
      norm_cutoffGradientL2Multiplier_apply_le η i _
    _ ≤ Kη * ‖gradientCLM hΩ u‖ := mul_le_mul_of_nonneg_left
        (norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
          hΩ χ k h hχΩ hχshift u)
        η.gradient_bound_nonneg

end HypoellipticAleksandrov.Parabolic.Dirichlet
