module

public import HypoellipticAleksandrov.Measure.LpZeroExtension
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise

/-!
# Localized spatial difference quotients on restricted `L²`

This module constructs the representative-independent cutoff-weighted forward
spatial difference quotient using ambient zero extension, translation,
restriction, and multiplication on quotient `L²` spaces.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
  (η : PDE.QuantitativeSmoothCutoff inner outer K)

/-- A smooth cutoff is almost everywhere strongly measurable on restricted volume. -/
theorem cutoff_aestronglyMeasurable :
    AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
  η.smooth.continuous.aestronglyMeasurable

/-- A quantitative smooth cutoff has norm at most one almost everywhere. -/
theorem cutoff_norm_le_one :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖η.toFun y‖ ≤ (1 : ℝ) :=
  ae_of_all _ fun y => η.norm_le_one y

end

section DifferenceQuotient

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : MeasurableSet Ω) (k : Fin d) (h : ℝ)
local notation "shift" => (h • PDE.basisVec k)
local notation "translateLp" => Lp.compMeasurePreservingₗᵢ ℝ (fun y => y + shift)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d)) shift)
local notation "extendLp" => Lp.zeroExtendLinearIsometry (μ := volume) hΩ
local notation "restrictLp" => LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω

/-- Difference quotient of the ambient zero extension, restricted to the domain. -/
def unweightedSpatialDifferenceQuotientL2 : PDE.ScalarLp Ω 2 →L[ℝ] PDE.ScalarLp Ω 2 :=
  h⁻¹ • (restrictLp).comp ((translateLp).toContinuousLinearMap.comp (extendLp).toContinuousLinearMap -
    (extendLp).toContinuousLinearMap)

/-- The zero-extension formula for the representative-independent quotient. -/
theorem unweightedSpatialDifferenceQuotientL2_apply_ae (f : PDE.ScalarLp Ω 2) :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k h f) =ᵐ[PDE.volumeOn Ω]
      fun y => ((extendLp f : PDE.Vec d → ℝ) (y + shift) - extendLp f y) / h := by
  let g : Lp ℝ 2 (volume : Measure (PDE.Vec d)) := extendLp f
  let v := translateLp g - g
  change ⇑(h⁻¹ • restrictLp v) =ᵐ[PDE.volumeOn Ω] _
  have hp : ⇑(translateLp g) =ᵐ[volume] (⇑g ∘ fun y => y + shift) :=
    Lp.coeFn_compMeasurePreserving g
      (measurePreserving_add_right (volume : Measure (PDE.Vec d)) shift)
  filter_upwards [Lp.coeFn_smul h⁻¹ (restrictLp v), LpToLpRestrictCLM_coeFn ℝ Ω v,
    (Lp.coeFn_sub (translateLp g) g).restrict (s := Ω), hp.restrict (s := Ω)] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.smul_apply, h₂, h₃, Pi.sub_apply, h₄]
  simp only [div_eq_mul_inv, Function.comp_apply, smul_eq_mul, mul_comm, g]

/-- A representative supported in the domain also represents the global zero extension. -/
theorem unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    (f : PDE.ScalarLp Ω 2) (g : PDE.Vec d → ℝ) (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hg : Function.support g ⊆ Ω) :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k h f) =ᵐ[PDE.volumeOn Ω]
      fun y => (g (y + shift) - g y) / h := by
  have hz : ⇑(extendLp f) =ᵐ[volume] g := by
    filter_upwards [Lp.coeFn_zeroExtendLinearIsometry hΩ f, ae_imp_of_ae_restrict hfg] with y hy hfy
    by_cases hm : y ∈ Ω
    · rw [hy, Set.indicator_of_mem hm]; exact hfy hm
    · rw [hy, Set.indicator_of_notMem hm]
      exact Eq.symm (Function.notMem_support.mp fun h => hm (hg h))
  have hshift := (measurePreserving_add_right (volume : Measure (PDE.Vec d)) shift).quasiMeasurePreserving.ae hz
  filter_upwards [unweightedSpatialDifferenceQuotientL2_apply_ae hΩ k h f,
    ae_restrict_of_ae hz, ae_restrict_of_ae (s := Ω) hshift] with y hy hz hshift
  rw [hy, hz, hshift]

variable (q : PDE.Vec d → ℝ) (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)

/-- A spatial quotient followed by multiplication by a bounded field. -/
def weightedSpatialDifferenceQuotientL2 : PDE.ScalarLp Ω 2 →L[ℝ] PDE.ScalarLp Ω 2 :=
  (scalarL2Multiplier q hq C hC hbound).comp (unweightedSpatialDifferenceQuotientL2 hΩ k h)

/-- Representative formula for a weighted spatial quotient. -/
theorem weightedSpatialDifferenceQuotientL2_apply_ae (f : PDE.ScalarLp Ω 2) :
    ⇑(weightedSpatialDifferenceQuotientL2 hΩ k h q hq C hC hbound f) =ᵐ[PDE.volumeOn Ω]
      fun y => q y * (((extendLp f : PDE.Vec d → ℝ) (y + shift) - extendLp f y) / h) := by
  filter_upwards [scalarL2Multiplier_apply_ae q hq C hC hbound (unweightedSpatialDifferenceQuotientL2 hΩ k h f),
    unweightedSpatialDifferenceQuotientL2_apply_ae hΩ k h f] with y hy hd
  rw [show weightedSpatialDifferenceQuotientL2 hΩ k h q hq C hC hbound f =
    scalarL2Multiplier q hq C hC hbound (unweightedSpatialDifferenceQuotientL2 hΩ k h f) from rfl, hy, hd]

/-- At points where the weight is active, only the local representative is needed. -/
theorem weightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    (f : PDE.ScalarLp Ω 2) (g : PDE.Vec d → ℝ) (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hshift : ∀ y, q y ≠ 0 → y + shift ∈ Ω) :
    ⇑(weightedSpatialDifferenceQuotientL2 hΩ k h q hq C hC hbound f) =ᵐ[PDE.volumeOn Ω]
      fun y => q y * ((g (y + shift) - g y) / h) := by
  have hz : ∀ᵐ y : PDE.Vec d ∂volume, y ∈ Ω → extendLp f y = g y := by
    filter_upwards [Lp.coeFn_zeroExtendLinearIsometry hΩ f, ae_imp_of_ae_restrict hfg] with y hy hfy hm
    rw [hy, Set.indicator_of_mem hm]; exact hfy hm
  have htrans := (measurePreserving_add_right (volume : Measure (PDE.Vec d)) shift).quasiMeasurePreserving.ae hz
  filter_upwards [weightedSpatialDifferenceQuotientL2_apply_ae hΩ k h q hq C hC hbound f,
    ae_restrict_of_ae hz, ae_restrict_of_ae (s := Ω) htrans, ae_restrict_mem (μ := volume) hΩ] with y hy hz ht hm
  rw [hy]
  by_cases hqz : q y = 0
  · simp [hqz]
  · rw [hz hm, ht (hshift y hqz)]

end DifferenceQuotient

/-- The representative-independent cutoff-weighted forward spatial difference
quotient on restricted-volume scalar `L²`. -/
noncomputable def localizedSpatialDifferenceQuotientL2
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  weightedSpatialDifferenceQuotientL2 hΩ k h η.toFun (cutoff_aestronglyMeasurable η)
    1 zero_le_one (cutoff_norm_le_one η)

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : MeasurableSet Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)
  (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))

/-- The restricted-space quotient agrees almost everywhere with the canonical
zero-extension representative formula. -/
theorem localizedSpatialDifferenceQuotientL2_apply_ae :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ η k h f) =ᵐ[PDE.volumeOn Ω]
      fun y => localizedSpatialDifferenceQuotient η k h
        (⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)) y :=
  weightedSpatialDifferenceQuotientL2_apply_ae hΩ k h η.toFun (cutoff_aestronglyMeasurable η)
    1 zero_le_one (cutoff_norm_le_one η) f

/-- A supplied restricted-space representative may replace the canonical zero
extension on the cutoff's forward active collar. -/
theorem localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    (g : PDE.Vec d → ℝ)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hηshift : η.ShiftMapsInto k h Ω) :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ η k h f) =ᵐ[PDE.volumeOn Ω]
      localizedSpatialDifferenceQuotient η k h g :=
  weightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq hΩ k h η.toFun (cutoff_aestronglyMeasurable η)
    1 zero_le_one (cutoff_norm_le_one η) f g hfg (fun y hy => hηshift (subset_tsupport η.toFun hy))

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
