module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Topology.Support
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder

open private HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialDifferenceQuotient_slice from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialTranslate_slice from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_drift_smoothOn_closedCylinder from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_coefficient_smoothOn_closedCylinder from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_scalar_smoothOn_closedCylinder from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.fintype_sum_sum_const_mul from HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeMap_image_closedCylinder_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.fintype_sum_const_mul from HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore


/-!
# Exact H10 commutator split
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet




variable {d : ℕ}



















section
variable {Ω : PDE.VelocityRegion d} (q : PDE.ScalarField d) (hq : Continuous q) (hcompact : HasCompactSupport q) (f g : PDE.ScalarLp Ω (2 ))

include hq hcompact
private theorem integrable_weighted_scalarLp_pair
      :
    Integrable (fun y => q y * f y * g y) (PDE.volumeOn Ω) := by



  have hweighted := ((Lp.memLp f).integrable_mul (Lp.memLp g)).mul_of_top_right ((hq.memLp_of_hasCompactSupport hcompact).restrict Ω)
  convert hweighted using 1
  ext y
  simp only [Pi.mul_apply]
  ring

private theorem integrable_weighted_scalarLp_pair_raw

    (p r : PDE.ScalarField d) (hf : ⇑f =ᵐ[PDE.volumeOn Ω] p)
    (hg : ⇑g =ᵐ[PDE.volumeOn Ω] r) :
    Integrable (fun y => (q y * p y) * r y) (PDE.volumeOn Ω) := by
  apply (integrable_weighted_scalarLp_pair q hq hcompact f g).congr
  filter_upwards [hf, hg] with y hyf hyg
  rw [hyf, hyg]
end


variable {Ω inner : PDE.VelocityRegion d} {Kη : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)

variable (k : Fin d) (h : ℝ) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) (i : Fin d)

private theorem h10_E_coord_ae
       :
    ⇑(PDE.hilbertVectorLpCoord Ω (2 ) i
        (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)) -
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) y -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) y := by
  filter_upwards [MeasureTheory.Lp.coeFn_sub
    (PDE.hilbertVectorLpCoord Ω (2 ) i
      (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift u)))
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u))] with y hy
  rw [hy]
  rfl

private theorem h10_H_coord_ae
       :
    ⇑(PDE.hilbertVectorLpCoord Ω (2 ) i
        (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)) +
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) y +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) y := by
  filter_upwards [MeasureTheory.Lp.coeFn_add
    (PDE.hilbertVectorLpCoord Ω (2 ) i
      (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift u)))
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u))] with y hy
  rw [hy]
  rfl

variable (u : H10HilbertGraph hΩ)

private theorem h10_U_coord_ae
       (j : Fin d) :
    ⇑(scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable)
      1 zero_le_one (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
        exact η.le_one y)
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))) =ᵐ[PDE.volumeOn Ω]
      fun y => η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y := scalarL2Multiplier_apply_ae η.toFun (η.smooth.continuous.aestronglyMeasurable)
    1 zero_le_one (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y) _

private theorem h10_U0_ae
       :
    ⇑(scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable)
      1 zero_le_one (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
        exact η.le_one y) (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
      fun y => η y * valueCLM hΩ u y := scalarL2Multiplier_apply_ae η.toFun (η.smooth.continuous.aestronglyMeasurable)
    1 zero_le_one (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y) _

private theorem integral_pair_add_const_mul
     {Ω : PDE.VelocityRegion d} (z : ℝ) (f g : PDE.ScalarField d)
    (hf : Integrable f (PDE.volumeOn Ω)) (hg : Integrable g (PDE.volumeOn Ω)) :
    (∫ y in Ω, (z * f y) + (z * g y)) =
      z * ((∫ y in Ω, f y) + (∫ y in Ω, g y)) := by
  rw [integral_add (hf.const_mul z) (hg.const_mul z), integral_const_mul,
    integral_const_mul]
  ring









section

variable {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}
variable (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
variable (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
variable (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
variable (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
variable (k : Fin d) (h τ : ℝ)
variable (hχshift : Set.MapsTo
  (fun y  => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω)
variable (hηshift : Set.MapsTo
  (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
variable (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)

include r₀ ha hτ hχshift

variable (i j : Fin d)

private theorem integrable_aT_E_H  :
    Integrable (fun y =>
      (χ y * spatialTranslate k h
          (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)) *
        (PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y -
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
            (valueCLM hΩ u) y) *
        (PDE.hilbertVectorLpCoord Ω (2 ) i
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y +
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
            (valueCLM hΩ u) y))
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let E : PDE.ScalarLp Ω (2 ) :=
    PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ (A u)) -
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
        (valueCLM hΩ u)
  let H : PDE.ScalarLp Ω (2 ) :=
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) +
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)
  let q  := fun y => χ y * spatialTranslate k h
    (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)




  simpa only [q, A] using
    (integrable_weighted_scalarLp_pair_raw q (by
        dsimp only [q]
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h _
          (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j) hτ hχshift) ((id (HasCompactSupport.mul_right χ.hasCompactSupport))) E H _ _ (by
        dsimp only [E, A]
        exact h10_E_coord_ae hΩ η k h hηshift u j) (by
        dsimp only [H, A]
        exact h10_H_coord_ae hΩ η k h hηshift u i))

private theorem integrable_aD_U_H  :
    Integrable (fun y =>
      (χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)) *
        (η y * PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ u) y) *
        (PDE.hilbertVectorLpCoord Ω (2 ) i
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y +
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
            (valueCLM hΩ u) y))
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let H : PDE.ScalarLp Ω (2 ) :=
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) +
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)

  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U : PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)) 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let q  := fun y => χ y * spatialDifferenceQuotient k h
    (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)




  simpa only [q, A] using
    (integrable_weighted_scalarLp_pair_raw q (by
        dsimp only [q]
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h _
          (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j) hτ hχshift) ((id (HasCompactSupport.mul_right χ.hasCompactSupport))) U H _ _ (by
        dsimp only [U]
        exact h10_U_coord_ae hΩ η u j) (by
        dsimp only [H, A]
        exact h10_H_coord_ae hΩ η k h hηshift u i))

omit r₀ ha hτ hχshift

include r₀ ha hb hτ hχshift

variable (j : Fin d)

private theorem integrable_driftT_E_V  :
    Integrable (fun y =>
      (χ y * spatialTranslate k h
          (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)) *
        (PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y -
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
            (valueCLM hΩ u) y) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let E : PDE.ScalarLp Ω (2 ) :=
    PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ (A u)) -
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
        (valueCLM hΩ u)
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let q  := fun y => χ y * spatialTranslate k h
    (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)




  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q (by
        dsimp only [q]
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h _
          (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_drift_smoothOn_closedCylinder r₀ r₁ a b ha hb j) hτ hχshift) ((id (HasCompactSupport.mul_right χ.hasCompactSupport))) E V _ _ (by
        dsimp only [E, A]
        exact h10_E_coord_ae hΩ η k h hηshift u j) (Filter.Eventually.of_forall fun _ => rfl))

private theorem integrable_driftD_U_V  :
    Integrable (fun y =>
      (χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)) *
        (η y * PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ u) y) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)

  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U : PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)) 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let q  := fun y => χ y * spatialDifferenceQuotient k h
    (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)




  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q (by
        dsimp only [q]
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h _
          (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_drift_smoothOn_closedCylinder r₀ r₁ a b ha hb j) hτ hχshift) ((id (HasCompactSupport.mul_right χ.hasCompactSupport))) U V _ _ (by
        dsimp only [U]
        exact h10_U_coord_ae hΩ η u j) (Filter.Eventually.of_forall fun _ => rfl))

omit r₀ ha hb hτ hχshift

include r₀ hc hτ hχshift

private theorem integrable_gammaT_V_V :
    Integrable (fun y =>
      (χ y * spatialTranslate k h
          (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let q  := fun y => χ y * spatialTranslate k h
    (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)


  have hV : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y :=
    Filter.Eventually.of_forall fun _ => rfl
  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q (by
        dsimp only [q]
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h _
          (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_scalar_smoothOn_closedCylinder r₀ r₁ c hc) hτ hχshift) ((id (HasCompactSupport.mul_right χ.hasCompactSupport))) V V _ _ hV hV)

private theorem integrable_gammaD_U0_V :
    Integrable (fun y =>
      (χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)) *
        (η y * valueCLM hΩ u y) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)

  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U₀ : PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)) 1 zero_le_one ηBound (valueCLM hΩ u)
  let q  := fun y => χ y * spatialDifferenceQuotient k h
    (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)




  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q (by
        dsimp only [q]
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h _
          (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_scalar_smoothOn_closedCylinder r₀ r₁ c hc) hτ hχshift) ((id (HasCompactSupport.mul_right χ.hasCompactSupport))) U₀ V _ _ (by
        dsimp only [U₀]
        exact h10_U0_ae hΩ η u) (Filter.Eventually.of_forall fun _ => rfl))

omit r₀ hc hτ hχshift

end

variable {d : ℕ}

variable {Ω : PDE.VelocityRegion d} (z : ℝ)

private theorem integral_pair_mul_const

    (q₁ p₁ q₂ p₂ g : PDE.ScalarField d)
    (h₁ : Integrable (fun y => (q₁ y * p₁ y) * g y) (PDE.volumeOn Ω))
    (h₂ : Integrable (fun y => (q₂ y * p₂ y) * g y) (PDE.volumeOn Ω)) :
    (∫ y in Ω, ((z * q₁ y) * p₁ y + (z * q₂ y) * p₂ y) * g y) =
      z * ((∫ y in Ω, (q₁ y * p₁ y) * g y) +
        ∫ y in Ω, (q₂ y * p₂ y) * g y) := by
  rw [show (fun y => ((z * q₁ y) * p₁ y + (z * q₂ y) * p₂ y) * g y) =
      fun y => z * ((q₁ y * p₁ y) * g y) + z * ((q₂ y * p₂ y) * g y) by
        funext y
        ring]
  exact integral_pair_add_const_mul z _ _ h₁ h₂

private theorem raw_six_term_split

    (source V U₀ : PDE.ScalarField d)
    (aT aD : Fin d → Fin d → PDE.ScalarField d)
    (E H U driftT driftD : Fin d → PDE.ScalarField d)
    (gammaT gammaD : PDE.ScalarField d)
    (haT : ∀ i j : Fin d, Integrable (fun y =>
      (aT i j y * E j y) * H i y) (PDE.volumeOn Ω))
    (haD : ∀ i j : Fin d, Integrable (fun y =>
      (aD i j y * U j y) * H i y) (PDE.volumeOn Ω))
    (hdt : ∀ j : Fin d, Integrable (fun y =>
      (driftT j y * E j y) * V y) (PDE.volumeOn Ω))
    (hdd : ∀ j : Fin d, Integrable (fun y =>
      (driftD j y * U j y) * V y) (PDE.volumeOn Ω))
    (hgt : Integrable (fun y => (gammaT y * V y) * V y) (PDE.volumeOn Ω))
    (hgd : Integrable (fun y => (gammaD y * U₀ y) * V y) (PDE.volumeOn Ω)) :
    -(∫ y in Ω, (z * source y) * V y) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y) -
        (∑ j : Fin d, ∫ y in Ω,
          ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y) +
        ∫ y in Ω, ((z * gammaT y) * V y + (z * gammaD y) * U₀ y) * V y =
      -(∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y) +
        z *
          (-(∫ y in Ω, source y * V y) -
              (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
                (aD i j y * U j y) * H i y) -
              (∑ j : Fin d, ∫ y in Ω,
                (driftT j y * E j y) * V y) -
              (∑ j : Fin d, ∫ y in Ω,
                (driftD j y * U j y) * V y) +
              (∫ y in Ω, (gammaT y * V y) * V y) +
              ∫ y in Ω, (gammaD y * U₀ y) * V y) := by
  let S : ℝ := ∫ y in Ω, source y * V y
  let P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (aT i j y * E j y) * H i y
  let AD : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (aD i j y * U j y) * H i y
  let DT : ℝ := ∑ j : Fin d, ∫ y in Ω,
    (driftT j y * E j y) * V y
  let DD : ℝ := ∑ j : Fin d, ∫ y in Ω,
    (driftD j y * U j y) * V y
  let GT : ℝ := ∫ y in Ω, (gammaT y * V y) * V y
  let GD : ℝ := ∫ y in Ω, (gammaD y * U₀ y) * V y
  have hsource : (∫ y in Ω, (z * source y) * V y) = z * S := by
    dsimp only [S]
    rw [show (fun y => (z * source y) * V y) =
        fun y => z * (source y * V y) by funext y; ring, integral_const_mul]
  have hprincipal (i j : Fin d)  :=
    integral_pair_mul_const z (aT i j) (E j) (aD i j) (U j) (H i) (haT i j) (haD i j)
  have hprincipalSum :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y) =
        z * (P + AD) := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y) =
        ∑ i : Fin d, ∑ j : Fin d, z *
          ((∫ y in Ω, (aT i j y * E j y) * H i y) +
            ∫ y in Ω, (aD i j y * U j y) * H i y) by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hprincipal i j]
    rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.fintype_sum_sum_const_mul]
    dsimp only [P, AD]
    simp_rw [Finset.sum_add_distrib]
  have hprincipalWeighted :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y) = z * P := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y) =
        ∑ i : Fin d, ∑ j : Fin d, z *
          ∫ y in Ω, (aT i j y * E j y) * H i y by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [show (fun y => (z * aT i j y) * E j y * H i y) =
              fun y => z * ((aT i j y * E j y) * H i y) by funext y; ring,
            integral_const_mul]]
    rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.fintype_sum_sum_const_mul]
  have hdrift (j : Fin d)  :=
    integral_pair_mul_const z (driftT j) (E j) (driftD j) (U j) V (hdt j) (hdd j)
  have hdriftSum :
      (∑ j : Fin d, ∫ y in Ω,
        ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y) =
        z * (DT + DD) := by
    rw [show (∑ j : Fin d, ∫ y in Ω,
        ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y) =
        ∑ j : Fin d, z *
          ((∫ y in Ω, (driftT j y * E j y) * V y) +
            ∫ y in Ω, (driftD j y * U j y) * V y) by
          apply Finset.sum_congr rfl
          intro j _
          exact hdrift j]
    rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.fintype_sum_const_mul]
    dsimp only [DT, DD]
    simp_rw [Finset.sum_add_distrib]
  have hscalar :
      (∫ y in Ω, ((z * gammaT y) * V y + (z * gammaD y) * U₀ y) * V y) =
        z * (GT + GD) := by
    dsimp only [GT, GD]
    exact integral_pair_mul_const z gammaT V gammaD U₀ V hgt hgd
  linarith

variable {Ω inner : PDE.VelocityRegion d}

variable {Kη Kχ : ℝ} (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)

private def commutatorRaw

    (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarField d := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.ScalarField d := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.ScalarField d := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.ScalarField d := fun i y => G i y - W i y
  let H : Fin d → PDE.ScalarField d := fun i y => G i y + W i y
  let U : Fin d → PDE.ScalarField d := fun j y =>
    η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y
  let U₀ : PDE.ScalarField d := fun y => η y * valueCLM hΩ u y
  let source : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD : PDE.ScalarField d := fun y =>
    ζ τ * η y * spatialDifferenceQuotient k h source (τ, y)
  let aT : Fin d → Fin d → PDE.ScalarField d := fun i j y =>
    ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.ScalarField d := fun i j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.ScalarField d := fun j y =>
    ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.ScalarField d := fun j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.ScalarField d := fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.ScalarField d := fun y =>
    ζ τ * χ y * spatialDifferenceQuotient k h γ (τ, y)
  ((-(∫ y in Ω, sourceD y * V y)) -
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (aT i j y * E j y + aD i j y * U j y) * H i y) -
    (∑ j : Fin d, ∫ y in Ω,
      (driftT j y * E j y + driftD j y * U j y) * V y) +
    (∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y))

private def translatedPrincipal

    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let G : Fin d → PDE.ScalarField d := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.ScalarField d := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.ScalarField d := fun i y => G i y - W i y
  let H : Fin d → PDE.ScalarField d := fun i y => G i y + W i y
  let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y

private theorem commutatorRaw_eq_split

    (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ) :
    commutatorRaw r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u =
      -translatedPrincipal r₀ r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
        localizedSpatialDifferenceQuotientH10NonprincipalRemainder
          r₁ hΩ a b c F η χ k h τ hηshift u := by
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V  := fun y => valueCLM hΩ (A u) y
  let G  := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) y
  let W  := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E  := fun i y => G i y - W i y
  let H  := fun i y => G i y + W i y
  let U  := fun j y =>
    η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y
  let U₀  := fun y => η y * valueCLM hΩ u y
  let source : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => F (r₁ - z.1) z.2
  let sourceD  := fun y =>
    η y * spatialDifferenceQuotient k h source (τ, y)
  let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let aT  := fun i j y =>
    χ y * spatialTranslate k h (α i j) (τ, y)
  let aD  := fun i j y =>
    χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT  := fun j y =>
    χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD  := fun j y =>
    χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT  := fun y => χ y * spatialTranslate k h γ (τ, y)
  let γD  := fun y =>
    χ y * spatialDifferenceQuotient k h γ (τ, y)
  have hsplit := raw_six_term_split (z := ζ τ) sourceD V U₀ aT aD E H U driftT driftD
    γT γD
    (fun i j => (id (integrable_aT_E_H r₀ r₁ hΩ a ha η χ k h τ hχshift hηshift hτ u i j)))
    (fun i j => (id (integrable_aD_U_H r₀ r₁ hΩ a ha η χ k h τ hχshift hηshift hτ u i j)))
    (fun j => (id (integrable_driftT_E_V r₀ r₁ hΩ a b ha hb η χ k h τ hχshift hηshift hτ u j)))
    (fun j => (id (integrable_driftD_U_V r₀ r₁ hΩ a b ha hb η χ k h τ hχshift hηshift hτ u j)))
    ((id (integrable_gammaT_V_V r₀ r₁ hΩ c hc η χ k h τ hχshift hηshift hτ u)))
    ((id (integrable_gammaD_U0_V r₀ r₁ hΩ c hc η χ k h τ hχshift hηshift hτ u)))
  simpa only [commutatorRaw, translatedPrincipal,
    localizedSpatialDifferenceQuotientH10NonprincipalRemainder, A, V, G, W, E, H, U, U₀,
    source, sourceD, α, drift, γ, aT, aD, driftT, driftD, γT, γD, mul_assoc] using hsplit

private def commutatorLhs
      {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift
  ζ τ * (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
    reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))

variable {Kη Kχ : ℝ} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)

private def compactCommutatorOutput
       (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
    ∃ hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
      (u : H10HilbertGraph hΩ),
      let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
        intro y hy; apply subset_tsupport; change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
      let hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
          (tsupport η.toFun) Ω := hχshift.mono_left hηχ
      commutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift u =
        commutatorRaw r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u

private theorem compactCommutatorOutput_of_accepted
       (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    compactCommutatorOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hrest⟩ :=
    exists_smallStep_reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro k h hh
  obtain ⟨hχshift, hfixed⟩ := hrest k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ u
  change commutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ _ u =
    commutatorRaw r₀ r₁ hΩ a b c F ζ η χ k h τ _ u
  simpa only [commutatorLhs, commutatorRaw] using hfixed τ hτ u

private def compactSplitOutput
       (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
    ∃ hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
      (u : H10HilbertGraph hΩ),
      let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
        intro y hy; apply subset_tsupport; change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
      let hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
          (tsupport η.toFun) Ω := hχshift.mono_left hηχ
      commutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift u =
        -translatedPrincipal r₀ r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u

variable (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (F : PDE.TimeScalarField d) (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)

private theorem compactSplitOutput_of_compact
        :
    compactSplitOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hrest⟩ := compactCommutatorOutput_of_accepted
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro k h hh
  obtain ⟨hχshift, hfixed⟩ := hrest k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ u
  exact (hfixed τ hτ u).trans
    (commutatorRaw_eq_split r₀ r₁ hΩ a b c F haSmooth hbSmooth hcSmooth ζ η χ k h τ
      hχshift _ hτ u)

include haSmooth hbSmooth hcSmooth hζunit in
/-- For all sufficiently small signed spatial steps, the exact arbitrary-`H¹₀`
fixed-slice commutator is minus its translated-principal term plus the scalar
time weight times the raw six-term nonprincipal remainder. -/
theorem
    exists_smallStep_h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder
        :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        ∃ hχshift : Set.MapsTo
          (fun y  => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω,
        ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (u : H10HilbertGraph hΩ),
        let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
          intro y hy
          apply subset_tsupport
          change χ y ≠ 0
          rw [χ.eq_one_on_inner y hy]
          exact one_ne_zero
        let hηshift : Set.MapsTo
            (fun y  => y + h • PDE.basisVec k)
            (tsupport η.toFun) Ω :=
          hχshift.mono_left hηχ
        let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let G : Fin d → PDE.ScalarField d := fun i y =>
          PDE.hilbertVectorLpCoord Ω (2 ) i
            (gradientCLM hΩ (A u)) y
        let W : Fin d → PDE.ScalarField d := fun i y =>
          cutoffGradientSpatialDifferenceQuotientL2
            hΩ.measurableSet η i k h (valueCLM hΩ u) y
        let E : Fin d → PDE.ScalarField d := fun i y => G i y - W i y
        let H : Fin d → PDE.ScalarField d := fun i y => G i y + W i y
        let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
          fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
        let Q : ℝ := ζ τ *
            (reverseTimeNegativeSourceRaw
                r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
        let P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
            (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
              E j y * H i y
        let R : ℝ :=
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u
        Q = -P + ζ τ * R := (id (compactSplitOutput_of_compact r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ))

/-- The fixed supplied-collar commutator is minus its translated-principal part
plus the nonprincipal remainder under the uniform majorants. -/
theorem h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder_of_majorants

    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (δ : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialMatrixFDerivFrobeniusNorm
        (fun w  => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
    (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
    (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialVectorFDerivFrobeniusNorm
        (fun w  => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
    (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
    (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w  => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
    (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w  => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M)
    (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ) :
    let hχshift : Set.MapsTo
        (fun y  => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω :=
      mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
    let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
      intro y hy
      apply subset_tsupport
      change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]
      exact one_ne_zero
    let hηshift : Set.MapsTo
        (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω :=
      hχshift.mono_left hηχ
    let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
    let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h η.tsupport_subset hηshift
    let G : Fin d → PDE.ScalarField d := fun i y =>
      PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) y
    let W : Fin d → PDE.ScalarField d := fun i y =>
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
    let E : Fin d → PDE.ScalarField d := fun i y => G i y - W i y
    let H : Fin d → PDE.ScalarField d := fun i y => G i y + W i y
    let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    let Q : ℝ := ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
    let P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y
    let R : ℝ := localizedSpatialDifferenceQuotientH10NonprincipalRemainder
      r₁ hΩ a b c F η χ k h τ hηshift u
    Q = -P + ζ τ * R := by
  let hχshift  :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift  :=
    hχshift.mono_left hηχ
  have hcomm :=
    reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit δ M hM hcarrier a b c F haSmooth
      hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD k h hh τ hτ u
  have hsplit := commutatorRaw_eq_split r₀ r₁ hΩ a b c F haSmooth hbSmooth hcSmooth ζ η χ
    k h τ hχshift hηshift hτ u
  simpa only [hχshift, hηχ, hηshift, localizedSpatialDifferenceQuotientH10NonprincipalRemainder, translatedPrincipal] using
    hcomm.trans hsplit

end HypoellipticAleksandrov.Parabolic.Dirichlet
