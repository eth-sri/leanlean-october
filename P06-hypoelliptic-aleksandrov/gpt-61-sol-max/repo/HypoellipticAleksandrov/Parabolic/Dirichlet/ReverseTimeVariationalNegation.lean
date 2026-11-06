module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
import Aesop



/-!
# Negation of reverse-time variational energy solutions

This file records the literal algebraic stability of the selected weak time
derivative, canonical Hilbert representative, and variational solution under
negation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModuleNegation
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

/-- Smoothness on a neighborhood is preserved by pointwise negation. -/
protected theorem IsSmoothOnNeighborhood.neg
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {f : E → G} (hf : IsSmoothOnNeighborhood f K) :
    IsSmoothOnNeighborhood (-f) K := by
  rcases hf with ⟨V, hVopen, hKV, hfV⟩
  exact ⟨V, hVopen, hKV, hfV.neg⟩

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

/-- The selected canonical representative commutes with literal negation. -/
theorem reverseTimeHilbertRepresentative_neg_eq

    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    reverseTimeHilbertRepresentative hΩ T hT
        _ _ (hdu.smul (-1)) =
      -reverseTimeHilbertRepresentative hΩ T hT u g hdu := by
  obtain ⟨hU, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu
  obtain ⟨hN, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT
    _ _ (hdu.smul (-1))
  apply ReverseTimeHilbertRepresentativeAgrees.unique hN hT
  filter_upwards [hU, Lp.coeFn_smul (-1 : ℝ) u] with τ hUτ hneg
  intro hτ
  let hτcc : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  change (-reverseTimeHilbertRepresentative hΩ T hT u g hdu) ⟨τ, hτcc⟩ =
    valueCLM hΩ (((-1 : ℝ) • u) τ)
  change -reverseTimeHilbertRepresentative hΩ T hT u g hdu ⟨τ, hτcc⟩ =
    valueCLM hΩ (((-1 : ℝ) • u) τ)
  rw [hUτ hτ, hneg]
  change -(valueCLM hΩ (u τ)) = valueCLM hΩ ((-1 : ℝ) • u τ)
  rw [(valueCLM hΩ).map_smul, neg_one_smul]

private theorem reverseTimeSourceSlice_neg_eq

    (r₁ τ : ℝ) (F : PDE.TimeScalarField d)
    (hF : MemLp ((F (r₁ - τ)))
      (2 ) (PDE.volumeOn Ω))
    (hnegF : MemLp (fun y  => -F (r₁ - τ) y)
      (2 ) (PDE.volumeOn Ω)) :
    reverseTimeSourceSlice r₁ τ (fun r y => -F r y) hnegF =
      (-1 : ℝ) • reverseTimeSourceSlice r₁ τ F hF := by
  aesop

variable (q : PDE.ScalarField d)

private theorem integral_hilbertVectorLpCoord_neg

    (i : Fin d) (U : PDE.HilbertVectorLp Ω (2 ))
    (w : PDE.ScalarLp Ω (2 )) :
    (∫ y in Ω, q y * (PDE.hilbertVectorLpCoord Ω (2 ) i (-U)) y * w y) =
      -∫ y in Ω, q y * (PDE.hilbertVectorLpCoord Ω (2 ) i U) y * w y := by
  rw [(PDE.hilbertVectorLpCoord Ω (2 ) i).map_neg]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg (PDE.hilbertVectorLpCoord Ω (2 ) i U)] with y hy
  rw [hy]
  rw [Pi.neg_apply]
  ring

private theorem integral_scalarLp_neg

    (U w : PDE.ScalarLp Ω (2 )) :
    (∫ y in Ω, q y * (-U) y * w y) = -∫ y in Ω, q y * U y * w y := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg U] with y hy
  rw [hy]
  rw [Pi.neg_apply]
  ring

variable (hΩ : IsOpen Ω)

variable (q : PDE.ScalarField d)

private theorem integral_gradientCLM_neg

    (i : Fin d) (u : H10HilbertGraph hΩ) (w : PDE.ScalarLp Ω (2 )) :
    (∫ y in Ω, q y *
      (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (-u))) y * w y) =
      -∫ y in Ω, q y *
        (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ u)) y * w y := by
  solve_by_elim (maxDepth := 4) [gradientCLM, integral_hilbertVectorLpCoord_neg]

private theorem integral_valueCLM_neg

    (u : H10HilbertGraph hΩ) (w : PDE.ScalarLp Ω (2 )) :
    (∫ y in Ω, q y * (valueCLM hΩ (-u)) y * w y) =
      -∫ y in Ω, q y * (valueCLM hΩ u) y * w y := by
  solve_by_elim (maxDepth := 4) [valueCLM, integral_scalarLp_neg]

variable (r₁ τ : ℝ) (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)

private theorem reverseTimeSpatialForm_neg_left


    (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c (-u) v =
      -reverseTimeSpatialForm hΩ r₁ τ a b c u v := by
  rw [reverseTimeSpatialForm_apply]
  rw [reverseTimeSpatialForm_apply]
  simp_rw [integral_gradientCLM_neg, integral_valueCLM_neg]
  simp only [Finset.sum_neg_distrib]
  ring

private theorem reverseTimeVariationalEquation_neg


    (q : H10HilbertGraph hΩ →L[ℝ] ℝ)
    (s sneg : PDE.ScalarLp Ω (2 ))
    (u v : H10HilbertGraph hΩ)
    (hs : sneg = (-1 : ℝ) • s)
    (heq : q v + reverseTimeSpatialForm hΩ r₁ τ a b c u v =
      reverseTimeSourceFunctional hΩ s v) :
    (-q) v + reverseTimeSpatialForm hΩ r₁ τ a b c (-u) v =
      reverseTimeSourceFunctional hΩ sneg v := by
  calc
    (-q) v + reverseTimeSpatialForm hΩ r₁ τ a b c (-u) v =
        -(q v + reverseTimeSpatialForm hΩ r₁ τ a b c u v) := by
      rw [ContinuousLinearMap.neg_apply, reverseTimeSpatialForm_neg_left]
      ring
    _ = -reverseTimeSourceFunctional hΩ s v := congrArg Neg.neg heq
    _ = reverseTimeSourceFunctional hΩ sneg v := by
      rw [hs, reverseTimeSourceFunctional_apply, reverseTimeSourceFunctional_apply]
      rw [inner_smul_right]
      ring

/-- Literal negation preserves the selected reverse-time variational energy solution. -/
theorem IsReverseTimeVariationalEnergySolution.neg

    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 ))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c (fun r y => -F r y) (IsSmoothOnNeighborhood.neg hFSmooth) (-initial)
      ((-1 : ℝ) • u) ((-1 : ℝ) • g) (hdu.smul (-1)) := by
  constructor
  · have hrep := reverseTimeHilbertRepresentative_neg_eq hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g hdu
    have htrace := congrArg
      (fun Q : C(Set.Icc 0 (r₁ - r₀), PDE.ScalarLp Ω (2 )) =>
        Q ⟨0, ⟨le_rfl, (sub_pos.mpr h₀₁).le⟩⟩) hrep

    exact (show reverseTimeInitialTrace hΩ (r₁ - r₀) _
        _ _ (hdu.smul (-1)) =
        -reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu by
        assumption).trans (congrArg Neg.neg hu.1)
  · filter_upwards [hu.2, Lp.coeFn_smul (-1 : ℝ) u,
      Lp.coeFn_smul (-1 : ℝ) g] with τ heq hnegU hnegG
    intro hτ v
    let hF := reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded F hFSmooth τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    let hnegF := reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded (fun r y => -F r y) (IsSmoothOnNeighborhood.neg hFSmooth) τ
        ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩

    have hnegU' : (((-1 : ℝ) • u) τ) = -(u τ) := by
      rw [hnegU]
      simp only [Pi.smul_apply, neg_one_smul]
    have hnegG' : (((-1 : ℝ) • g) τ) = -(g τ) := by
      rw [hnegG]
      simp only [Pi.smul_apply, neg_one_smul]
    rw [hnegU', hnegG']
    exact reverseTimeVariationalEquation_neg hΩ r₁ τ a b c (g τ)
      (reverseTimeSourceSlice r₁ τ F hF)
      (reverseTimeSourceSlice r₁ τ (fun r y => -F r y) hnegF)
      (u τ) v (reverseTimeSourceSlice_neg_eq r₁ τ F hF hnegF) (heq hτ v)

end HypoellipticAleksandrov.Parabolic.Dirichlet
