module

public import NearlyMinimax.AffineCells
public import NearlyMinimax.PopulationMomentDerivatives

@[expose] public section

/-! Original-law dyadic Grams and their exact normalized whitening charts. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x w : Covariate d)

def dyadicNormalizedAnchor : Covariate d :=
  gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x

def dyadicCellAffine : Covariate d :=
  gridAffine (k := ((2 : ℕ) ^ j)) (regularGridCell _ (by positivity) x) w

def dyadicNormalizedDensity : Covariate d → ℝ := θ.density ∘ dyadicCellAffine j x

def dyadicKnownGram :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂cubeVolume d

def dyadicPopulationGram :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ

def dyadicPreconditionedGram : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (dyadicKnownGram j x)⁻¹ * dyadicPopulationGram θ j x

end

variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d)

include hθ in
theorem admissible_designLaw_setIntegral
    {s : Set (Covariate d)} (hs : MeasurableSet s) (f : Covariate d → ℝ) :
    (∫ z in s, f z ∂designLaw θ) = ∫ z in s, θ.density z * f z ∂cubeVolume d := by
  unfold designLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hθ.1.ennreal_ofReal.aemeasurable) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hθ.2.2.1] with z hz
  rw [ENNReal.toReal_ofReal (C.densityLower_pos.le.trans hz.1)]
  rfl

theorem dyadic_cell_integral (f : Covariate d → ℝ) :
    dyadicPilotScale d j * (∫ z in dyadicPilotCell j x, f z ∂cubeVolume d) =
      ∫ w, f (dyadicCellAffine j x w) ∂cubeVolume d := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicPilotScale, dyadicPilotCell, Set.preimage, Set.mem_singleton_iff, dyadicCellAffine] using
    regular_grid_cell_integral (k := 2^j) (by positivity) (regularGridCell _ (by positivity) x) f

include hθ in
theorem dyadic_design_integral (f : Covariate d → ℝ) :
    dyadicPilotScale d j * (∫ z in dyadicPilotCell j x, f z ∂designLaw θ) =
      ∫ w, dyadicNormalizedDensity θ j x w * f (dyadicCellAffine j x w) ∂cubeVolume d := by
  rw [admissible_designLaw_setIntegral hθ (dyadicPilotCell_measurable j x)]
  exact dyadic_cell_integral j x _

theorem dyadicKnownGram_eq_normalized :
    dyadicKnownGram (ℓ := ℓ) j x = anchoredGram (dyadicNormalizedAnchor j x) := by
  ext γ δ
  simp only [dyadicKnownGram, dyadic_cell_integral, dyadicCellAffine, dyadicAnchoredFeature_affine]
  rfl

include hθ in
theorem dyadicPopulationGram_eq_normalized :
    dyadicPopulationGram (ℓ := ℓ) θ j x =
      anchoredDensityGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  ext γ δ
  simp only [dyadicPopulationGram, dyadic_design_integral hθ, dyadicCellAffine, dyadicAnchoredFeature_affine]
  rfl

include hθ in
theorem dyadicNormalizedDensity_measurable :
    Measurable (dyadicNormalizedDensity θ j x) :=
  hθ.1.comp (gridAffineEquiv _ (by positivity) _).measurable

include hθ in
theorem dyadicNormalizedDensity_bounds :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper :=
  gridAffine_ae_pullback _ (by positivity) _ hθ.2.2.1

theorem dyadicKnownGram_posDef :
    (dyadicKnownGram (ℓ := ℓ) j x).PosDef := by
  rw [dyadicKnownGram_eq_normalized]
  exact anchoredGram_posDef _

end NearlyMinimax
