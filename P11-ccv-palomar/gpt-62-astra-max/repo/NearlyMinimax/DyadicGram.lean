module

public import NearlyMinimax.AffineCells
public import NearlyMinimax.PopulationMomentDerivatives

@[expose] public section

/-! Original-law dyadic Grams and their exact normalized whitening charts. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax

def dyadicNormalizedAnchor {d : ℕ} (j : ℕ) (x : Covariate d) : Covariate d :=
  gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x

def dyadicCellAffine {d : ℕ} (j : ℕ) (x w : Covariate d) : Covariate d :=
  gridAffine ((2 : ℕ) ^ j) (regularGridCell _ (by positivity) x) w

def dyadicNormalizedDensity {d : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ := θ.density ∘ dyadicCellAffine j x

def dyadicKnownGram {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂cubeVolume d

def dyadicPopulationGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ

def dyadicPreconditionedGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (dyadicKnownGram j x)⁻¹ * dyadicPopulationGram θ j x

theorem admissible_designLaw_setIntegral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (s : Set (Covariate d)) (hs : MeasurableSet s) (f : Covariate d → ℝ) :
    (∫ z in s, f z ∂designLaw θ) = ∫ z in s, θ.density z * f z ∂cubeVolume d := by
  unfold designLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hθ.1.ennreal_ofReal.aemeasurable) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hθ.2.2.1] with z hz
  rw [ENNReal.toReal_ofReal (C.densityLower_pos.le.trans hz.1)]
  rfl

theorem dyadicKnownGram_eq_normalized {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicKnownGram (ℓ := ℓ) j x = anchoredGram (dyadicNormalizedAnchor j x) := by
  ext γ δ
  have h := regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicKnownGram, dyadicPilotScale,
    dyadicPilotCell, Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine,
    anchoredGram, dyadicNormalizedAnchor] using h

theorem dyadicPopulationGram_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicPopulationGram (ℓ := ℓ) θ j x =
      anchoredDensityGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  ext γ δ
  change dyadicPilotScale d j * (∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ) = _
  rw [admissible_designLaw_setIntegral C θ hθ _ (dyadicPilotCell_measurable j x)]
  have h := regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => θ.density z * (dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ))
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicPilotScale, dyadicPilotCell,
    Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine, anchoredDensityGram,
    dyadicNormalizedAnchor, dyadicNormalizedDensity, Function.comp_apply, dyadicCellAffine] using h

theorem dyadicNormalizedDensity_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    Measurable (dyadicNormalizedDensity θ j x) :=
  hθ.1.comp (gridAffineEquiv _ (by positivity) _).measurable

theorem dyadicNormalizedDensity_bounds {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper :=
  gridAffine_ae_pullback _ (by positivity) _ hθ.2.2.1

theorem dyadicKnownGram_posDef {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (dyadicKnownGram (ℓ := ℓ) j x).PosDef := by
  rw [dyadicKnownGram_eq_normalized]
  exact anchoredGram_posDef _

end NearlyMinimax
