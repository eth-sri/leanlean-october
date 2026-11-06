module

public import NearlyMinimax.AffineCells
public import NearlyMinimax.PopulationMomentDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Original-law dyadic Grams and their exact normalized whitening charts. -/

𝛍
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
𝚨

𝗇 𝔈 𝗟 ^ j
def dyadicNormalizedAnchor (j : ℕ) (x : Covariate d) : Covariate d :=
  gridNormalizedAnchor 𝔈  𝖠₃  x

def dyadicCellAffine (j : ℕ) (x w : Covariate d) : Covariate d :=
  gridAffine 𝔈 (regularGridCell _  𝖠₃  x) w

def dyadicNormalizedDensity (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : 𝙀 := θ.density ∘ dyadicCellAffine j x

𝗇 𝔄 𝘧₁ γ * 𝘧₁ δ
𝗇 𝔐 𝗎
𝗇 𝔅 Matrix 𝔐 𝔐 ℝ
def dyadicKnownGram (j : ℕ) (x : Covariate d) :
    𝔅 := fun γ δ =>
  𝘟 * ∫ z in dyadicPilotCell j x,
    𝔄 ∂cubeVolume d

𝗇 𝔉 ∫ z in dyadicPilotCell j x, 𝔄 ∂designLaw θ
def dyadicPopulationGram (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    𝔅 := fun γ δ =>
  𝘟 * 𝔉

def dyadicPreconditionedGram (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : 𝔅 :=
  𝗵₁ * dyadicPopulationGram θ j x

𝗇 𝔍 𝙟
theorem admissible_designLaw_setIntegral C
    θ (hθ : 𝔍)
    s (hs : MeasurableSet s) (f : 𝙀) :
     ∫ z in s, f z ∂designLaw θ = ∫ z in s, θ.density z * f z ∂cubeVolume d := by
  unfold designLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hθ.1.ennreal_ofReal.aemeasurable (Filter.Eventually.of_forall 𝘕) f hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hθ.2.2.1] with z hz
  rw [ENNReal.toReal_ofReal $ C.densityLower_pos.le.trans hz.1 ]
  rfl

𝗇 𝔊 dyadicKnownGram (ℓ := ℓ) j x
𝗇 𝔎 𝘎₂
𝗇 𝔏 𝘷
theorem dyadicKnownGram_eq_normalized j (x : Covariate d) :
    𝔊 = anchoredGram 𝔎 := by
  ext γ δ
  have h := regular_grid_cell_integral 𝔏  𝖠₃ 
    (regularGridCell _  𝖠₃  x)
     fun z => 𝔄
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicKnownGram, dyadicPilotScale,
    dyadicPilotCell, Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine,
    anchoredGram, dyadicNormalizedAnchor] using h

𝗇 𝔇 dyadicNormalizedDensity θ j x
theorem dyadicPopulationGram_eq_normalized C
    θ (hθ : 𝔍) j (x : Covariate d) :
    dyadicPopulationGram (ℓ := ℓ) θ j x =
      anchoredDensityGram 𝔎 𝔇 := by
  ext γ δ
  change 𝘟 * 𝔉 = _
  rw [admissible_designLaw_setIntegral C θ hθ _ $ dyadicPilotCell_measurable j x ]
  have h := regular_grid_cell_integral 𝔏  𝖠₃ 
    (regularGridCell _  𝖠₃  x)
     fun z => θ.density z * 𝔄
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicPilotScale, dyadicPilotCell,
    Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine, anchoredDensityGram,
    dyadicNormalizedAnchor, dyadicNormalizedDensity, Function.comp_apply, dyadicCellAffine] using h

theorem dyadicNormalizedDensity_measurable C
    θ (hθ : 𝔍) j (x : Covariate d) :
    Measurable 𝔇 :=
  hθ.1.comp (gridAffineEquiv _  𝖠₃  _).measurable

theorem dyadicNormalizedDensity_bounds C
    θ (hθ : 𝔍) j x :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ 𝔇 w ∧
      𝔇 w ≤ C.densityUpper :=
  gridAffine_ae_pullback _  𝖠₃  _ hθ.2.2.1

theorem dyadicKnownGram_posDef j (x : Covariate d) :
    (𝔊).PosDef := by
  rw [dyadicKnownGram_eq_normalized]
  exact anchoredGram_posDef _
