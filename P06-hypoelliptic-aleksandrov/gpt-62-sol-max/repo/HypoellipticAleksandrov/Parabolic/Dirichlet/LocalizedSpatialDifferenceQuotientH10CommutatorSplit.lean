module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder

/-!
# Exact H10 commutator split
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem integrable_weighted_pair {q f g : PDE.Vec d → ℝ}
    (hq : Continuous q ∧ HasCompactSupport q) (hf : MemLp f 2 (PDE.volumeOn Ω))
    (hg : MemLp g 2 (PDE.volumeOn Ω)) : Integrable (fun y => q y * f y * g y) (PDE.volumeOn Ω) := by
  have hq' : MemLp q ∞ (volume : Measure (PDE.Vec d)) := hq.1.memLp_of_hasCompactSupport hq.2
  change Integrable (q * f * g) _
  simpa only [mul_assoc] using (hf.integrable_mul hg).mul_of_top_right (hq'.restrict Ω)

private theorem integral_pair_mul_const (z : ℝ)
    (q₁ p₁ q₂ p₂ g : PDE.Vec d → ℝ)
    (h₁ : Integrable (fun y => (q₁ y * p₁ y) * g y) (PDE.volumeOn Ω))
    (h₂ : Integrable (fun y => (q₂ y * p₂ y) * g y) (PDE.volumeOn Ω)) :
    (∫ y in Ω, ((z * q₁ y) * p₁ y + (z * q₂ y) * p₂ y) * g y ∂volume) =
      z * ((∫ y in Ω, (q₁ y * p₁ y) * g y ∂volume) +
        ∫ y in Ω, (q₂ y * p₂ y) * g y ∂volume) := by
  rw [show (fun y => ((z * q₁ y) * p₁ y + (z * q₂ y) * p₂ y) * g y) =
      fun y => z * (q₁ y * p₁ y * g y) + z * (q₂ y * p₂ y * g y) by funext y; ring]
  rw [integral_add (h₁.const_mul z) (h₂.const_mul z), integral_const_mul, integral_const_mul, mul_add]

private theorem raw_six_term_split (z : ℝ)
    (source V U₀ : PDE.Vec d → ℝ)
    (aT aD : Fin d → Fin d → PDE.Vec d → ℝ)
    (E H U driftT driftD : Fin d → PDE.Vec d → ℝ)
    (gammaT gammaD : PDE.Vec d → ℝ)
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
    -(∫ y in Ω, (z * source y) * V y ∂volume) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y ∂volume) -
        (∑ j : Fin d, ∫ y in Ω,
          ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y ∂volume) +
        ∫ y in Ω, ((z * gammaT y) * V y + (z * gammaD y) * U₀ y) * V y ∂volume =
      -(∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y ∂volume) +
        z *
          (-(∫ y in Ω, source y * V y ∂volume) -
              (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
                (aD i j y * U j y) * H i y ∂volume) -
              (∑ j : Fin d, ∫ y in Ω,
                (driftT j y * E j y) * V y ∂volume) -
              (∑ j : Fin d, ∫ y in Ω,
                (driftD j y * U j y) * V y ∂volume) +
              (∫ y in Ω, (gammaT y * V y) * V y ∂volume) +
              ∫ y in Ω, (gammaD y * U₀ y) * V y ∂volume) := by
  have hp (i j : Fin d) := integral_pair_mul_const z (aT i j) (E j) (aD i j) (U j) (H i) (haT i j) (haD i j)
  have hd (j : Fin d) := integral_pair_mul_const z (driftT j) (E j) (driftD j) (U j) V (hdt j) (hdd j)
  simp_rw [hp, hd, integral_pair_mul_const z gammaT V gammaD U₀ V hgt hgd]
  simp_rw [mul_assoc, integral_const_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

end

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}

/-- The translated principal term in the fixed-time commutator. -/
def h10TranslatedPrincipal
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (w : ℝ)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (w * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y ∂volume

private theorem commutatorRaw_eq_split
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : χ.ShiftMapsInto k h Ω)
    (hηshift : η.ShiftMapsInto k h Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ) :
    h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u =
      -h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift u + ζ τ *
        localizedSpatialDifferenceQuotientH10NonprincipalRemainder
          r₁ hΩ a b c F η χ k h τ hηshift u := by
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y =>
    η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y
  let U₀ : PDE.Vec d → ℝ := fun y => η y * valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let sourceD : PDE.Vec d → ℝ := fun y =>
    η y * spatialDifferenceQuotient k h source (τ, y)
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ :=
    fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let aT : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.Vec d → ℝ := fun j y =>
    χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.Vec d → ℝ := fun j y =>
    χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.Vec d → ℝ := fun y => χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.Vec d → ℝ := fun y =>
    χ y * spatialDifferenceQuotient k h γ (τ, y)
  let J j := PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)
  let G' i := PDE.hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ (A u))
  let W' i := cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u)
  have hV : MemLp V 2 (PDE.volumeOn Ω) := Lp.memLp (valueCLM hΩ (A u))
  have hE (i : Fin d) : MemLp (E i) 2 (PDE.volumeOn Ω) :=
    (Lp.memLp (G' i - W' i)).ae_eq (Lp.coeFn_sub _ _)
  have hH (i : Fin d) : MemLp (H i) 2 (PDE.volumeOn Ω) :=
    (Lp.memLp (G' i + W' i)).ae_eq (Lp.coeFn_add _ _)
  have hη : MemLp η.toFun ∞ (PDE.volumeOn Ω) :=
    (η.smooth.continuous.memLp_of_hasCompactSupport (μ := volume) η.hasCompactSupport).restrict Ω
  have hU (i : Fin d) : MemLp (U i) 2 (PDE.volumeOn Ω) := hη.mul (Lp.memLp (J i))
  have hU₀ : MemLp U₀ 2 (PDE.volumeOn Ω) := hη.mul (Lp.memLp (valueCLM hΩ u))
  have coeff {f : TimeVelocity d → ℝ}
      (hf : IsSmoothOnNeighborhood f (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
      (Continuous (fun y => χ y * spatialTranslate k h (fun z => f (r₁ - z.1, z.2)) (τ, y)) ∧
        HasCompactSupport (fun y => χ y * spatialTranslate k h (fun z => f (r₁ - z.1, z.2)) (τ, y))) ∧
      (Continuous (fun y => χ y * spatialDifferenceQuotient k h (fun z => f (r₁ - z.1, z.2)) (τ, y)) ∧
        HasCompactSupport (fun y => χ y * spatialDifferenceQuotient k h (fun z => f (r₁ - z.1, z.2)) (τ, y))) := by
    simpa only [one_mul] using cutoffSlice_translate_quotient χ k h 1
      (IsSmoothOnNeighborhood.reverseTimeClosedCylinder hf) hτ hχshift
  have hA (i j : Fin d) := coeff (IsSmoothOnNeighborhood.coefficientEntry a ha i j)
  have hB (j : Fin d) := coeff (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)
  have hC := coeff hc
  have hsplit := raw_six_term_split (ζ τ) sourceD V U₀ aT aD E H U driftT driftD γT γD
    (fun i j => integrable_weighted_pair (hA i j).1 (hE j) (hH i))
    (fun i j => integrable_weighted_pair (hA i j).2 (hU j) (hH i))
    (fun j => integrable_weighted_pair (hB j).1 (hE j) hV)
    (fun j => integrable_weighted_pair (hB j).2 (hU j) hV)
    (integrable_weighted_pair hC.1 hV hV) (integrable_weighted_pair hC.2 hU₀ hV)
  simpa only [h10CommutatorRawRhs, h10CommutatorRawLeaf, h10TranslatedPrincipal,
    localizedSpatialDifferenceQuotientH10NonprincipalRemainder, A, V, G, W, E, H, U, U₀,
    source, sourceD, α, drift, γ, aT, aD, driftT, driftD, γT, γD, mul_assoc] using hsplit

/-- The localized commutator is minus the translated principal term plus the remainder. -/
theorem h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hF : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ) (hτ : τ ∈ Icc 0 (r₁ - r₀))
    (hχshift : χ.ShiftMapsInto k h Ω) (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ) :
    h10CommutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η k h τ hηshift u =
      -h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift u +
        ζ τ * localizedSpatialDifferenceQuotientH10NonprincipalRemainder r₁ hΩ a b c F η χ k h τ hηshift u :=
  (reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F ha hb hc hF ζ η χ k h τ hτ hχshift hηshift u).trans
    (commutatorRaw_eq_split r₀ r₁ hΩ a b c F ha hb hc ζ η χ k h τ hχshift hηshift hτ u)

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
