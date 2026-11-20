module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CommutatorSplit
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientTranslatedPrincipalCoercivity

/-!
# Fixed-slice H10 coercive commutator consequence
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ T : ℝ} (r₁ : ℝ) (hΩ : IsOpen Ω)
  (a : CoefficientField d) (ζ : ReverseTimeScalarTest T)
  (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
  (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (k : Fin d) (h τ : ℝ)
  (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ)
include d Ω inner Kη Kχ T r₁ hΩ a ζ η χ k h τ hηshift u

private def canonicalTranslatedPrincipalValue : ℝ :=
    let Ev : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      localizedSpatialDifferenceQuotientPrincipalFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let Hv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      localizedSpatialDifferenceQuotientCompanionFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let α : Fin d → Fin d → TimeVelocity d → ℝ :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y ∂volume

end

private theorem raw_translatedPrincipal_eq_canonical_ev_hv
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ T : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ζ : ReverseTimeScalarTest T)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ) :
    h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift u =
      canonicalTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u := by
  unfold h10TranslatedPrincipal canonicalTranslatedPrincipalValue
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  apply integral_congr_ae
  have hE := hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM
    hΩ η j k h η.tsupport_subset hηshift u
  have hH := hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM
    hΩ η i k h η.tsupport_subset hηshift u
  simp only [hE, hH]
  let G l := PDE.hilbertVectorLpCoord Ω 2 l (gradientCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u))
  let W l := cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η l k h (valueCLM hΩ u)
  filter_upwards [Lp.coeFn_sub (G j) (W j), Lp.coeFn_add (G i) (W i)] with y hy hz
  dsimp only [G, W] at hy hz
  simp only [hy, hz, Pi.sub_apply, Pi.add_apply]

private theorem translated_principal_raw_lower
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ lam Lam : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h : ℝ)
    (hχshift : χ.ShiftMapsInto k h Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (hζnonneg : 0 ≤ ζ τ)
    (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ) :
    ζ τ * (lam * ‖gradientCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 -
      Lam * ‖cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u‖ ^ 2) ≤
      h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift u := by
  have hcanonical :=
    localizedSpatialDifferenceQuotient_translatedPrincipal_lower_of_loewner
      r₀ r₁ lam Lam hΩ a haSmooth hLower hUpper ζ η χ k h hχshift τ hτ hζnonneg u
  have hbridge := raw_translatedPrincipal_eq_canonical_ev_hv
    r₁ hΩ a ζ η χ k h τ hηshift u
  change _ ≤ canonicalTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u at hcanonical
  exact hcanonical.trans_eq hbridge.symm

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
  (hΩbounded : Bornology.IsBounded Ω)
include h₀₁ hΩbounded

section
variable (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
include a b c

private def coerciveFixedSlice
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : χ.ShiftMapsInto k h Ω) (τ : ℝ) (u : H10HilbertGraph hΩ) : Prop :=
  let hηχ := χ.inner_subset_tsupport
  let hηshift : η.ShiftMapsInto k h Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
  let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  let Q : ℝ := ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
  Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
    ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2))

private theorem coerciveFixedSlice_of_adapterFacts
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hF : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (k : Fin d) (h : ℝ)
    (hχshift : χ.ShiftMapsInto k h Ω) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hζnonneg : 0 ≤ ζ τ)
    (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ)
    (hsplit : ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) =
        -h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u)
    (hrem : |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
      r₁ hΩ a b c F η χ k h τ hηshift u| ≤
        ε * ‖gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) :
    coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
      k h hχshift τ u := by
  let hηχ := χ.inner_subset_tsupport
  let hηshift' : η.ShiftMapsInto k h Ω := hχshift.mono_left hηχ
  have hshift : hηshift = hηshift' := Subsingleton.elim _ _
  subst hηshift
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift'
  let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift'
  let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
  let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  let Q : ℝ := ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
  let z : ℝ := ζ τ
  let X : ℝ := lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2
  let Y : ℝ := ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)
  let R : ℝ := localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift' u
  let Praw : ℝ := h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift' u
  change Q = -Praw + z * R at hsplit
  have hprincipalRaw := translated_principal_raw_lower
    r₀ r₁ lam Lam hΩ a ha hLower hUpper ζ η χ k h hχshift τ hτ hζnonneg hηshift' u
  change z * X ≤ Praw at hprincipalRaw
  change |R| ≤ Y at hrem
  change coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
    k h hχshift τ u
  dsimp only [coerciveFixedSlice]
  have hRle : R ≤ Y := (le_abs_self R).trans hrem
  have hzR : z * R ≤ z * Y := mul_le_mul_of_nonneg_left hRle hζnonneg
  calc
    Q + z * X = (-Praw + z * R) + z * X := by rw [hsplit]
    _ = z * R + (z * X - Praw) := by ring
    _ ≤ z * R + 0 := by
      simpa only [add_comm] using
        add_le_add_left (sub_nonpos.mpr hprincipalRaw) (z * R)
    _ = z * R := by ring
    _ ≤ z * Y := hzR

end

/-- The full fixed-slice coercive term is bounded by a nonprincipal Young
remainder, with its constant uniform in the reverse-time scalar test. -/
theorem exists_uniform_timeTest_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (δ : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧
      ∀ (ζ : ReverseTimeScalarTest (r₁ - r₀))
        (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1),
      ∀ (lam Lam : ℝ) (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ),
        ∀ (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
          (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
          (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
          (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
          (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hbound : ReverseTimeCoefficientMajorant r₀ r₁ (tsupport χ.toFun) δ M a b c F),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
          (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
          let hχshift : χ.ShiftMapsInto k h Ω :=
            mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
              hcarrier k hh
          let hηχ := χ.inner_subset_tsupport
          let hηshift : η.ShiftMapsInto k h Ω :=
            hχshift.mono_left hηχ
          let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientEnergyTestH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            gradientCLM hΩ (A u)
          let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
          let Q : ℝ := ζ τ *
            (reverseTimeNegativeSourceRaw
                r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
          Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
            ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) := by
  obtain ⟨Cε, hCε, hrem⟩ :=
    exists_uniform_nonprincipalRemainder_bound_of_majorants
      r₀ r₁ hΩ η χ δ M hM hcarrier ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro ζ hζunit lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hbound k h hh τ hτ hζnonneg u
  let hχshift : χ.ShiftMapsInto k h Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ := χ.inner_subset_tsupport
  let hηshift : η.ShiftMapsInto k h Ω :=
    hχshift.mono_left hηχ
  have hsplit :=
    h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
      ζ η χ k h τ hτ hχshift hηshift u
  have hsplitRaw : ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) =
        -h10TranslatedPrincipal r₁ hΩ a (ζ τ) η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u := by
    exact hsplit
  have hremBound :=
    hrem a b c F haSmooth hbSmooth hcSmooth hFSmooth hbound
      k h hh τ hτ u
  change |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift u| ≤
      ε * ‖gradientCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2) at hremBound
  change coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ ε Cε lam Lam
    k h hχshift τ u
  exact coerciveFixedSlice_of_adapterFacts
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hFSmooth ζ η χ ε Cε lam Lam hLower hUpper
      k h hχshift τ hτ hζnonneg hηshift u hsplitRaw hremBound

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
