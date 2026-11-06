module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CommutatorSplit
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientTranslatedPrincipalCoercivity
import Batteries.Tactic.Alias
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith



/-!
# Fixed-slice H10 coercive commutator consequence
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

variable {Ω inner : PDE.VelocityRegion d} {Kη Kχ T : ℝ} (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d) (ζ : ReverseTimeScalarTest T) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (k : Fin d) (h τ : ℝ) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ)

private def rawTranslatedPrincipalValue
      : ℝ :=
    let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift
    let Gv : PDE.HilbertVectorLp Ω (2 ) := gradientCLM hΩ (A u)
    let G : Fin d → PDE.ScalarField d := fun i y =>
      PDE.hilbertVectorLpCoord Ω (2 ) i Gv y
    let W : Fin d → PDE.ScalarField d := fun i y =>
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u) y
    let E : Fin d → PDE.ScalarField d := fun i y => G i y - W i y
    let H : Fin d → PDE.ScalarField d := fun i y => G i y + W i y
    let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y

private def canonicalTranslatedPrincipalValue
      : ℝ :=
    let Ev : PDE.HilbertVectorLp Ω (2 ) :=
      localizedSpatialDifferenceQuotientPrincipalFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let Hv : PDE.HilbertVectorLp Ω (2 ) :=
      localizedSpatialDifferenceQuotientCompanionFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        PDE.hilbertVectorLpCoord Ω (2 ) j Ev y *
        PDE.hilbertVectorLpCoord Ω (2 ) i Hv y

private theorem integral_eq_of_coord_sub_add
     {Ω : PDE.VelocityRegion d} {T : ℝ}
    (ζ : ReverseTimeScalarTest T) (χ : PDE.ScalarField d)
    (k : Fin d) (h τ : ℝ)
    (α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (Gv : PDE.HilbertVectorLp Ω (2 ))
    (Wl : Fin d → PDE.ScalarLp Ω (2 ))
    (Ev Hv : PDE.HilbertVectorLp Ω (2 ))
    (hEeq : ∀ j : Fin d, PDE.hilbertVectorLpCoord Ω (2 ) j Ev =
      PDE.hilbertVectorLpCoord Ω (2 ) j Gv - Wl j)
    (hHeq : ∀ i : Fin d, PDE.hilbertVectorLpCoord Ω (2 ) i Hv =
      PDE.hilbertVectorLpCoord Ω (2 ) i Gv + Wl i) :
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        (PDE.hilbertVectorLpCoord Ω (2 ) j Gv y - Wl j y) *
        (PDE.hilbertVectorLpCoord Ω (2 ) i Gv y + Wl i y)) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
          PDE.hilbertVectorLpCoord Ω (2 ) j Ev y *
          PDE.hilbertVectorLpCoord Ω (2 ) i Hv y := by
  have hEraw (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      PDE.hilbertVectorLpCoord Ω (2 ) j Ev y =
        PDE.hilbertVectorLpCoord Ω (2 ) j Gv y - Wl j y := by
    rw [hEeq j]
    filter_upwards [MeasureTheory.Lp.coeFn_sub
      (PDE.hilbertVectorLpCoord Ω (2 ) j Gv)
      (Wl j)] with y hy
    exact hy
  have hHraw (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      PDE.hilbertVectorLpCoord Ω (2 ) i Hv y =
        PDE.hilbertVectorLpCoord Ω (2 ) i Gv y + Wl i y := by
    rw [hHeq i]
    filter_upwards [MeasureTheory.Lp.coeFn_add
      (PDE.hilbertVectorLpCoord Ω (2 ) i Gv)
      (Wl i)] with y hy
    exact hy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [hEraw j, hHraw i] with y hE hH
  rw [hE, hH]

private theorem raw_translatedPrincipal_eq_canonical_ev_hv
     {Ω inner : PDE.VelocityRegion d} {Kη Kχ T : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ζ : ReverseTimeScalarTest T)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) :
    rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u =
      canonicalTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u := by
  let sharedTerm_362d6a69f2 := ((gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)))
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let Gv : PDE.HilbertVectorLp Ω (2 ) := gradientCLM hΩ (A u)
  let Wl  := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u)
  let Ev : PDE.HilbertVectorLp Ω (2 ) :=
    localizedSpatialDifferenceQuotientPrincipalFieldCLM
      hΩ η k h η.tsupport_subset hηshift u
  let Hv : PDE.HilbertVectorLp Ω (2 ) :=
    localizedSpatialDifferenceQuotientCompanionFieldCLM
      hΩ η k h η.tsupport_subset hηshift u
  let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  have hEeq (j : Fin d) :
      PDE.hilbertVectorLpCoord Ω (2 ) j Ev =
        PDE.hilbertVectorLpCoord Ω (2 ) j Gv - Wl j := by
    calc
      _ = PDE.hilbertVectorLpCoord Ω (2 ) j
          sharedTerm_362d6a69f2 -
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
            (valueCLM hΩ u) := by
        solve_by_elim (maxDepth := 4) [@_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM]
      _ = _ := by
        gcongr
  have hHeq (i : Fin d) :
      PDE.hilbertVectorLpCoord Ω (2 ) i Hv =
        PDE.hilbertVectorLpCoord Ω (2 ) i Gv + Wl i := by
    calc
      _ = PDE.hilbertVectorLpCoord Ω (2 ) i
          sharedTerm_362d6a69f2 +
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
            (valueCLM hΩ u) := (id (hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM hΩ η i k h η.tsupport_subset hηshift u))
      _ = _ := by
        gcongr
  have hbridge := integral_eq_of_coord_sub_add
    ζ χ k h τ α Gv Wl Ev Hv hEeq hHeq
  simpa only [rawTranslatedPrincipalValue, canonicalTranslatedPrincipalValue,
    A, Gv, Wl, Ev, Hv, α] using hbridge

private theorem scalar_coercive_consequence
    (Q P R z X Y : ℝ) (hsplit : Q = -P + z * R) (hprincipal : z * X ≤ P)
    (hRabs : |R| ≤ Y) (hz : 0 ≤ z) :
    Q + z * X ≤ z * Y := by
  have hRle  := (le_abs_self R).trans hRabs
  nlinarith

variable {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}

private theorem translated_principal_raw_lower

    (r₀ r₁ lam Lam : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (hζnonneg : 0 ≤ ζ τ)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) :
    ζ τ * (lam * ‖gradientCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 -
      Lam * ‖cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u‖ ^ 2) ≤
      rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u := (id
  (fun hcanonical =>
    LE.le.trans_eq hcanonical (Eq.symm (raw_translatedPrincipal_eq_canonical_ev_hv r₁ hΩ a ζ η χ k h τ hηshift u)))
  (localizedSpatialDifferenceQuotient_translatedPrincipal_lower_of_loewner r₀ r₁ lam Lam hΩ a haSmooth hLower hUpper ζ η
    χ k h hχshift τ hτ hζnonneg u))

variable (r₀ r₁ : ℝ)

variable (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)

private def compactSplitOutput


    (_ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (_hζ : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
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
      let A := localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift
      let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h η.tsupport_subset hηshift
      ζ τ * (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ (B u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) =
        -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u

private theorem compactSplitOutput_of_accepted


    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζ : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    compactSplitOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := by
  obtain ⟨δ, hδ, hrest⟩ :=
    exists_smallStep_h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder
      r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ
  refine ⟨δ, hδ, ?_⟩
  intro k h hh
  obtain ⟨hχshift, hfixed⟩ := hrest k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ u
  change _ = -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ _ u + _
  simpa only [rawTranslatedPrincipalValue] using hfixed τ hτ u

variable (hΩ : IsOpen Ω) (a : CoefficientField d) (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)

private def compactRemainderOutput


    (_ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 ≤ Cε ∧
    ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      ∀ hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
        (tsupport χ.toFun) Ω, ∀ (τ : ℝ), τ ∈ Set.Icc 0 (r₁ - r₀) →
        ∀ u : H10HilbertGraph hΩ,
        let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
          intro y hy; apply subset_tsupport; change χ y ≠ 0
          rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
        let hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
            (tsupport η.toFun) Ω := hχshift.mono_left hηχ
        let A := localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift
        |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u| ≤
          ε * ‖gradientCLM hΩ (A u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)

private theorem compactRemainderOutput_of_accepted


    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    compactRemainderOutput r₀ r₁ hΩ a b c F ha hb hc hF η χ := by
  obtain ⟨δ, hδ, hrest⟩ :=
    exists_smallStep_localizedSpatialDifferenceQuotientH10_nonprincipalRemainder_bound
      r₀ r₁ hΩ a b c F ha hb hc hF η χ
  refine ⟨δ, hδ, ?_⟩
  assumption

variable (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)

variable (a : CoefficientField d) (b : PDE.TimeVectorField d)

variable (c F : PDE.TimeScalarField d)

private def coerciveFixedSlice



    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) (τ : ℝ) (u : H10HilbertGraph hΩ) : Prop :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
  let hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : PDE.HilbertVectorLp Ω (2 ) := gradientCLM hΩ (A u)
  let Wv : PDE.HilbertVectorLp Ω (2 ) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  let Q : ℝ := ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
  Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
    ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2))

private theorem coerciveFixedSlice_of_adapterFacts



    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ)
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hζnonneg : 0 ≤ ζ τ)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ)
    (hsplit : ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) =
        -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u)
    (hrem : |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
      r₁ hΩ a b c F η χ k h τ hηshift u| ≤
        ε * ‖gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) :
    coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
      k h hχshift τ u := by

  let hηshift'  := hχshift.mono_left (by
      intro y hy; apply subset_tsupport; change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]; exact one_ne_zero)
  have hshift : hηshift = hηshift' := Subsingleton.elim _ _
  subst hηshift

  let B  :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift'
  let Gv : PDE.HilbertVectorLp Ω (2 ) := gradientCLM hΩ ((localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift') u)

  let Q : ℝ := ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
  let z : ℝ := ζ τ
  let X : ℝ := lam * ‖Gv‖ ^ 2 - Lam * ‖(cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u)‖ ^ 2
  let Y : ℝ := ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)
  let R : ℝ := localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift' u
  let Praw : ℝ := rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift' u
  change Q = -Praw + z * R at hsplit
  have hprincipalRaw := translated_principal_raw_lower
    r₀ r₁ lam Lam hΩ a ha hLower hUpper ζ η χ k h hχshift τ hτ hζnonneg hηshift' u
  change z * X ≤ Praw at hprincipalRaw
  change |R| ≤ Y at hrem
  change coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
    k h hχshift τ u
  dsimp only [coerciveFixedSlice]
  exact scalar_coercive_consequence Q Praw R z X Y hsplit hprincipalRaw hrem hζnonneg

variable (c : PDE.TimeScalarField d)

private def coerciveConsequenceOutput


    (_ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (_hζ : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 ≤ Cε ∧
    ∀ (lam Lam : ℝ)
      (_hLower : ∀ z : TimeVelocity d,
        z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
      (_hUpper : ∀ z : TimeVelocity d,
        z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        ∃ hχshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (_hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (_hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
          coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
            k h hχshift τ u

variable (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (F : PDE.TimeScalarField d) (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζ : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)

private theorem coerciveConsequenceOutput_of_adapters


     :
    coerciveConsequenceOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := (Exists.casesOn (compactSplitOutput_of_accepted r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ) fun δsplit h =>
  And.casesOn h fun hδsplit hsplit =>
    Exists.casesOn (compactRemainderOutput_of_accepted r₀ r₁ hΩ a b c F ha hb hc hF η χ) fun δrem h =>
      And.casesOn h fun hδrem hrem =>
        Exists.intro (min δsplit δrem)
          ⟨lt_min hδsplit hδrem, fun ε hε =>
            Exists.casesOn (hrem ε hε) fun Cε h =>
              And.casesOn h fun hCε hremStep =>
                Exists.intro Cε
                  ⟨hCε, fun lam Lam hLower hUpper k h hh =>
                    Exists.casesOn (hsplit k h (LE.le.trans hh (min_le_left δsplit δrem))) fun hχshift hsplitStep =>
                      Exists.intro hχshift fun τ hτ hζnonneg u =>
                        id
                          (fun hsplitEq =>
                            id
                              (fun hremBound =>
                                coerciveFixedSlice_of_adapterFacts r₀ r₁ h₀₁ hΩ hΩbounded a b c F ha hF ζ η χ ε Cε lam
                                  Lam hLower hUpper k h hχshift τ hτ hζnonneg
                                  (MapsTo.mono_left hχshift fun ⦃y⦄ hy =>
                                    subset_tsupport χ.toFun
                                      (id
                                        (Eq.mpr (id (congrArg (fun _a => _a ≠ 0) (χ.eq_one_on_inner y hy)))
                                          one_ne_zero)))
                                  u hsplitEq hremBound)
                              (hremStep k h (LE.le.trans hh (min_le_right δsplit δrem)) hχshift τ hτ u))
                          (hsplitStep τ hτ u)⟩⟩)




/-- For all sufficiently small signed steps, the exact fixed-slice H10
commutator plus its Loewner coercive term is bounded by the weighted
nonprincipal Young remainder. -/
theorem exists_smallStep_h10Commutator_add_coerciveTerm_le_nonprincipalYoung


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
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ Cε : ℝ, 0 ≤ Cε ∧
          ∀ (lam Lam : ℝ)
            (hLower : ∀ z : TimeVelocity d,
              z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
            (hUpper : ∀ z : TimeVelocity d,
              z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
            ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
              ∃ hχshift : Set.MapsTo
                (fun y  => y + h • PDE.basisVec k)
                (tsupport χ.toFun) Ω,
              ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
                (hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
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
                let Gv : PDE.HilbertVectorLp Ω (2 ) :=
                  gradientCLM hΩ (A u)
                let Wv : PDE.HilbertVectorLp Ω (2 ) :=
                  cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
                let Q : ℝ := ζ τ *
                  (reverseTimeNegativeSourceRaw
                      r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
                    reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
                Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
                  ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) := (id
  (coerciveConsequenceOutput_of_adapters r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η
    χ))

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
        (b : PDE.TimeVectorField d)
        (c F : PDE.TimeScalarField d),
        ∀ (haSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => a z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hbSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => b z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hcSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => c z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hFSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => F z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hLower : ∀ z : TimeVelocity d,
            z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
              lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
          (hUpper : ∀ z : TimeVelocity d,
            z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
              a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
          (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialMatrixFDerivFrobeniusNorm
              (fun w  =>
                reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            PDE.vecEuclideanNorm
              (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialVectorFDerivFrobeniusNorm
              (fun w  =>
                reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialScalarFDerivEuclideanNorm
              (fun w  =>
                -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialScalarFDerivEuclideanNorm
              (fun w  =>
                -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
          (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
          let hχshift : Set.MapsTo
              (fun y  => y + h • PDE.basisVec k)
              (tsupport χ.toFun) Ω :=
            mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
              hcarrier k hh
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
          let Gv : PDE.HilbertVectorLp Ω (2 ) :=
            gradientCLM hΩ (A u)
          let Wv : PDE.HilbertVectorLp Ω (2 ) :=
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
    hA hB hBD hq hqD hfD k h hh τ hτ hζnonneg u
  let hχshift  :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh

  let hηshift  :=
    hχshift.mono_left (by
        intro y hy
        apply subset_tsupport
        change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]
        exact one_ne_zero)
  have hsplit :=
    h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit δ hcarrier M hM a b c F haSmooth
        hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD k h hh τ hτ u

  have hremBound :=
    hrem a b c F haSmooth hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD
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
      k h hχshift τ hτ hζnonneg hηshift u (by
          simpa only [rawTranslatedPrincipalValue] using hsplit) hremBound

end HypoellipticAleksandrov.Parabolic.Dirichlet
