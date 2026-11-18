module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder





/-- Testing the reverse-time spatial form against `u₊` only sees `u₊` in
the first argument as well. -/
theorem reverseTimeSpatialForm_apply_positivePart_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10PositivePart hΩ u) =
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10PositivePart hΩ u) (h10PositivePart hΩ u)     := by
  have h10PositivePart_gradientCoord {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω,
    (PDE.hilbertVectorLpCoord Ω 2 k
      (gradientCLM hΩ (h10PositivePart hΩ u))) y =
      {z | 0 < valueCLM hΩ u z}.indicator
        (fun z => (PDE.hilbertVectorLpCoord Ω 2 k
          (gradientCLM hΩ u)) z) y := by
    filter_upwards [gradientCLM_h10PositivePart hΩ u,
      PDE.coeFn_hilbertVectorLpCoord Ω 2 k (gradientCLM hΩ u),
      PDE.coeFn_hilbertVectorLpCoord Ω 2 k
        (gradientCLM hΩ (h10PositivePart hΩ u))] with y hg hu hp
    calc
      _ = (gradientCLM hΩ (h10PositivePart hΩ u) y).ofLp k := hp
      _ = ({z | 0 < valueCLM hΩ u z}.indicator
          (gradientCLM hΩ u) y).ofLp k := congrArg (fun q => q.ofLp k) hg
      _ = _ := by
        by_cases hy : 0 < valueCLM hΩ u y
        · have hleft :
              {z | 0 < valueCLM hΩ u z}.indicator
                  (fun z => gradientCLM hΩ u z) y = gradientCLM hΩ u y :=
            Set.indicator_of_mem (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _
          have hright :
              {z | 0 < valueCLM hΩ u z}.indicator
                  (fun z => (PDE.hilbertVectorLpCoord Ω 2 k
                    (gradientCLM hΩ u)) z) y =
                (PDE.hilbertVectorLpCoord Ω 2 k
                  (gradientCLM hΩ u)) y :=
            Set.indicator_of_mem (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _
          rw [hleft, hright]
          exact hu.symm
        · have hleft :
              {z | 0 < valueCLM hΩ u z}.indicator
                  (fun z => gradientCLM hΩ u z) y = 0 :=
            Set.indicator_of_notMem
              (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _
          have hright :
              {z | 0 < valueCLM hΩ u z}.indicator
                  (fun z => (PDE.hilbertVectorLpCoord Ω 2 k
                    (gradientCLM hΩ u)) z) y = 0 :=
            Set.indicator_of_notMem
              (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _
          rw [hleft, hright]
          rfl
  have reverseTimeScalar_positivePart_eq {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (c : ℝ → PDE.Vec d → ℝ) (u : H10HilbertGraph hΩ) :
      (∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10PositivePart hΩ u) y) =
        ∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ (h10PositivePart hΩ u) y *
          valueCLM hΩ (h10PositivePart hΩ u) y := by
    have hvalue : ∀ᵐ y ∂PDE.volumeOn Ω,
        valueCLM hΩ (h10PositivePart hΩ u) y = max (valueCLM hΩ u y) 0 := by
      rw [valueCLM_h10PositivePart]
      exact Lp.coeFn_posPart (valueCLM hΩ u)
    apply integral_congr_ae
    filter_upwards [hvalue] with y hv
    by_cases hy : 0 < valueCLM hΩ u y
    · have hv' : valueCLM hΩ (h10PositivePart hΩ u) y = valueCLM hΩ u y :=
        hv.trans (max_eq_left (le_of_lt hy))
      exact congrArg (fun q => reverseTimeScalarCoefficient r₁ c τ y * q *
        valueCLM hΩ (h10PositivePart hΩ u) y) hv'.symm
    · have hvzero : valueCLM hΩ (h10PositivePart hΩ u) y = 0 :=
        hv.trans (max_eq_right (le_of_not_gt hy))
      calc
        _ = reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y * 0 :=
          congrArg (fun q => reverseTimeScalarCoefficient r₁ c τ y *
            valueCLM hΩ u y * q) hvzero
        _ = 0 := mul_zero _
        _ = reverseTimeScalarCoefficient r₁ c τ y * 0 * 0 := by ring
        _ = _ := congrArg (fun q => reverseTimeScalarCoefficient r₁ c τ y * q * q)
          hvzero.symm
  have reverseTimeDrift_positivePart_eq {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (u : H10HilbertGraph hΩ) :
      (∑ j : Fin d, ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y *
          valueCLM hΩ (h10PositivePart hΩ u) y) =
        ∑ j : Fin d, ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω 2 j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            valueCLM hΩ (h10PositivePart hΩ u) y := by
    have hvalue : ∀ᵐ y ∂PDE.volumeOn Ω,
        valueCLM hΩ (h10PositivePart hΩ u) y = max (valueCLM hΩ u y) 0 := by
      rw [valueCLM_h10PositivePart]
      exact Lp.coeFn_posPart (valueCLM hΩ u)
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    have hj := h10PositivePart_gradientCoord hΩ u j
    filter_upwards [hvalue, hj] with y hv hpj
    by_cases hy : 0 < valueCLM hΩ u y
    · have hpj' := hpj.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
      exact congrArg (fun q => reverseTimeDivergenceDrift r₁ a b τ y j * q *
        valueCLM hΩ (h10PositivePart hΩ u) y) hpj'.symm
    · have hvzero : valueCLM hΩ (h10PositivePart hΩ u) y = 0 :=
        hv.trans (max_eq_right (le_of_not_gt hy))
      calc
        _ = reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y * 0 :=
          congrArg (fun q => reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y * q) hvzero
        _ = 0 := mul_zero _
        _ = reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω 2 j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y * 0 := (mul_zero _).symm
        _ = _ := congrArg (fun q => reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (h10PositivePart hΩ u))) y * q) hvzero.symm
  have reverseTimePrincipal_positivePart_eq {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d) (u : H10HilbertGraph hΩ) :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω 2 i
            (gradientCLM hΩ (h10PositivePart hΩ u))) y) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            (PDE.hilbertVectorLpCoord Ω 2 i
              (gradientCLM hΩ (h10PositivePart hΩ u))) y := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [(h10PositivePart_gradientCoord hΩ u j), (h10PositivePart_gradientCoord hΩ u i)] with y hpj hpi
    by_cases hy : 0 < valueCLM hΩ u y
    · have hpj' := hpj.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
      have hpi' := hpi.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
      calc
        _ = a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y *
            (PDE.hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u)) y :=
          congrArg (fun q => a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y * q) hpi'
        _ = a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            (PDE.hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u)) y :=
          congrArg (fun q => a (r₁ - τ) y i j * q *
            (PDE.hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u)) y) hpj'.symm
        _ = _ := congrArg (fun q => a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (h10PositivePart hΩ u))) y * q) hpi'.symm
    · have hpj' := hpj.trans (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
      have hpi' := hpi.trans (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
      calc
        _ = a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y * 0 :=
          congrArg (fun q => a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y * q) hpi'
        _ = 0 := mul_zero _
        _ = a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y * 0 := (mul_zero _).symm
        _ = _ := congrArg (fun q => a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (h10PositivePart hΩ u))) y * q) hpi'.symm
  rw [reverseTimeSpatialForm_apply, reverseTimeSpatialForm_apply]
  rw [reverseTimePrincipal_positivePart_eq hΩ r₁ τ a u]
  apply congrArg₂ (fun x y => x - y)
  · exact congrArg (fun q => _ + q)
      (reverseTimeDrift_positivePart_eq hΩ r₁ τ a b u)
  · exact reverseTimeScalar_positivePart_eq hΩ r₁ τ c u



local instance comparisonModule {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) := MeasureTheory.Lp.instModule




private def comparisonClamp (T r : ℝ) := min T (max 0 r)

private theorem comparisonClamp_mem {T : ℝ} (hT : 0 < T) (r : ℝ) :
    comparisonClamp T r ∈ Icc 0 T := by
  exact ⟨le_min hT.le (le_max_left _ _), min_le_left _ _⟩

private theorem comparisonClamp_eq {T r : ℝ} (hr : r ∈ Icc 0 T) :
    comparisonClamp T r = r := by
  simp only [comparisonClamp, max_eq_right hr.1, min_eq_right hr.2]


private theorem comparison_clamped_energy_zero
    {E : Type*} [NormedAddCommGroup E] [Lattice E] [Norm E]
    {T : ℝ} (hT : 0 < T) (W : C(Icc 0 T, E))
    (hW0 : ‖W ⟨0,⟨le_rfl,hT.le⟩⟩‖ = 0) :
    ‖W ⟨comparisonClamp T 0, comparisonClamp_mem hT 0⟩‖^2 = 0 := by
  have hh : (⟨comparisonClamp T 0,comparisonClamp_mem hT 0⟩ : Icc 0 T) =
      ⟨0,⟨le_rfl,hT.le⟩⟩ := Subtype.ext (comparisonClamp_eq ⟨le_rfl,hT.le⟩)
  rw [hh, hW0]
  norm_num






/-- Reverse-time variational comparison: ordered initial data and the original-source
orientation `F₂ ≤ F₁` imply spatial almost-everywhere order at every closed time. -/
theorem reverseTimeVariationalEnergySolution_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F₁ F₂ : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF₁Smooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F₁ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF₂Smooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F₂ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0)
    (hF₂leF₁ : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      F₂ z.1 z.2 ≤ F₁ z.1 z.2)
    (initial₁ initial₂ : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, initial₁ y ≤ initial₂ y)
    (u₁ : ReverseTimeL2V hΩ (r₁ - r₀))
    (g₁ : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu₁ : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u₁ g₁)
    (hu₁ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₁ hF₁Smooth initial₁ u₁ g₁ hdu₁)
    (u₂ : ReverseTimeL2V hΩ (r₁ - r₀))
    (g₂ : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu₂ : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u₂ g₂)
    (hu₂ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₂ hF₂Smooth initial₂ u₂ g₂ hdu₂) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u₁ g₁ hdu₁ ⟨τ, hτ⟩ y ≤
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u₂ g₂ hdu₂ ⟨τ, hτ⟩ y      := by
  have comparison_posPart_clamped_energy_zero {Ω : Set (PDE.Vec d)} {T : ℝ} (hT : 0 < T) (W : C(Icc 0 T, PDE.ScalarLp Ω 2)) (hW0 : Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩) = 0) :
      ‖Lp.posPart (W ⟨comparisonClamp T 0, comparisonClamp_mem hT 0⟩)‖^2 = 0 := by
    exact comparison_clamped_energy_zero hT
      ⟨fun q => Lp.posPart (W q), Lp.continuous_posPart.comp W.continuous⟩
      (by change ‖Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩)‖ = 0; rw [hW0, norm_zero])
  have reverseTimeHilbertRepresentative_sub_eq {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : ReverseTimeL2V hΩ T) (k : ReverseTimeL2VStar hΩ T) (hdv : HasGelfandWeakTimeDerivative hΩ T hT v k) (hdiff : HasGelfandWeakTimeDerivative hΩ T hT (u - v) (g - k)) :
      reverseTimeHilbertRepresentative hΩ T hT (u - v) (g - k) hdiff =
      reverseTimeHilbertRepresentative hΩ T hT u g hdu -
        reverseTimeHilbertRepresentative hΩ T hT v k hdv := by
    obtain ⟨hU, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu
    obtain ⟨hV, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT v k hdv
    obtain ⟨hW, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT (u - v) (g - k) hdiff
    apply ReverseTimeHilbertRepresentativeAgrees.unique hW hT
    filter_upwards [hU, hV, Lp.coeFn_sub u v] with τ hUτ hVτ huv
    intro hτ
    let hτcc : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    change
      (reverseTimeHilbertRepresentative hΩ T hT u g hdu -
        reverseTimeHilbertRepresentative hΩ T hT v k hdv) ⟨τ, hτcc⟩ =
        valueCLM hΩ ((u - v) τ)
    change reverseTimeHilbertRepresentative hΩ T hT u g hdu ⟨τ, hτcc⟩ -
        reverseTimeHilbertRepresentative hΩ T hT v k hdv ⟨τ, hτcc⟩ =
          valueCLM hΩ ((u - v) τ)
    rw [hUτ hτ, hVτ hτ, huv]
    exact (valueCLM hΩ).map_sub _ _
  have comparison_ae_rate {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F₁ F₂ : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood (fun z => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hF₁Smooth : IsSmoothOnNeighborhood (fun z => F₁ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hF₂Smooth : IsSmoothOnNeighborhood (fun z => F₂ z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • 1 ≤ a z.1 z.2) (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0) (hF₂leF₁ : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      F₂ z.1 z.2 ≤ F₁ z.1 z.2) (initial₁ initial₂ : PDE.ScalarLp Ω 2) (u₁ : ReverseTimeL2V hΩ (r₁-r₀)) (g₁ : ReverseTimeL2VStar hΩ (r₁-r₀)) (hdu₁ : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) (sub_pos.mpr h₀₁) u₁ g₁) (hu₁ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₁ hF₁Smooth initial₁ u₁ g₁ hdu₁) (u₂ : ReverseTimeL2V hΩ (r₁-r₀)) (g₂ : ReverseTimeL2VStar hΩ (r₁-r₀)) (hdu₂ : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) (sub_pos.mpr h₀₁) u₂ g₂) (hu₂ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₂ hF₂Smooth initial₂ u₂ g₂ hdu₂) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ τ ∂reverseTimeVolume (r₁-r₀),
      2 * ((g₁-g₂) τ) (h10PositivePart hΩ ((u₁-u₂) τ)) +
        lam * ‖gradientCLM hΩ (h10PositivePart hΩ ((u₁-u₂) τ))‖^2 ≤
      2*K*‖valueCLM hΩ (h10PositivePart hΩ ((u₁-u₂) τ))‖^2 := by
    have comparison_scalar_energy (g₁ g₂ B₁ B₂ Bw Bp S₁ S₂ G V lam K : ℝ) (h₁ : g₁ + B₁ = S₁) (h₂ : g₂ + B₂ = S₂) (hBsub : B₁ - B₂ = Bw) (hBpos : Bw = Bp) (hS : S₁ - S₂ ≤ 0) (hG : (lam / 2) * G - K * V ≤ Bp) :
        2 * (g₁ - g₂) + lam * G ≤ 2 * K * V := by
      linarith
    have reverseTimeSourceFunctional_sub_nonpos_of_ae_le {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (f₁ f₂ : PDE.ScalarLp Ω 2) (hf : ∀ᵐ y ∂PDE.volumeOn Ω, f₂ y ≤ f₁ y) (u : H10HilbertGraph hΩ) :
        reverseTimeSourceFunctional hΩ f₁ (h10PositivePart hΩ u) -
        reverseTimeSourceFunctional hΩ f₂ (h10PositivePart hΩ u) ≤ 0 := by
      have hvalueNonneg :
          ∀ᵐ y ∂PDE.volumeOn Ω,
            0 ≤ valueCLM hΩ (h10PositivePart hΩ u) y := by
        rw [valueCLM_h10PositivePart]
        filter_upwards [Lp.coeFn_posPart (valueCLM hΩ u)] with y hy
        rw [hy]
        exact le_max_right _ _
      have hinner :
          inner ℝ (valueCLM hΩ (h10PositivePart hΩ u)) f₂ ≤
            inner ℝ (valueCLM hΩ (h10PositivePart hΩ u)) f₁ := by
        rw [L2.inner_def, L2.inner_def]
        apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
        filter_upwards [hf, hvalueNonneg] with y hyf hyv
        simp
        exact mul_le_mul_of_nonneg_right hyf hyv
      rw [reverseTimeSourceFunctional_apply, reverseTimeSourceFunctional_apply,
        neg_sub_neg]
      exact sub_nonpos.mpr hinner
    obtain ⟨K,hK,hGard⟩ := reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
    refine ⟨K,hK,?_⟩
    rcases hu₁ with ⟨_,heq₁⟩
    rcases hu₂ with ⟨_,heq₂⟩
    filter_upwards [heq₁,heq₂,Lp.coeFn_sub u₁ u₂,Lp.coeFn_sub g₁ g₂,
      ae_restrict_mem measurableSet_Ioo] with τ heq₁τ heq₂τ huτ hgτ hτ
    have hτcc : τ ∈ Icc 0 (r₁-r₀) := ⟨hτ.1.le,hτ.2.le⟩
    let w := u₁ τ-u₂ τ
    let wp := h10PositivePart hΩ w
    let f₁ := reverseTimeSourceSlice r₁ τ F₁
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F₁ hF₁Smooth τ hτcc)
    let f₂ := reverseTimeSourceSlice r₁ τ F₂
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F₂ hF₂Smooth τ hτcc)
    have hs : ∀ᵐ y ∂PDE.volumeOn Ω, f₂ y ≤ f₁ y := by
      filter_upwards [coeFn_reverseTimeSourceSlice r₁ τ F₁ _,
        coeFn_reverseTimeSourceSlice r₁ τ F₂ _,ae_restrict_mem hΩ.measurableSet]
        with y h1 h2 hy
      rw [h1,h2]
      exact hF₂leF₁ (r₁-τ,y) ⟨⟨by linarith [h₀₁,hτ.2],by linarith [hτ.1]⟩,
        subset_closure hy⟩
    have e₁ : (g₁ τ) wp + reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ τ) wp =
        reverseTimeSourceFunctional hΩ f₁ wp := heq₁τ hτ wp
    have e₂ : (g₂ τ) wp + reverseTimeSpatialForm hΩ r₁ τ a b c (u₂ τ) wp =
        reverseTimeSourceFunctional hΩ f₂ wp := heq₂τ hτ wp
    let B := reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth ⟨τ,hτcc⟩
    have hB : reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ τ) wp -
        reverseTimeSpatialForm hΩ r₁ τ a b c (u₂ τ) wp =
        reverseTimeSpatialForm hΩ r₁ τ a b c w wp := by
      have hm := congrArg (fun q => q wp)
        (B.map_sub (u₁ τ) (u₂ τ))
      simpa only [B,reverseTimeSpatialFormOperator_apply,ContinuousLinearMap.sub_apply,w]
        using hm.symm
    rw [huτ,hgτ]
    change 2*((g₁ τ) wp-(g₂ τ) wp)+lam*‖gradientCLM hΩ wp‖^2 ≤
      2*K*‖valueCLM hΩ wp‖^2
    exact comparison_scalar_energy _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ hB (reverseTimeSpatialForm_apply_positivePart_eq hΩ r₁ τ a b c w) (reverseTimeSourceFunctional_sub_nonpos_of_ae_le hΩ f₁ f₂ hs w) (hGard τ hτcc wp)
  have comparison_posPart_zero {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (w : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hd : HasGelfandWeakTimeDerivative hΩ T hT w g) (K : ℝ) (hK : 0 ≤ K) (hrate : ∀ᵐ τ ∂reverseTimeVolume T,
      2 * (g τ) (h10PositivePart hΩ (w τ)) +
        ‖gradientCLM hΩ (h10PositivePart hΩ (w τ))‖ ^ 2 * 0 ≤
      2 * K * ‖valueCLM hΩ (h10PositivePart hΩ (w τ))‖ ^ 2) (hW0 : Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd
      ⟨0,⟨le_rfl,hT.le⟩⟩) = 0) :
      ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd ⟨t,ht⟩) = 0 := by
    have comparison_value_integral {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (w : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hd : HasGelfandWeakTimeDerivative hΩ T hT w g) (t : ℝ) (ht : t ∈ Icc 0 T) :
        (∫ r in Ioc 0 t, ‖valueCLM hΩ (h10PositivePart hΩ (w r))‖ ^ 2
        ∂reverseTimeVolume T) =
      ∫ r in Ioc 0 t, ‖Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd
        ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩)‖ ^ 2 := by
      have comparison_setIntegral_eq (f : ℝ → ℝ) :
          (∫ r in Ioc 0 t, f r ∂reverseTimeVolume T) = ∫ r in Ioc 0 t, f r := by
        rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
          Measure.restrict_restrict measurableSet_Ioc]
        congr 2
        exact inter_eq_left.mpr (Ioc_subset_Icc_self.trans fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)
      let W := reverseTimeHilbertRepresentative hΩ T hT w g hd
      calc
        _ = ∫ r in Ioc 0 t, ‖Lp.posPart (W
            ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩)‖ ^ 2
            ∂reverseTimeVolume T := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae ((reverseTimeHilbertRepresentative_spec hΩ T hT w g hd).1),
            ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioo)] with r hWr hr
          have hrcc : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
          have hWr' : W ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩ =
              valueCLM hΩ (w r) := by simpa only [comparisonClamp_eq hrcc] using hWr hr
          rw [hWr', ← valueCLM_h10PositivePart]
        _ = _ := comparison_setIntegral_eq _
    have comparisonClamp_continuous : Continuous (comparisonClamp T) :=
      continuous_const.min (continuous_const.max continuous_id)
    have comparison_energy_increment {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hd : HasGelfandWeakTimeDerivative hΩ T hT u g) (t : ℝ) (ht : t ∈ Icc 0 T) :
        ‖Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT u g hd ⟨t, ht⟩)‖ ^ 2 -
        ‖Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT u g hd
          ⟨0, ⟨le_rfl, hT.le⟩⟩)‖ ^ 2 =
        2 * ∫ r in Ioc 0 t, (g r) (h10PositivePart hΩ (u r)) ∂reverseTimeVolume T := by
      exact reverseTimeHilbertRepresentative_posPart_norm_sq_increment hΩ T hT u g hd
        0 t ⟨le_rfl, hT.le⟩ ht ht.1
    let W := reverseTimeHilbertRepresentative hΩ T hT w g hd
    let E : ℝ → ℝ := fun t => ‖Lp.posPart
      (W ⟨comparisonClamp T t, comparisonClamp_mem hT t⟩)‖^2
    have hEc : ContinuousOn E (Icc 0 T) :=
      (((Lp.continuous_posPart.comp W.continuous).norm.pow 2).comp
        ((comparisonClamp_continuous).subtype_mk _)).continuousOn
    have hEn : ∀ t ∈ Icc 0 T, 0 ≤ E t := fun _ _ => sq_nonneg _
    have hE0 : E 0 = 0 := by
      exact comparison_posPart_clamped_energy_zero hT W hW0
    have hEle : ∀ t ∈ Icc 0 T, E t ≤ (2*K) * ∫ r in Ioc 0 t, E r := by
      intro t ht
      have hi := comparison_energy_increment hΩ T hT w g hd t ht
      have hpair :=
        (integrable_reverseTimeDualPairing hΩ T (reverseTimePositivePart hΩ T w) g).congr (by
          filter_upwards [coeFn_reverseTimePositivePart hΩ T w] with r hr
          rw [hr])
      have hm := (Lp.memLp (reverseTimePositivePart hΩ T w)).continuousLinearMap_comp
        (valueCLM hΩ)
      have hv :=
        ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm).congr (by
          filter_upwards [coeFn_reverseTimePositivePart hΩ T w] with r hr
          rw [hr])
      have hint : (∫ r in Ioc 0 t, 2 * (g r) (h10PositivePart hΩ (w r))
          ∂reverseTimeVolume T) ≤
          ∫ r in Ioc 0 t, 2*K*‖valueCLM hΩ (h10PositivePart hΩ (w r))‖^2
            ∂reverseTimeVolume T :=
        setIntegral_mono_ae_restrict (hpair.const_mul 2).integrableOn
        (hv.const_mul (2*K)).integrableOn (ae_restrict_of_ae (by
          filter_upwards [hrate] with r hr
          simpa using hr))
      rw [integral_const_mul, integral_const_mul] at hint
      have hh : (⟨comparisonClamp T t,comparisonClamp_mem hT t⟩ : Icc 0 T) =
          ⟨t,ht⟩ := Subtype.ext (comparisonClamp_eq ht)
      dsimp only [E]
      rw [hW0, norm_zero, zero_pow (by norm_num), sub_zero] at hi
      have hbound : ‖Lp.posPart (W ⟨t,ht⟩)‖^2 ≤
          2*K * ∫ r in Ioc 0 t, ‖Lp.posPart
            (W ⟨comparisonClamp T r, comparisonClamp_mem hT r⟩)‖^2 := by
        dsimp only [W]
        rw [← (comparison_value_integral hΩ T hT w g hd t ht)]
        linarith
      calc
        _ = ‖Lp.posPart (W ⟨t,ht⟩)‖^2 :=
          congrArg (fun q => ‖Lp.posPart (W q)‖^2) hh
        _ ≤ _ := hbound
    have hz := eq_zero_on_Icc_of_nonneg_le_mul_integral hT
      (mul_nonneg (by norm_num) hK) E hEc hEn hE0 hEle
    intro t ht
    have hh : (⟨comparisonClamp T t,comparisonClamp_mem hT t⟩ : Icc 0 T) =
        ⟨t,ht⟩ := Subtype.ext (comparisonClamp_eq ht)
    have hs : ‖Lp.posPart (W ⟨t,ht⟩)‖^2 = 0 := by
      simpa only [E, hh] using hz t ht
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (Lp.posPart (W ⟨t,ht⟩))]
  have comparison_initialTrace_sub {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u₁ u₂ : ReverseTimeL2V hΩ T) (g₁ g₂ : ReverseTimeL2VStar hΩ T) (hd₁ : HasGelfandWeakTimeDerivative hΩ T hT u₁ g₁) (hd₂ : HasGelfandWeakTimeDerivative hΩ T hT u₂ g₂) (hd : HasGelfandWeakTimeDerivative hΩ T hT (u₁-u₂) (g₁-g₂)) :
      reverseTimeInitialTrace hΩ T hT (u₁-u₂) (g₁-g₂) hd =
      reverseTimeInitialTrace hΩ T hT u₁ g₁ hd₁ -
        reverseTimeInitialTrace hΩ T hT u₂ g₂ hd₂ := by
    have hr := reverseTimeHilbertRepresentative_sub_eq hΩ T hT
      u₁ g₁ hd₁ u₂ g₂ hd₂ hd
    convert (congrArg (fun Q : C(Icc 0 T, PDE.ScalarLp Ω 2) => Q ⟨0,⟨le_rfl,hT.le⟩⟩) hr) using 1 <;> rfl
  let hT := sub_pos.mpr h₀₁
  let hd : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) hT
      (u₁ - u₂) (g₁ - g₂) := by
    change HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
      (u₁ - u₂) (g₁ - g₂)
    simpa [sub_eq_add_neg] using hdu₁.add (hdu₂.smul (-1 : ℝ))
  obtain ⟨K,hK,hrate⟩ := comparison_ae_rate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F₁ F₂ haSmooth hbSmooth hcSmooth hF₁Smooth hF₂Smooth hLower hcNonpos
    hF₂leF₁ initial₁ initial₂ u₁ g₁ hdu₁ hu₁ u₂ g₂ hdu₂ hu₂
  let wd := u₁-u₂
  let gd := g₁-g₂
  let hdd := hd
  have hrate' : ∀ᵐ τ ∂reverseTimeVolume (r₁-r₀),
      2 * (gd τ) (h10PositivePart hΩ (wd τ)) +
        lam * ‖gradientCLM hΩ (h10PositivePart hΩ (wd τ))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10PositivePart hΩ (wd τ))‖ ^ 2 := by
    simpa only [wd, gd] using hrate
  let W := reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT wd gd hdd
  have hW0 : Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩) = 0 := by
    change Lp.posPart (reverseTimeInitialTrace hΩ (r₁-r₀) hT (u₁-u₂) (g₁-g₂) hd) = 0
    rw [(comparison_initialTrace_sub hΩ (r₁-r₀) hT u₁ u₂ g₁ g₂ hdu₁ hdu₂ hd), (hu₁.1), (hu₂.1)]
    apply Lp.ext
    filter_upwards [Lp.coeFn_posPart (initial₁-initial₂), Lp.coeFn_sub initial₁ initial₂,
      Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω), hinitial]
      with y hp hs hz hi
    rw [hp, hs, hz]
    simp only [Pi.sub_apply]
    exact max_eq_right (sub_nonpos.mpr hi)
  intro τ hτ
  have hrate0 : ∀ᵐ r ∂reverseTimeVolume (r₁-r₀),
      2 * (gd r) (h10PositivePart hΩ (wd r)) +
        ‖gradientCLM hΩ (h10PositivePart hΩ (wd r))‖^2 * 0 ≤
      2*K*‖valueCLM hΩ (h10PositivePart hΩ (wd r))‖^2 := by
    filter_upwards [hrate'] with r hr
    have hg : 0 ≤ lam * ‖gradientCLM hΩ (h10PositivePart hΩ (wd r))‖^2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    simpa using (show
      2 * (gd r) (h10PositivePart hΩ (wd r)) ≤
        2*K*‖valueCLM hΩ (h10PositivePart hΩ (wd r))‖^2 by linarith)
  have hw : ∀ᵐ y ∂PDE.volumeOn Ω, W ⟨τ,hτ⟩ y ≤ 0 := by
    filter_upwards [Lp.ext_iff.mp (comparison_posPart_zero hΩ (r₁-r₀) hT wd gd hdd K hK hrate0 hW0 τ hτ), Lp.coeFn_posPart (W ⟨τ,hτ⟩),
      Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω)] with y hy hpy hz
    rw [hpy, hz] at hy
    exact max_eq_right_iff.mp hy
  have hrepW : W = reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ -
      reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ := by
    dsimp only [W, wd, gd, hdd]
    exact reverseTimeHilbertRepresentative_sub_eq hΩ (r₁-r₀) hT u₁ g₁ hdu₁ u₂ g₂ hdu₂ hd
  rw [hrepW] at hw
  filter_upwards [hw, Lp.coeFn_sub
    (reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ ⟨τ,hτ⟩)
    (reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ ⟨τ,hτ⟩)] with y hy hsy
  change ((reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ ⟨τ,hτ⟩ -
    reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ ⟨τ,hτ⟩) y) ≤ 0 at hy
  rw [hsy] at hy
  exact sub_nonpos.mp hy

end HypoellipticAleksandrov.Parabolic.Dirichlet

