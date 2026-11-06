module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCutoffFields
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Reverse-time coefficient cutoff fields

This module localizes the actual reverse-time coefficient fields by one
compact time--space cutoff before taking forward spatial translates and
difference quotients.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ}

private theorem exists_common_cutoff_mul_spatialFields_of_smoothOnNeighborhood
     {S : HypoellipticAleksandrov.Parabolic.Region d} {ι : Type*} [Fintype ι]
    (hS : IsCompact S) (β : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hβcont : Continuous β) (hβcompact : HasCompactSupport β)
    (hβS : tsupport β ⊆ S) (hβunit : ∀ z, ‖β z‖ ≤ 1)
    (f : ι → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ i, IsSmoothOnNeighborhood (f i) S) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (i : ι) (k : Fin d) (h : ℝ), |h| ≤ δ →
        (Continuous (fun z => β z * spatialTranslate k h (f i) z) ∧
          HasCompactSupport (fun z => β z * spatialTranslate k h (f i) z) ∧
          ∀ z, ‖β z * spatialTranslate k h (f i) z‖ ≤ C) ∧
        (Continuous (fun z => β z * spatialDifferenceQuotient k h (f i) z) ∧
          HasCompactSupport (fun z => β z * spatialDifferenceQuotient k h (f i) z) ∧
          ∀ z, ‖β z * spatialDifferenceQuotient k h (f i) z‖ ≤ C) := by
  classical
  have hfold : ∀ t : Finset ι, ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ i ∈ t, ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        (Continuous (fun z => β z * spatialTranslate k h (f i) z) ∧
          HasCompactSupport (fun z => β z * spatialTranslate k h (f i) z) ∧
          ∀ z, ‖β z * spatialTranslate k h (f i) z‖ ≤ C) ∧
        (Continuous (fun z => β z * spatialDifferenceQuotient k h (f i) z) ∧
          HasCompactSupport (fun z => β z * spatialDifferenceQuotient k h (f i) z) ∧
          ∀ z, ‖β z * spatialDifferenceQuotient k h (f i) z‖ ≤ C) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨1, 0, zero_lt_one, le_rfl, ?_⟩
        intro i hi
        exact (Finset.notMem_empty i hi).elim
    | insert i t hit ih =>
        rcases ih with ⟨δt, Ct, hδt, hCt, ht⟩
        rcases hf i with ⟨V, hVopen, hSV, hV⟩
        obtain ⟨δi, Ci, hδi, hCi, hi⟩ :=
          IsCompact.exists_cutoff_mul_spatialFields_of_contDiffOn_one hS hVopen hSV
            (f i) (hV.of_le (by simp))
        refine ⟨min δi δt, max Ci Ct, lt_min hδi hδt,
          hCi.trans (le_max_left _ _), ?_⟩
        intro q hq k h hh
        rcases Finset.mem_insert.mp hq with rfl | hq
        · rcases hi β hβcont hβcompact hβS hβunit k h (le_min_iff.mp hh).1 with
            ⟨htranslate, hdq⟩
          refine ⟨⟨htranslate.1, htranslate.2.1, ?_⟩, ⟨hdq.1, hdq.2.1, ?_⟩⟩
          · intro z
            exact (htranslate.2.2 z).trans (le_max_left _ _)
          · intro z
            exact (hdq.2.2 z).trans (le_max_left _ _)
        · rcases ht q hq k h (le_min_iff.mp hh).2 with ⟨htranslate, hdq⟩
          refine ⟨⟨htranslate.1, htranslate.2.1, ?_⟩, ⟨hdq.1, hdq.2.1, ?_⟩⟩
          · intro z
            exact (htranslate.2.2 z).trans (le_max_right _ _)
          · intro z
            exact (hdq.2.2 z).trans (le_max_right _ _)
  simpa using hfold Finset.univ

/-- A compact time--space cutoff simultaneously localizes the forward spatial
translates and totalized forward spatial difference quotients of the
reverse-time divergence-form coefficient fields. -/
theorem exists_reverseTimeCoefficient_cutoff_mul_spatialFields_of_smoothOnNeighborhood
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (r₀ r₁ : ℝ)
    (χ : PDE.QuantitativeSmoothCutoff inner outer K)
    (hχΩ : tsupport χ.toFun ⊆ Ω)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    let β : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * χ z.2
    let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
    let γ : HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      let fieldBound : (HypoellipticAleksandrov.Parabolic.ScalarField d) → Prop :=
        fun q =>
          ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
            (Continuous (fun z => β z * spatialTranslate k h q z) ∧
              HasCompactSupport (fun z => β z * spatialTranslate k h q z) ∧
              ∀ z, ‖β z * spatialTranslate k h q z‖ ≤ C) ∧
            (Continuous (fun z =>
                β z * spatialDifferenceQuotient k h q z) ∧
              HasCompactSupport (fun z =>
                β z * spatialDifferenceQuotient k h q z) ∧
              ∀ z, ‖β z * spatialDifferenceQuotient k h q z‖ ≤ C)
      (∀ i j : Fin d, fieldBound (α i j)) ∧
        (∀ j : Fin d, fieldBound (drift j)) ∧
        fieldBound γ := by
  dsimp only
  let S : HypoellipticAleksandrov.Parabolic.Region d := tsupport (ζ : ℝ → ℝ) ×ˢ tsupport χ.toFun
  let β : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * χ z.2
  have hS : IsCompact S :=
    ζ.hasCompactSupport.prod χ.hasCompactSupport

  have hβS : tsupport β ⊆ S := by
    apply closure_minimal
    · intro z hz
      have hmul : ζ z.1 * χ z.2 ≠ 0 := hz
      refine ⟨?_, ?_⟩
      · apply subset_tsupport
        intro hzero
        exact hmul (by simp [hzero])
      · apply subset_tsupport
        intro hzero
        exact hmul (by simp [hzero])
    · exact hS.isClosed


  have hreverseS : reverseTimeMap r₁ '' S ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
    rintro w ⟨z, hz, rfl⟩
    rcases hz with ⟨hτ, hy⟩
    have hτinterval : z.1 ∈ Set.Ioo 0 (r₁ - r₀) :=
      ζ.tsupport_subset hτ
    rw [mem_scalarParabolicClosedCylinder_iff]
    refine ⟨?_, ?_, subset_closure (hχΩ hy)⟩
    · simp only [reverseTimeMap_apply]
      linarith [hτinterval.2]
    · simp only [reverseTimeMap_apply]
      linarith [hτinterval.1]
  let q : (Fin d × Fin d) ⊕ (Fin d ⊕ Unit) → HypoellipticAleksandrov.Parabolic.ScalarField d := fun x z =>
    match x with
    | Sum.inl ⟨i, j⟩ => reverseTimeCoefficient r₁ a z.1 z.2 i j
    | Sum.inr (Sum.inl j) => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
    | Sum.inr (Sum.inr ()) => reverseTimeScalarCoefficient r₁ c z.1 z.2

  obtain ⟨δ, C, hδ, hC, hqfields⟩ :=
    exists_common_cutoff_mul_spatialFields_of_smoothOnNeighborhood hS β ((ζ.contDiff.continuous.comp continuous_fst).mul
          (χ.smooth.continuous.comp continuous_snd)) (hS.of_isClosed_subset (isClosed_tsupport _) hβS)
      hβS (by
          intro z
          rw [show β z = ζ z.1 * χ z.2 from rfl, norm_mul]

          calc
            ‖ζ z.1‖ * ‖χ z.2‖ ≤ 1 * 1 :=
              mul_le_mul (hζunit z.1) (by
                  rw [Real.norm_eq_abs, abs_of_nonneg (χ.nonneg _)]
                  exact χ.le_one _) (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul 1) q ((fun x =>
  Sum.casesOn x
    (fun x =>
      Prod.casesOn x fun i j =>
        id (IsSmoothOnNeighborhood.reverseTime r₁ hreverseS (IsSmoothOnNeighborhood.coefficientEntry a ha i j)))
    fun x =>
    Sum.casesOn x
      (fun x =>
        id (IsSmoothOnNeighborhood.reverseTime r₁ hreverseS (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb x)))
      fun x => PUnit.casesOn x (id (IsSmoothOnNeighborhood.reverseTime r₁ hreverseS hc))))
  refine ⟨δ, C, hδ, hC, ?_, ?_, ?_⟩
  · intro i j k h hh
    exact hqfields (Sum.inl (i, j)) k h hh
  · intro j k h hh
    exact hqfields (Sum.inr (Sum.inl j)) k h hh
  · intro k h hh
    exact hqfields (Sum.inr (Sum.inr ())) k h hh

end HypoellipticAleksandrov.Parabolic.Dirichlet
