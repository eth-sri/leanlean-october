module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Compact reverse-time coefficient difference-quotient bounds

This module derives simultaneous signed spatial difference-quotient bounds for
the smooth reverse-time coefficient fields on a compact time--velocity carrier.
It is pointwise infrastructure for a later commutator calculation.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ}

variable {S : HypoellipticAleksandrov.Parabolic.Region d} {ι : Type*}

private theorem exists_common_spatialDifferenceQuotient_bound_of_smoothOnNeighborhood
      [Fintype ι]
    (hS : IsCompact S) (f : ι → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ i, IsSmoothOnNeighborhood (f i) S) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (i : ι) (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δ → z ∈ S →
        |spatialDifferenceQuotient k h (f i) z| ≤ C := by
  classical
  have hfold : ∀ t : Finset ι, ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ i ∈ t, ∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δ → z ∈ S →
        |spatialDifferenceQuotient k h (f i) z| ≤ C := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨1, 0, zero_lt_one, le_rfl, ?_⟩
        intro i hi
        exact (Finset.notMem_empty i hi).elim
    | insert i t hit ih =>
        rcases ih with ⟨δt, Ct, hδt, hCt, ht⟩
        rcases hf i with ⟨V, hVopen, hSV, hV⟩
        obtain ⟨δi, Ci, hδi, hCi, _hδV, _hderiv, _hmap, hi⟩ :=
          IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one hS hVopen hSV
            (hV.of_le (by simp))
        refine ⟨min δi δt, max Ci Ct, lt_min hδi hδt,
          hCi.trans (le_max_left _ _), ?_⟩
        intro q hq k h z hh hz
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact (hi k h z (le_min_iff.mp hh).1 hz).trans (le_max_left _ _)
        · exact (ht q hq k h z (le_min_iff.mp hh).2 hz).trans (le_max_right _ _)
  simpa using hfold Finset.univ

private theorem exists_common_spatialTranslate_bound_of_smoothOnNeighborhood
      [Fintype ι]
    (hS : IsCompact S) (f : ι → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ i, IsSmoothOnNeighborhood (f i) S) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (i : ι) (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δ → z ∈ S →
        |spatialTranslate k h (f i) z| ≤ C := by
  classical
  have hfold : ∀ t : Finset ι, ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ i ∈ t, ∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δ → z ∈ S →
        |spatialTranslate k h (f i) z| ≤ C := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨1, 0, zero_lt_one, le_rfl, ?_⟩
        intro i hi
        exact (Finset.notMem_empty i hi).elim
    | insert i t hit ih =>
        rcases ih with ⟨δt, Ct, hδt, hCt, ht⟩
        rcases hf i with ⟨V, hVopen, hSV, hV⟩
        obtain ⟨δi, Di, hδi, hDi, hδV, _hderiv, _hmap, _hdq⟩ :=
          IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one hS hVopen hSV
            (hV.of_le (by simp))

        obtain ⟨Qi, hQi⟩ := hS.cthickening.exists_bound_of_continuousOn (hV.continuousOn.mono hδV)

        have hi : ∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δi → z ∈ S →
            |spatialTranslate k h (f i) z| ≤ max Qi Di := by
          intro k h z hh hz
          have hshift  :=
            Metric.mem_cthickening_of_dist_le (spatialShift k h z) z δi S hz
              (by simpa only [dist_spatialShift] using hh)
          change |f i (spatialShift k h z)| ≤ max Qi Di
          rw [← Real.norm_eq_abs]
          exact (hQi _ hshift).trans (le_max_left _ _)
        refine ⟨min δi δt, max (max Qi Di) Ct, lt_min hδi hδt,
          (hDi.trans (le_max_right _ _)).trans (le_max_left _ _), ?_⟩
        intro q hq k h z hh hz
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact (hi k h z (le_min_iff.mp hh).1 hz).trans (le_max_left _ _)
        · exact (ht q hq k h z (le_min_iff.mp hh).2 hz).trans (le_max_right _ _)
  simpa using hfold Finset.univ

/-- Smooth coefficient and source data on a common neighborhood have one signed
spatial difference-quotient bound on a compact reverse-time carrier. -/
theorem IsCompact.exists_reverseTimeSpatialDifferenceQuotient_bounds_of_smoothOnNeighborhood
     {S K : HypoellipticAleksandrov.Parabolic.Region d}
    (hS : IsCompact S) (r₁ : ℝ)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (hSK : reverseTimeMap r₁ '' S ⊆ K)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2) K)
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2) K)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2) K)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2) K) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      (∀ (i j k : Fin d) (h : ℝ) (z : TimeVelocity d),
        |h| ≤ δ → z ∈ S →
          |spatialDifferenceQuotient k h
            (fun z  =>
              reverseTimeCoefficient r₁ a z.1 z.2 i j) z| ≤ C) ∧
      (∀ (j k : Fin d) (h : ℝ) (z : TimeVelocity d),
        |h| ≤ δ → z ∈ S →
          |spatialDifferenceQuotient k h
            (fun z  =>
              reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) z| ≤ C) ∧
      (∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d),
        |h| ≤ δ → z ∈ S →
          |spatialDifferenceQuotient k h
            (fun z  =>
              reverseTimeScalarCoefficient r₁ c z.1 z.2) z| ≤ C) ∧
      (∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d),
        |h| ≤ δ → z ∈ S →
          |spatialDifferenceQuotient k h
            (fun z  =>
              reverseTimeScalarCoefficient r₁ F z.1 z.2) z| ≤ C) := (Exists.casesOn
  (exists_common_spatialDifferenceQuotient_bound_of_smoothOnNeighborhood hS
    (fun x z =>
      match x with
      | Sum.inl (i, j) => reverseTimeCoefficient r₁ a z.1 z.2 i j
      | Sum.inr (Sum.inl j) => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
      | Sum.inr (Sum.inr false) => reverseTimeScalarCoefficient r₁ c z.1 z.2
      | Sum.inr (Sum.inr true) => reverseTimeScalarCoefficient r₁ F z.1 z.2)
    fun x =>
    Sum.casesOn x
      (fun x =>
        Prod.casesOn x fun i j =>
          id (IsSmoothOnNeighborhood.reverseTime r₁ hSK (IsSmoothOnNeighborhood.coefficientEntry a ha i j)))
      fun x =>
      Sum.casesOn x
        (fun x =>
          id (IsSmoothOnNeighborhood.reverseTime r₁ hSK (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb x)))
        fun x =>
        Bool.casesOn x (id (IsSmoothOnNeighborhood.reverseTime r₁ hSK hc))
          (id (IsSmoothOnNeighborhood.reverseTime r₁ hSK hF)))
  fun δ h =>
  Exists.casesOn h fun C h =>
    And.casesOn h fun hδ right =>
      And.casesOn right fun hC hqbound =>
        Exists.intro δ
          (Exists.intro C
            ⟨hδ,
              ⟨hC,
                ⟨fun i j k h z hh hz => hqbound (Sum.inl (i, j)) k h z hh hz,
                  ⟨fun j k h z hh hz => hqbound (Sum.inr (Sum.inl j)) k h z hh hz,
                    ⟨fun k h z hh hz => hqbound (Sum.inr (Sum.inr false)) k h z hh hz, fun k h z hh hz =>
                      hqbound (Sum.inr (Sum.inr true)) k h z hh hz⟩⟩⟩⟩⟩))

/-- Smooth reverse-time data have one raw signed-step amplitude bound and one
spatial collar on the full closed reverse-time slab over a compact cutoff
carrier. -/
theorem exists_reverseTimeSpatialRawAmplitude_bounds_of_smoothOnNeighborhood
     {Ω inner : PDE.VelocityRegion d} {Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (χ : PDE.QuantitativeSmoothCutoff inner Ω Kχ)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        Set.MapsTo
          (fun y  => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω) ∧
      (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
        |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
          y ∈ tsupport χ.toFun →
            |spatialDifferenceQuotient k h
              (fun z  => F (r₁ - z.1) z.2) (τ, y)| ≤ C) ∧
      (∀ (i j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
        |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
          y ∈ tsupport χ.toFun →
            |spatialDifferenceQuotient k h
              (fun z  =>
                reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)| ≤ C) ∧
      (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
        |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
          y ∈ tsupport χ.toFun →
            |spatialTranslate k h
              (fun z  =>
                reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ C) ∧
      (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
        |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
          y ∈ tsupport χ.toFun →
            |spatialDifferenceQuotient k h
              (fun z  =>
                reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ C) ∧
      (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
        |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
          y ∈ tsupport χ.toFun →
            |spatialTranslate k h
              (fun z  =>
                reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ C) ∧
      (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
        |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
          y ∈ tsupport χ.toFun →
            |spatialDifferenceQuotient k h
              (fun z  =>
                reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ C) := by
  let S  := Set.Icc 0 (r₁ - r₀) ×ˢ tsupport χ.toFun
  have hS : IsCompact S :=
    isCompact_Icc.prod χ.hasCompactSupport.isCompact
  have hSK : reverseTimeMap r₁ '' S ⊆ scalarParabolicClosedCylinder r₀ r₁ Ω := by
    rintro w ⟨z, hz, rfl⟩
    rcases hz with ⟨hτ, hy⟩
    rw [mem_scalarParabolicClosedCylinder_iff]
    refine ⟨?_, ?_, subset_closure (χ.tsupport_subset hy)⟩
    · simp only [reverseTimeMap_apply]
      linarith [hτ.2]
    · simp only [reverseTimeMap_apply]
      linarith [hτ.1]
  obtain ⟨δDQ, CDQ, hδDQ, hCDQ, hmatrixDQ, hdriftDQ, hscalarDQ, hsourceDQ⟩ :=
    IsCompact.exists_reverseTimeSpatialDifferenceQuotient_bounds_of_smoothOnNeighborhood hS
      r₁ a b c F hSK ha hb hc hF
  let q : Fin d ⊕ Unit → HypoellipticAleksandrov.Parabolic.ScalarField d := fun x z =>
    match x with
    | Sum.inl j => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
    | Sum.inr () => reverseTimeScalarCoefficient r₁ c z.1 z.2

  obtain ⟨δT, CT, hδT, _hCT, htranslate⟩ :=
    exists_common_spatialTranslate_bound_of_smoothOnNeighborhood hS q (show ∀ x, IsSmoothOnNeighborhood (q x) S by
        intro x
        rcases x with j | x
        · change IsSmoothOnNeighborhood
            ((fun z  =>
              scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j) ∘ reverseTimeMap r₁) S
          exact IsSmoothOnNeighborhood.reverseTime r₁ hSK
            (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)
        · rcases x with ⟨⟩
          change IsSmoothOnNeighborhood
            ((fun z : TimeVelocity d => c z.1 z.2) ∘ reverseTimeMap r₁) S
          exact IsSmoothOnNeighborhood.reverseTime r₁ hSK hc)
  let K  := ({0} : Set ℝ) ×ˢ tsupport χ.toFun
  let U : HypoellipticAleksandrov.Parabolic.Region d := Set.univ ×ˢ Ω



  obtain ⟨δχ, hδχ, _hχthickening, hcollar⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar (show IsCompact K by
        exact isCompact_singleton.prod χ.hasCompactSupport.isCompact) (show IsOpen U by
        exact isOpen_univ.prod hΩ) (show K ⊆ U by
        intro z hz
        exact ⟨by simp, χ.tsupport_subset hz.2⟩)
  refine ⟨min δχ (min δDQ δT), max CDQ CT,
    lt_min hδχ (lt_min hδDQ hδT),
    hCDQ.trans (le_max_left _ _), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h hh y hy
    have hz := hcollar k h (hh.trans (min_le_left _ _)) (show (0, y) ∈ K from
      ⟨by simp, hy⟩)
    exact hz.2
  · intro k h τ y hh hτ hy
    exact (hsourceDQ k h (τ, y)
      (hh.trans (min_le_right _ _ |>.trans (min_le_left _ _))) ⟨hτ, hy⟩).trans
        (le_max_left _ _)
  · intro i j k h τ y hh hτ hy
    exact (hmatrixDQ i j k h (τ, y)
      (hh.trans (min_le_right _ _ |>.trans (min_le_left _ _))) ⟨hτ, hy⟩).trans
        (le_max_left _ _)
  · intro j k h τ y hh hτ hy
    exact (htranslate (Sum.inl j) k h (τ, y)
      (hh.trans (min_le_right _ _ |>.trans (min_le_right _ _))) ⟨hτ, hy⟩).trans
        (le_max_right _ _)
  · intro j k h τ y hh hτ hy
    exact (hdriftDQ j k h (τ, y)
      (hh.trans (min_le_right _ _ |>.trans (min_le_left _ _))) ⟨hτ, hy⟩).trans
        (le_max_left _ _)
  · intro k h τ y hh hτ hy
    exact (htranslate (Sum.inr ()) k h (τ, y)
      (hh.trans (min_le_right _ _ |>.trans (min_le_right _ _))) ⟨hτ, hy⟩).trans
        (le_max_right _ _)
  · intro k h τ y hh hτ hy
    exact (hscalarDQ k h (τ, y)
      (hh.trans (min_le_right _ _ |>.trans (min_le_left _ _))) ⟨hτ, hy⟩).trans
        (le_max_left _ _)

end HypoellipticAleksandrov.Parabolic.Dirichlet
