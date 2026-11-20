module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10NonprincipalRemainderDefinition
public import HypoellipticAleksandrov.Parabolic.Dirichlet.NestedCutoffLocality
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import PDEFoundation.Sobolev.Cutoff.Basic
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialRawAmplitudeMajorant
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SixTermYoung
public import HypoellipticAleksandrov.Topology.Support
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeCutoffSlice
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
/-!
# Raw nonprincipal localized commutator remainder
This module isolates the six non-translated-principal fixed-time commutator
terms and proves their uniform Young bound from the smooth data.
-/
@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
section
variable {d : ℕ}

private theorem norm_cutoff_mul_le_of_tsupport_bound {Ω inner : Set (PDE.Vec d)} {K C : ℝ}
    (β : PDE.QuantitativeSmoothCutoff inner Ω K) (q : PDE.Vec d → ℝ)
    (hC : 0 ≤ C) (hq : ∀ y ∈ tsupport β.toFun, ‖q y‖ ≤ C) :
    ∀ y, ‖β y * q y‖ ≤ C := by
  intro y
  by_cases hy : β y = 0
  · simp [hy, hC]
  · have hys := subset_tsupport β.toFun hy
    calc
      ‖β y * q y‖ = ‖β y‖ * ‖q y‖ := norm_mul _ _
      _ ≤ 1 * C := mul_le_mul
        (β.norm_le_one y)
        (hq y hys) (norm_nonneg _) zero_le_one
      _ = C := one_mul _
private theorem norm_gradientCLM_le_graph {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : H10HilbertGraph hΩ) :
    ‖gradientCLM hΩ u‖ ≤ ‖u‖ := by
  let z : PDE.H1HilbertAmbient Ω := (u : PDE.H1HilbertGraph Ω).1
  change ‖z.snd‖ ≤ ‖z‖
  exact WithLp.norm_snd_le _ z
private theorem abs_sum_fin_le (f : Fin d → ℝ) (M : ℝ)
    (hf : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ (Fintype.card (Fin d) : ℝ) * M := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, M := by gcongr with i; exact hf i
    _ = (Fintype.card (Fin d) : ℝ) * M := by simp
private theorem abs_sum_fin_fin_le (f : Fin d → Fin d → ℝ) (M : ℝ)
    (hf : ∀ i j, |f i j| ≤ M) :
    |∑ i, ∑ j, f i j| ≤ (Fintype.card (Fin d) : ℝ) ^ 2 * M := by
  calc
    |∑ i, ∑ j, f i j| ≤ ∑ i, |∑ j, f i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |f i j| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hf i j
    _ = (Fintype.card (Fin d) : ℝ) ^ 2 * M := by simp; ring
private theorem abs_source_pairing_le_sq_add {Ω : Set (PDE.Vec d)} (sourceLp V : PDE.ScalarLp Ω 2)
    (source : PDE.Vec d → ℝ) (n S : ℝ)
    (hs : ⇑sourceLp =ᵐ[PDE.volumeOn Ω] source) (hV : ‖V‖ ≤ n) (hS : ‖sourceLp‖ ^ 2 ≤ S) :
    |∫ y in Ω, source y * V y| ≤ S + n ^ 2 := by
  rw [Analysis.integral_mul_eq_inner_L2 hs.symm (Filter.EventuallyEq.rfl : _ =ᵐ[PDE.volumeOn Ω] V)]
  nlinarith only [((abs_real_inner_le_norm sourceLp V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))), hS, sq_nonneg (‖sourceLp‖ - n), sq_nonneg ‖sourceLp‖, sq_nonneg n]

end

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)}

private theorem abs_source_fixedSlice_le_sq_add {Kη Kχ C : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (δ : ℝ) (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : χ.ShiftMapsInto k h Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ)
    (hsourceRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
        y ∈ tsupport χ.toFun →
          |spatialDifferenceQuotient k h
            (fun z : TimeVelocity d => F (r₁ - z.1) z.2) (τ, y)| ≤ C) :
    |∫ y in Ω,
        (η y * spatialDifferenceQuotient k h
          (fun z : TimeVelocity d => F (r₁ - z.1) z.2) (τ, y)) *
          valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset
              (hχshift.mono_left (χ.inner_subset_tsupport)) u) y ∂volume| ≤
      C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun) + ‖u‖ ^ 2 := by
  let hηχ := χ.inner_subset_tsupport
  let hηshift : η.ShiftMapsInto k h Ω := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ (A u)
  let sourceD : PDE.Vec d → ℝ := fun y =>
    η y * spatialDifferenceQuotient k h (fun z : TimeVelocity d => F (r₁ - z.1) z.2) (τ, y)
  have hsourceDCont : Continuous sourceD := by
    dsimp only [sourceD]
    simpa only [one_mul] using
      (cutoffSlice_translate_quotient η k h 1 (r₀ := r₀) (r₁ := r₁)
        (IsSmoothOnNeighborhood.reverseTimeClosedCylinder hF) hτ hηshift).2.1
  have hsourceDBound : ∀ y, ‖sourceD y‖ ≤ C := by
    apply norm_cutoff_mul_le_of_tsupport_bound η _ hC
    intro y hy
    simpa only [Real.norm_eq_abs, sourceD] using hsourceRaw k h τ y hh hτ (hηχ hy)
  have hsourceDSupp : tsupport sourceD ⊆ tsupport χ.toFun :=
    (tsupport_mul_subset_left).trans hηχ
  have hsourceDCompact : HasCompactSupport sourceD :=
    χ.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _) hsourceDSupp
  let sourceLp : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    compactlySupportedContinuousToScalarLp (Ω := Ω) sourceD hsourceDCont hsourceDCompact
  have hsourceLpAE : ⇑sourceLp =ᵐ[PDE.volumeOn Ω] sourceD := by
    dsimp [sourceLp]
    exact coeFn_compactlySupportedContinuousToScalarLp _ hsourceDCont hsourceDCompact
  have hsourceSq : ‖sourceLp‖ ^ 2 ≤
      C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun) := by
    dsimp [sourceLp]
    have hqcompact :=
      χ.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport sourceD) hsourceDSupp
    have hqae := coeFn_compactlySupportedContinuousToScalarLp (Ω := Ω) sourceD hsourceDCont hqcompact
    have henergy := PDE.integral_sq_eq_sq_norm_of_ae_eq
      (compactlySupportedContinuousToScalarLp (Ω := Ω) sourceD hsourceDCont hqcompact) sourceD hqae
    rw [← henergy]
    exact integral_sq_le_mul_volumeOn_of_tsupport_subset sourceD hsourceDCont χ.hasCompactSupport.isCompact hsourceDSupp C hsourceDBound
  have hVNorm : ‖V‖ ≤ ‖u‖ := by
    calc
      ‖V‖ ≤ ‖gradientCLM hΩ u‖ := by
        dsimp [V, A]
        exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
          hΩ η k h η.tsupport_subset hηshift u
      _ ≤ ‖u‖ := norm_gradientCLM_le_graph hΩ u
  exact abs_source_pairing_le_sq_add sourceLp V sourceD ‖u‖
    (C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun)) hsourceLpAE hVNorm hsourceSq
/-- The nonprincipal localized commutator remainder has a constant fixed
before the coefficient data, under the literal uniform spatial majorants of
the Caccioppoli estimate. -/
theorem exists_uniform_nonprincipalRemainder_bound_of_majorants {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (δ M : ℝ) (hM : 0 ≤ M)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧
      ∀ (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ),
        ∀ (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
          (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
          (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
          (hF : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
          (hbound : ReverseTimeCoefficientMajorant r₀ r₁ (tsupport χ.toFun) δ M a b c F),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ),
          ∀ (τ : ℝ), τ ∈ Set.Icc 0 (r₁ - r₀) →
            ∀ u : H10HilbertGraph hΩ,
              let hχshift : χ.ShiftMapsInto k h Ω :=
                mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
                  hcarrier k hh
              let hηχ := χ.inner_subset_tsupport
              let hηshift : η.ShiftMapsInto k h Ω := hχshift.mono_left hηχ
              let A := localizedSpatialDifferenceQuotientH10CLM
                hΩ η k h η.tsupport_subset hηshift
              |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
                  r₁ hΩ a b c F η χ k h τ hηshift u| ≤
                ε * ‖gradientCLM hΩ (A u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2) := by
  let D : ℝ := Fintype.card (Fin d)
  let S := M ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun)
  let B := (D ^ 2 + D) * M
  let C₀ := 1 + B * Kη + (D + 2) * M
  have hK := η.gradient_bound_nonneg
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀, D]; positivity
  have hQ : 0 ≤ B ^ 2 / (4 * ε) := by positivity
  refine ⟨S + C₀ + B ^ 2 / (4 * ε), by positivity, ?_⟩
  intro a b c F ha hb hc hF hbound k h hh τ hτ u
  obtain ⟨_, hsource, haD, hbT, hbD, hcT, hcD⟩ :=
    reverseTimeSpatialRawAmplitude_bounds_of_majorants r₀ r₁ χ δ M hcarrier
      a b c F ha hb hc hF hbound
  let hχ : χ.ShiftMapsInto k h Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hη : η.ShiftMapsInto k h Ω := hχ.mono_left χ.inner_subset_tsupport
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hη
  let n := ‖u‖
  let g := ‖gradientCLM hΩ (A u)‖
  let V := valueCLM hΩ (A u)
  let G (i : Fin d) := PDE.hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ (A u))
  let W (i : Fin d) := cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u)
  let U (j : Fin d) := PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)
  let U₀ := valueCLM hΩ u
  have hG (i : Fin d) : ‖G i‖ ≤ g := PDE.norm_hilbertVectorLpCoord_le i _
  have hUn (i : Fin d) : ‖U i‖ ≤ n := (PDE.norm_hilbertVectorLpCoord_le i _).trans (norm_gradientCLM_le_graph hΩ u)
  have hU₀ : ‖U₀‖ ≤ n := WithLp.norm_fst_le _ (u : PDE.H1HilbertGraph Ω).1
  have hV : ‖V‖ ≤ n :=
    (norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
      hΩ η k h η.tsupport_subset hη u).trans (norm_gradientCLM_le_graph hΩ u)
  have hW (i : Fin d) : ‖W i‖ ≤ Kη * n :=
    (norm_cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_le_gradient
      hΩ η χ subset_rfl i k h χ.tsupport_subset hχ u).trans
      (mul_le_mul_of_nonneg_left (norm_gradientCLM_le_graph hΩ u) hK)
  have hH (i : Fin d) : ‖G i + W i‖ ≤ g + Kη * n :=
    (norm_add_le _ _).trans (add_le_add (hG i) (hW i))
  have hE (i : Fin d) : ‖G i - W i‖ ≤ g + Kη * n :=
    (norm_sub_le _ _).trans (add_le_add (hG i) (hW i))
  let aD (i j : Fin d) (y : PDE.Vec d) := spatialDifferenceQuotient k h
    (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)
  let bT (j : Fin d) (y : PDE.Vec d) := spatialTranslate k h
    (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  let bD (j : Fin d) (y : PDE.Vec d) := spatialDifferenceQuotient k h
    (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  let cT (y : PDE.Vec d) := spatialTranslate k h (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  let cD (y : PDE.Vec d) := spatialDifferenceQuotient k h (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  let s := ∫ y in Ω, (η y * spatialDifferenceQuotient k h (fun z => F (r₁ - z.1) z.2) (τ, y)) * V y
  let P := ∑ i, ∑ j, ∫ y in Ω, (χ y * aD i j y) * (η y * U j y) * (G i y + W i y)
  let T := ∑ j, ∫ y in Ω, (χ y * bT j y) * (G j y - W j y) * V y
  let L := ∑ j, ∫ y in Ω, (χ y * bD j y) * (η y * U j y) * V y
  let R := ∫ y in Ω, (χ y * cT y) * V y * V y
  let Q := ∫ y in Ω, (χ y * cD y) * (η y * U₀ y) * V y
  have hpair {q f₁ f₂ : PDE.Vec d → ℝ} {X Y : PDE.ScalarLp Ω 2} {x y : ℝ}
      (hq : ∀ z ∈ tsupport χ.toFun, |q z| ≤ M)
      (h₁ : f₁ =ᵐ[PDE.volumeOn Ω] X) (h₂ : f₂ =ᵐ[PDE.volumeOn Ω] Y)
      (hx : ‖X‖ ≤ x) (hy : ‖Y‖ ≤ y) :
      |∫ z in Ω, (χ z * q z) * f₁ z * f₂ z| ≤ M * x * y := by
    refine (Analysis.abs_integral_weighted_mul_le_L2 hM (Filter.Eventually.of_forall ?_) h₁ h₂).trans ?_
    · simpa only [Real.norm_eq_abs] using norm_cutoff_mul_le_of_tsupport_bound χ q hM
        (fun z hz => by simpa only [Real.norm_eq_abs] using hq z hz)
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hx hM) hy (norm_nonneg _)
        (mul_nonneg hM ((norm_nonneg _).trans hx))
  have hpairη {q f₂ : PDE.Vec d → ℝ} {X Y : PDE.ScalarLp Ω 2} {x y : ℝ}
      (hq : ∀ z ∈ tsupport χ.toFun, |q z| ≤ M) (h₂ : f₂ =ᵐ[PDE.volumeOn Ω] Y)
      (hx : ‖X‖ ≤ x) (hy : ‖Y‖ ≤ y) :
      |∫ z in Ω, (χ z * q z) * (η z * X z) * f₂ z| ≤ M * x * y := by
    have hqη (z) (hz : z ∈ tsupport χ.toFun) : |q z * η z| ≤ M := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (η.norm_le_one z) (abs_nonneg (q z))).trans
        (by simpa only [mul_one] using hq z hz)
    simpa only [mul_assoc] using hpair hqη Filter.EventuallyEq.rfl h₂ hx hy
  have hs : |s| ≤ S + n ^ 2 :=
    abs_source_fixedSlice_le_sq_add r₀ r₁ hΩ F hF η χ δ hM k h hh hχ τ hτ u hsource
  have hp : |P| ≤ D ^ 2 * (M * n * (g + Kη * n)) := by
    apply abs_sum_fin_fin_le
    intro i j
    exact hpairη (fun z hz => haD i j k h τ z hh hτ hz) (Lp.coeFn_add (G i) (W i)).symm (hUn j) (hH i)
  have ht : |T| ≤ D * (M * (g + Kη * n) * n) := by
    apply abs_sum_fin_le
    intro j
    exact hpair (fun z hz => hbT j k h τ z hh hτ hz) (Lp.coeFn_sub (G j) (W j)).symm
      Filter.EventuallyEq.rfl (hE j) hV
  have hl : |L| ≤ D * (M * n * n) := by
    apply abs_sum_fin_le
    intro j
    exact hpairη (fun z hz => hbD j k h τ z hh hτ hz) Filter.EventuallyEq.rfl (hUn j) hV
  have hr : |R| ≤ M * n * n :=
    hpair (fun z hz => hcT k h τ z hh hτ hz) Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl hV hV
  have hq : |Q| ≤ M * n * n :=
    hpairη (fun z hz => hcD k h τ z hh hτ hz) Filter.EventuallyEq.rfl hU₀ hV
  change |-s - P - T - L + R + Q| ≤ ε * g ^ 2 + _
  calc
    _ ≤ S + C₀ * n ^ 2 + B * g * n := by
      refine (abs_six_terms_le s P T L R Q).trans ?_
      dsimp only [C₀, B]
      nlinarith only [hs, hp, ht, hl, hr, hq]
    _ ≤ _ := by
      have h := young_eps ε B g n hε
      nlinarith only [h, hS, hC₀, hQ, mul_nonneg hS (sq_nonneg n)]

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
