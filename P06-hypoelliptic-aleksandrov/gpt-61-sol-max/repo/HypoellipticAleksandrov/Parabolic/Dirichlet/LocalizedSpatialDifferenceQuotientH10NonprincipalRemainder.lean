module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10NonprincipalRemainderDefinition
public import HypoellipticAleksandrov.Parabolic.Dirichlet.NestedCutoffLocality
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialDifferenceQuotientBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialRawAmplitudeMajorant
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SixTermYoung
public import HypoellipticAleksandrov.Topology.Support
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Bound
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds

open private HypoellipticAleksandrov.Parabolic.Dirichlet.abs_principal_multiplierInner_le from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
open private HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
open private HypoellipticAleksandrov.Parabolic.Dirichlet.inner_scalarLp_eq_setIntegral_of_ae_eq from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator

/-!
# Raw nonprincipal localized commutator remainder
This module isolates the six non-translated-principal fixed-time commutator
terms and proves their uniform Young bound from the smooth data.
-/
@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ}

private theorem inner_scalarL2Multiplier_eq_setIntegral
     {Ω : PDE.VelocityRegion d}
    (q : PDE.ScalarField d) (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 )) :
    inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g =
      ∫ y in Ω, q y * f y * g y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarL2Multiplier_apply_ae q hq C hC hqBound f] with y hy
  rw [hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring
section
variable {Ω inner : PDE.VelocityRegion d} {K : ℝ} (r₀ r₁ τ : ℝ) (β : PDE.QuantitativeSmoothCutoff inner Ω K) (k : Fin d) (h : ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : IsSmoothOnNeighborhood f (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω)) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (hβshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport β.toFun) Ω)

include hf hτ hβshift
private theorem continuous_cutoff_spatialDifferenceQuotient_slice
      :
    Continuous (fun y => β y * spatialDifferenceQuotient k h f (τ, y)) := by
  rcases hf with ⟨V, hVopen, hSV, hV⟩
  let g₀ : PDE.Vec d → TimeVelocity d := fun y => (τ, y)
  let g₁  := fun y => (τ, y + h • PDE.basisVec k)
  let U  := g₀ ⁻¹' V ∩ g₁ ⁻¹' V
  have hg₀ : Continuous g₀ := by
    exact continuous_const.prodMk continuous_id
  have hg₁ : Continuous g₁ := by
    exact continuous_const.prodMk (continuous_id.add continuous_const)



  have hf₁ : ContinuousOn (fun y => f (τ, y + h • PDE.basisVec k)) U := by
    exact hV.continuousOn.comp hg₁.continuousOn fun y hy => hy.2

  exact HypoellipticAleksandrov.continuous_mul_of_tsupport_subset ((hg₀.isOpen_preimage V hVopen).inter (hg₁.isOpen_preimage V hVopen))
    β.smooth.continuous.continuousOn (by
        intro y hy
        constructor
        · exact hSV ⟨hτ, subset_closure (β.tsupport_subset hy)⟩
        · exact hSV ⟨hτ, subset_closure (hβshift hy)⟩) (by
        simpa only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
          spatialShift_apply, Pi.sub_def] using (hf₁.sub (by
              exact hV.continuousOn.comp hg₀.continuousOn fun y hy => hy.1)).div_const h)
private theorem continuous_cutoff_spatialTranslate_slice
      :
    Continuous (fun y => β y * spatialTranslate k h f (τ, y)) := by
  rcases hf with ⟨V, hVopen, hSV, hV⟩
  let g  := fun y => (τ, y + h • PDE.basisVec k)
  let U  := g ⁻¹' V
  have hg : Continuous g := by
    exact continuous_const.prodMk (continuous_id.add continuous_const)



  exact HypoellipticAleksandrov.continuous_mul_of_tsupport_subset (hg.isOpen_preimage V hVopen)
    β.smooth.continuous.continuousOn (by
        intro y hy
        exact hSV ⟨hτ, subset_closure (hβshift hy)⟩) (by
        simp only [spatialTranslate_apply, spatialShift_apply]
        change ContinuousOn (f ∘ g) U
        exact hV.continuousOn.comp hg.continuousOn (show MapsTo g U V from fun _ hy => hy))
end

variable {Ω : PDE.VelocityRegion d} (r₀ r₁ : ℝ)

private theorem reverseTimeMap_image_closedCylinder_subset
      :
    reverseTimeMap r₁ '' (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
  rintro w ⟨z, hz, rfl⟩
  rcases hz with ⟨hτ, hy⟩
  rw [mem_scalarParabolicClosedCylinder_iff]
  refine ⟨?_, ?_, hy⟩
  · simp only [reverseTimeMap_apply]
    linarith [hτ.2]
  · simp only [reverseTimeMap_apply]
    linarith [hτ.1]
private theorem reverseTime_source_smoothOn_closedCylinder

    (F : PDE.TimeScalarField d)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F (r₁ - z.1) z.2)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := (id (IsSmoothOnNeighborhood.reverseTime r₁ (reverseTimeMap_image_closedCylinder_subset r₀ r₁) hF))
variable (a : CoefficientField d)

private theorem reverseTime_coefficient_smoothOn_closedCylinder


    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (i j : Fin d) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := (id
  (IsSmoothOnNeighborhood.reverseTime r₁ (reverseTimeMap_image_closedCylinder_subset r₀ r₁)
    (IsSmoothOnNeighborhood.coefficientEntry a ha i j)))
private theorem reverseTime_drift_smoothOn_closedCylinder

     (b : PDE.TimeVectorField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (j : Fin d) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := (id
  (IsSmoothOnNeighborhood.reverseTime r₁ (reverseTimeMap_image_closedCylinder_subset r₀ r₁)
    (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)))
private theorem reverseTime_scalar_smoothOn_closedCylinder

    (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := (reverseTime_source_smoothOn_closedCylinder r₀ r₁ c hc)
variable {Ω inner : PDE.VelocityRegion d}

private theorem norm_cutoff_mul_le_of_tsupport_bound
      {K C : ℝ}
    (β : PDE.QuantitativeSmoothCutoff inner Ω K) (q : PDE.ScalarField d)
    (hC : 0 ≤ C) (hq : ∀ y ∈ tsupport β.toFun, ‖q y‖ ≤ C) :
    ∀ y, ‖β y * q y‖ ≤ C := by
  intro y
  by_cases hy : β y = 0
  · simp [hy, hC]
  ·
    calc
      ‖β y * q y‖ = ‖β y‖ * ‖q y‖ := norm_mul _ _
      _ ≤ 1 * C := mul_le_mul
        (by
          rw [Real.norm_eq_abs, abs_of_nonneg (β.nonneg y)]
          exact β.le_one y)
        (hq y (subset_tsupport β.toFun hy)) (norm_nonneg _) zero_le_one
      _ = C := one_mul _
private theorem tsupport_cutoff_mul_subset
      {K : ℝ}
    (β : PDE.QuantitativeSmoothCutoff inner Ω K) (q : PDE.ScalarField d) :
  tsupport (fun y => β y * q y) ⊆ tsupport β.toFun :=
  tsupport_mul_subset_left
private theorem sq_norm_compactlySupportedContinuousToScalarLp_le
     {Ω K : PDE.VelocityRegion d}
    (q : PDE.ScalarField d) (hq : Continuous q) (hK : IsCompact K)
    (hqK : tsupport q ⊆ K) (C : ℝ) (hqC : ∀ y, ‖q y‖ ≤ C) :
    ‖compactlySupportedContinuousToScalarLp (Ω := Ω) q hq
      (hK.of_isClosed_subset (isClosed_tsupport q) hqK)‖ ^ 2 ≤
      C ^ 2 * (PDE.volumeOn Ω).real K := by


  have henergy := PDE.integral_sq_eq_sq_norm_of_ae_eq
    _ q (coeFn_compactlySupportedContinuousToScalarLp (Ω := Ω) q hq (hK.of_isClosed_subset (isClosed_tsupport q) hqK))
  rw [← henergy]
  exact integral_sq_le_mul_volumeOn_of_tsupport_subset q hq hK hqK C hqC
variable {Ω : PDE.VelocityRegion d}



variable (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ)

private theorem norm_valueCLM_le_graph
       :
    ‖valueCLM hΩ u‖ ≤ ‖u‖ := by
  let z  := (u : PDE.H1HilbertGraph Ω).1
  change ‖z.fst‖ ≤ ‖z‖
  exact WithLp.norm_fst_le _ z
private theorem norm_gradientCLM_le_graph
       :
    ‖gradientCLM hΩ u‖ ≤ ‖u‖ := by
  let z  := (u : PDE.H1HilbertGraph Ω).1
  change ‖z.snd‖ ≤ ‖z‖
  exact WithLp.norm_snd_le _ z
variable (q : PDE.ScalarField d) (hq : AEStronglyMeasurable q (PDE.volumeOn Ω)) (C : ℝ) (hC : 0 ≤ C) (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C) (f g : PDE.ScalarLp Ω (2 ))



include hq hC hqBound in
private theorem abs_setIntegral_mul_mul_le

     (p r : PDE.ScalarField d)
    (hf : ⇑f =ᵐ[PDE.volumeOn Ω] p) (hg : ⇑g =ᵐ[PDE.volumeOn Ω] r) :
    |∫ y in Ω, (q y * p y) * r y| ≤ C * ‖f‖ * ‖g‖ := by
  have heq : (∫ y in Ω, (q y * p y) * r y) =
      inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g := by
    rw [inner_scalarL2Multiplier_eq_setIntegral]
    apply integral_congr_ae
    filter_upwards [hf, hg] with y hyf hyg
    rw [hyf, hyg]
  rw [heq]
  exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.abs_principal_multiplierInner_le q hq C hC hqBound f g
variable (f g : PDE.ScalarLp Ω (2 ))



private theorem abs_inner_scalarLp_le

     :
    |Inner.inner ℝ f g| ≤ ‖f‖ * ‖g‖ :=
  abs_real_inner_le_norm f g
private theorem mul_le_mul_left_nonneg (a b c : ℝ)
    (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left hbc ha
variable {d : ℕ}

private theorem abs_source_pairing_le_sq_add
     {Ω : PDE.VelocityRegion d}
    (sourceLp V : PDE.ScalarLp Ω (2 ))
    (source : PDE.ScalarField d) (n S : ℝ)
    (hsource : ⇑sourceLp =ᵐ[PDE.volumeOn Ω] source)
    (hV : ‖V‖ ≤ n) (hsq : ‖sourceLp‖ ^ 2 ≤ S) :
    |∫ y in Ω, source y * V y| ≤ S + n ^ 2 := by
  have hinner  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.inner_scalarLp_eq_setIntegral_of_ae_eq sourceLp V source _
      hsource (Filter.Eventually.of_forall fun _ => rfl)
  calc
    |∫ y in Ω, source y * V y| = |Inner.inner ℝ sourceLp V| := by rw [hinner]
    _ ≤ ‖sourceLp‖ * ‖V‖ := abs_inner_scalarLp_le sourceLp V
    _ ≤ ‖sourceLp‖ * n := mul_le_mul_left_nonneg _ _ _ hV (norm_nonneg _)
    _ ≤ S + n ^ 2 := by nlinarith [sq_nonneg (‖sourceLp‖ - n)]
private theorem abs_sum_fin_le
     (f : Fin d → ℝ) (M : ℝ)
    (hf : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ (Fintype.card (Fin d) : ℝ) * M := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, M := by gcongr with i; exact hf i
    _ = (Fintype.card (Fin d) : ℝ) * M := by simp
private theorem abs_sum_fin_fin_le
     (f : Fin d → Fin d → ℝ) (M : ℝ)
    (hf : ∀ i j, |f i j| ≤ M) :
    |∑ i, ∑ j, f i j| ≤ (Fintype.card (Fin d) : ℝ) ^ 2 * M := by
  calc
    |∑ i, ∑ j, f i j| ≤ ∑ i, |∑ j, f i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |f i j| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, M := by
      bound
    _ = (Fintype.card (Fin d) : ℝ) ^ 2 * M := by simp; ring
private theorem abs_multiplier_pairing_le
     {Ω : PDE.VelocityRegion d}
    (q : PDE.ScalarField d) (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C N M : ℝ) (hC : 0 ≤ C)
    (hqC : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 )) (p r : PDE.ScalarField d)
    (hf : ⇑f =ᵐ[PDE.volumeOn Ω] p) (hg : ⇑g =ᵐ[PDE.volumeOn Ω] r)
    (hfn : ‖f‖ ≤ N) (hgm : ‖g‖ ≤ M) (hN : 0 ≤ N) (_hM : 0 ≤ M) :
    |∫ y in Ω, (q y * p y) * r y| ≤ C * N * M := by
  calc
    _ ≤ C * ‖f‖ * ‖g‖ := abs_setIntegral_mul_mul_le q hq C hC hqC f g p r hf hg
    _ ≤ (C * N) * M := mul_le_mul (mul_le_mul_of_nonneg_left hfn hC) hgm
        (norm_nonneg _) (mul_nonneg hC hN)
    _ = _ := by ring
variable {Ω inner : PDE.VelocityRegion d}

private theorem abs_source_fixedSlice_le_sq_add
      {Kη Kχ C : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (F : PDE.TimeScalarField d)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (δ : ℝ) (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ)
    (hsourceRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) →
        y ∈ tsupport χ.toFun →
          |spatialDifferenceQuotient k h
            (fun z  => F (r₁ - z.1) z.2) (τ, y)| ≤ C) :
    |∫ y in Ω,
        (η y * spatialDifferenceQuotient k h
          (fun z  => F (r₁ - z.1) z.2) (τ, y)) *
          valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset
              (hχshift.mono_left (by
                intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy])) u) y| ≤
      C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun) + ‖u‖ ^ 2 := by
  let sharedTerm_143b633510 := ((fun z : TimeVelocity d => F (r₁ - z.1) z.2))
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]
  let hηshift  := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let sourceD  := fun y =>
    η y * spatialDifferenceQuotient k h sharedTerm_143b633510 (τ, y)
  have hsourceDCont : Continuous sourceD := by
    dsimp [sourceD]
    exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ η k h
      sharedTerm_143b633510
      (reverseTime_source_smoothOn_closedCylinder r₀ r₁ F hF) hτ hηshift

  have hsourceDSupp : tsupport sourceD ⊆ tsupport χ.toFun :=
    (tsupport_cutoff_mul_subset η _).trans hηχ
  have hsourceDCompact  :=
    χ.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _) hsourceDSupp
  let sourceLp : PDE.ScalarLp Ω (2 ) :=
    compactlySupportedContinuousToScalarLp  sourceD hsourceDCont hsourceDCompact



  exact abs_source_pairing_le_sq_add sourceLp V sourceD ‖u‖
    _ ((id (coeFn_compactlySupportedContinuousToScalarLp sourceD hsourceDCont hsourceDCompact))) (by
        calc
          ‖V‖ ≤ ‖gradientCLM hΩ u‖ := by
            dsimp [V, A]
            exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
              hΩ η k h η.tsupport_subset hηshift u
          _ ≤ ‖u‖ := norm_gradientCLM_le_graph hΩ u) (by
        dsimp [sourceLp]
        exact sq_norm_compactlySupportedContinuousToScalarLp_le sourceD hsourceDCont
          χ.hasCompactSupport.isCompact hsourceDSupp C (by
              apply norm_cutoff_mul_le_of_tsupport_bound η _ hC
              intro y hy
              exact hsourceRaw k h τ y hh hτ (hηχ hy)))
private def nonprincipalA_fixedSliceTerm
      {Kη Kχ : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]
  let hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let G : Fin d → PDE.ScalarLp Ω (2 ) := fun i =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u))
  let W : Fin d → PDE.ScalarLp Ω (2 ) := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u)
  let H : Fin d → PDE.ScalarLp Ω (2 ) := fun i => G i + W i
  let ηMeas := η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U : Fin d → PDE.ScalarLp Ω (2 ) := fun j =>
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let aD : Fin d → Fin d → PDE.ScalarField d := fun i j y =>
    χ y * spatialDifferenceQuotient k h
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)
  ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (aD i j y * U j y) * H i y
private theorem abs_nonprincipalA_fixedSliceTerm_le
      {Kη Kχ C δ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ)
    (haRaw : ∀ (i j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)| ≤ C) :
    |nonprincipalA_fixedSliceTerm r₁ hΩ a η χ k h τ hχshift u| ≤
      (Fintype.card (Fin d) : ℝ) ^ 2 * C * ‖u‖ *
        (‖gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset
            (hχshift.mono_left (by
              intro y hy; apply subset_tsupport
              simp [χ.eq_one_on_inner y hy])) u)‖ + Kη * ‖u‖) := by
  let sharedTerm_d466bcf193 := (Fin d → PDE.ScalarLp Ω (2 ))


  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset (hχshift.mono_left (show tsupport η.toFun ⊆ tsupport χ.toFun by
        intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]))
  let G := fun i  => PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u))
  let W : sharedTerm_d466bcf193 := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u)
  let H : sharedTerm_d466bcf193 := fun i => G i + W i
  let ηMeas := η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U : sharedTerm_d466bcf193 := fun j =>
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let aD  := fun i j y =>
    χ y * spatialDifferenceQuotient k h
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)
  let g : ℝ := ‖gradientCLM hΩ (A u)‖
  let n : ℝ := ‖u‖
  have haDCont (i j : Fin d) : Continuous (aD i j) := by
    dsimp [aD]
    exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h
      (fun z  => reverseTimeCoefficient r₁ a z.1 z.2 i j)
      (reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j) hτ hχshift
  have haDBound (i j : Fin d) : ∀ y, ‖aD i j y‖ ≤ C := by
    apply norm_cutoff_mul_le_of_tsupport_bound χ _ hC
    intro y hy
    exact haRaw i j k h τ y hh hτ hy
  have haMeas (i j : Fin d) : AEStronglyMeasurable (aD i j) (PDE.volumeOn Ω) :=
    (haDCont i j).aestronglyMeasurable
  have haBoundAE (i j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖aD i j y‖ ≤ C :=
    Filter.Eventually.of_forall (haDBound i j)
  have hHAE (i : Fin d) : ⇑(H i) =ᵐ[PDE.volumeOn Ω] fun y => G i y + W i y := by
    change ⇑(G i + W i) =ᵐ[PDE.volumeOn Ω] fun y => G i y + W i y
    filter_upwards [MeasureTheory.Lp.coeFn_add (G i) (W i)] with y hadd
    rw [hadd]
    rfl
  have hUAE (j : Fin d) : ⇑(U j) =ᵐ[PDE.volumeOn Ω] fun y =>
      η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y := by
    simpa only [U] using scalarL2Multiplier_apply_ae η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  have hGNorm (i : Fin d) : ‖G i‖ ≤ g := by
    dsimp [G, g]
    exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le i _
  have hKη  := η.gradient_bound_nonneg
  have hWBase (i : Fin d)  :=
    norm_cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_le_gradient


      hΩ η χ subset_rfl i k h χ.tsupport_subset hχshift u
  have hWNorm (i : Fin d) : ‖W i‖ ≤ Kη * n := by
    calc
      ‖W i‖ ≤ Kη * ‖gradientCLM hΩ u‖ := by
        change ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u)‖ ≤ Kη * ‖gradientCLM hΩ u‖
        exact hWBase i
      _ ≤ Kη * n := by
        dsimp [n]
        exact mul_le_mul_of_nonneg_left (norm_gradientCLM_le_graph hΩ u) hKη
  have hHNorm (i : Fin d) : ‖H i‖ ≤ g + Kη * n := by
    calc
      ‖H i‖ ≤ ‖G i‖ + ‖W i‖ := norm_add_le _ _
      _ ≤ g + Kη * n := add_le_add (hGNorm i) (hWNorm i)
  have hUNorm (j : Fin d) : ‖U j‖ ≤ n := by
    calc
      ‖U j‖ ≤ ‖PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ u)‖ := by
        let sharedTerm_6676dab0a3 := ((PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        change ‖scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
          sharedTerm_6676dab0a3‖ ≤ _
        simpa only [one_mul] using
          (norm_scalarL2Multiplier_apply_le η.toFun ηMeas 1 zero_le_one ηBound
            sharedTerm_6676dab0a3)
      _ ≤ ‖gradientCLM hΩ u‖ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j _
      _ ≤ n := by
        dsimp [n]
        exact norm_gradientCLM_le_graph hΩ u
  have haTerm (i j : Fin d) :
      |∫ y in Ω, (aD i j y * U j y) * H i y| ≤
        C * n * (g + Kη * n) := by
    have hpair := abs_multiplier_pairing_le (aD i j) (haMeas i j) C n (g + Kη * n)
      hC (haBoundAE i j) (U j) (H i)
      (fun y => η y * PDE.hilbertVectorLpCoord Ω (2 ) j
        (gradientCLM hΩ u) y)
      (fun y => G i y + W i y) (hUAE j) (hHAE i) (hUNorm j) (hHNorm i)
      (norm_nonneg _) (by positivity)
    have heq : (∫ y in Ω, (aD i j y * U j y) * H i y) =
        ∫ y in Ω, (aD i j y *
          (η y * PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ u) y)) * (G i y + W i y) := by
      apply integral_congr_ae
      filter_upwards [hUAE j, hHAE i] with y hU hH
      rw [hU, hH]
    rw [heq]
    exact hpair
  have hsum := abs_sum_fin_fin_le
    _
    _ haTerm
  change |∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (aD i j y * U j y) * H i y| ≤ _
  calc
    _ ≤ (Fintype.card (Fin d) : ℝ) ^ 2 * (C * n * (g + Kη * n)) := hsum
    _ = _ := by dsimp only [g, n, A]; ring
private def nonprincipalDriftT_fixedSliceTerm
      {Kη Kχ : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]
  let hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let G : Fin d → PDE.ScalarLp Ω (2 ) := fun i =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u))
  let W : Fin d → PDE.ScalarLp Ω (2 ) := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u)
  let E : Fin d → PDE.ScalarLp Ω (2 ) := fun i => G i - W i
  let driftT : Fin d → PDE.ScalarField d := fun j y =>
    χ y * spatialTranslate k h
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  ∑ j : Fin d, ∫ y in Ω, (driftT j y * E j y) * V y
private theorem abs_nonprincipalDriftT_fixedSliceTerm_le
      {Kη Kχ C δ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)
    (hdriftTRaw : ∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialTranslate k h
          (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ C) :
    |nonprincipalDriftT_fixedSliceTerm r₁ hΩ a b η χ k h τ hχshift u| ≤
      (Fintype.card (Fin d) : ℝ) * C * ‖u‖ *
        (‖gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset
            (hχshift.mono_left (by
              intro y hy; apply subset_tsupport; change χ y ≠ 0
              rw [χ.eq_one_on_inner y hy]; exact one_ne_zero)) u)‖ + Kη * ‖u‖) := by
  let sharedTerm_5a09c27654 := (Fin d → PDE.ScalarLp Ω (2 ))

  let hηshift  := hχshift.mono_left (show tsupport η.toFun ⊆ tsupport χ.toFun by
      intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy])
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let G : sharedTerm_5a09c27654 := fun i =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u))
  let W : sharedTerm_5a09c27654 := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u)
  let E : sharedTerm_5a09c27654 := fun i => G i - W i
  let driftT  := fun j y =>
    χ y * spatialTranslate k h
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  let g : ℝ := ‖gradientCLM hΩ (A u)‖
  let n : ℝ := ‖u‖
  have hdriftTCont (j : Fin d) : Continuous (driftT j) := by
    dsimp [driftT]
    exact continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h
      _
      (reverseTime_drift_smoothOn_closedCylinder r₀ r₁ a b ha hb j) hτ hχshift
  have hdriftTBound (j : Fin d) : ∀ y, ‖driftT j y‖ ≤ C := by
    apply norm_cutoff_mul_le_of_tsupport_bound χ _ hC
    intro y hy
    exact hdriftTRaw j k h τ y hh hτ hy
  have hdriftTMeas (j : Fin d) : AEStronglyMeasurable (driftT j) (PDE.volumeOn Ω) :=
    (hdriftTCont j).aestronglyMeasurable
  have hdriftTBoundAE (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖driftT j y‖ ≤ C :=
    Filter.Eventually.of_forall (hdriftTBound j)
  have hVAE : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y := Filter.Eventually.of_forall fun _ => rfl
  have hEAE (i : Fin d) : ⇑(E i) =ᵐ[PDE.volumeOn Ω] fun y => G i y - W i y := by
    change ⇑(G i - W i) =ᵐ[PDE.volumeOn Ω] fun y => G i y - W i y
    filter_upwards [MeasureTheory.Lp.coeFn_sub (G i) (W i)] with y hsub
    rw [hsub]
    rfl

  have hKη  := η.gradient_bound_nonneg
  have hGNorm (i : Fin d) : ‖G i‖ ≤ g := by
    dsimp [G, g]
    exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le i _
  have hWNorm (i : Fin d) : ‖W i‖ ≤ Kη * n := by
    calc
      ‖W i‖ ≤ Kη * ‖gradientCLM hΩ u‖ := by
        change ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u)‖ ≤ Kη * ‖gradientCLM hΩ u‖
        exact norm_cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_le_gradient


          hΩ η χ subset_rfl i k h χ.tsupport_subset hχshift u
      _ ≤ Kη * n := by
        dsimp [n]
        exact mul_le_mul_of_nonneg_left (norm_gradientCLM_le_graph hΩ u) hKη
  have hENorm (i : Fin d) : ‖E i‖ ≤ g + Kη * n := by
    calc
      ‖E i‖ ≤ ‖G i‖ + ‖W i‖ := norm_sub_le _ _
      _ ≤ g + Kη * n := add_le_add (hGNorm i) (hWNorm i)
  have hterm (j : Fin d) :
      |∫ y in Ω, (driftT j y * E j y) * V y| ≤ C * n * (g + Kη * n) := by
    have hpair := abs_multiplier_pairing_le (driftT j) (hdriftTMeas j)
      C (g + Kη * n) n hC (hdriftTBoundAE j) (E j) V
      (fun y => G j y - W j y) (fun y => V y) (hEAE j) hVAE (hENorm j) (show ‖V‖ ≤ n by
          calc
            ‖V‖ ≤ ‖gradientCLM hΩ u‖ := by
              dsimp [V, A]
              exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
                hΩ η k h η.tsupport_subset hηshift u
            _ ≤ n := by dsimp [n]; exact norm_gradientCLM_le_graph hΩ u)
      (by positivity) (norm_nonneg _)
    have heq : (∫ y in Ω, (driftT j y * E j y) * V y) =
        ∫ y in Ω, (driftT j y * (G j y - W j y)) * V y := by
      apply integral_congr_ae
      filter_upwards [hEAE j] with y hE
      rw [hE]
    rw [heq]
    calc
      _ ≤ C * (g + Kη * n) * n := hpair
      _ = C * n * (g + Kη * n) := by ring
  have hsum := abs_sum_fin_le
    _
    _ hterm
  change |∑ j : Fin d, ∫ y in Ω, (driftT j y * E j y) * V y| ≤ _
  calc
    _ ≤ (Fintype.card (Fin d) : ℝ) * (C * n * (g + Kη * n)) := hsum
    _ = _ := by dsimp only [g, n, A]; ring
private def nonprincipalDriftD_fixedSliceTerm
      {Kη Kχ : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]
  let hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let ηMeas := η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U : Fin d → PDE.ScalarLp Ω (2 ) := fun j =>
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let driftD : Fin d → PDE.ScalarField d := fun j y =>
    χ y * spatialDifferenceQuotient k h
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  ∑ j : Fin d, ∫ y in Ω, (driftD j y * U j y) * V y
private theorem abs_nonprincipalDriftD_fixedSliceTerm_le
      {Kη Kχ C δ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)
    (hdriftDRaw : ∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ C) :
    |nonprincipalDriftD_fixedSliceTerm r₁ hΩ a b η χ k h τ hχshift u| ≤
      (Fintype.card (Fin d) : ℝ) * C * ‖u‖ ^ 2 := by

  let hηshift  := hχshift.mono_left (show tsupport η.toFun ⊆ tsupport χ.toFun by
      intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy])
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let ηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U  := fun j =>
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let driftD  := fun j y =>
    χ y * spatialDifferenceQuotient k h
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  let n : ℝ := ‖u‖
  have hdriftDCont (j : Fin d) : Continuous (driftD j) := by
    dsimp [driftD]
    exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h
      (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
      (reverseTime_drift_smoothOn_closedCylinder r₀ r₁ a b ha hb j) hτ hχshift
  have hdriftDBound (j : Fin d) : ∀ y, ‖driftD j y‖ ≤ C := by
    apply norm_cutoff_mul_le_of_tsupport_bound χ _ hC
    intro y hy
    exact hdriftDRaw j k h τ y hh hτ hy
  have hdriftDMeas (j : Fin d) : AEStronglyMeasurable (driftD j) (PDE.volumeOn Ω) :=
    (hdriftDCont j).aestronglyMeasurable
  have hdriftDBoundAE (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖driftD j y‖ ≤ C :=
    Filter.Eventually.of_forall (hdriftDBound j)
  have hVAE : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y := Filter.Eventually.of_forall fun _ => rfl
  have hUAE (j : Fin d) : ⇑(U j) =ᵐ[PDE.volumeOn Ω] fun y =>
      η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y := by
    simpa only [U] using scalarL2Multiplier_apply_ae η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))

  have hUNorm (j : Fin d) : ‖U j‖ ≤ n := by
    calc
      ‖U j‖ ≤ ‖PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ u)‖ := by
        let sharedTerm_6bddaf7e49 := ((PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        change ‖scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
          sharedTerm_6bddaf7e49‖ ≤ _
        simpa only [one_mul] using norm_scalarL2Multiplier_apply_le η.toFun ηMeas 1
          zero_le_one ηBound sharedTerm_6bddaf7e49
      _ ≤ ‖gradientCLM hΩ u‖ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j _
      _ ≤ n := by dsimp [n]; exact norm_gradientCLM_le_graph hΩ u
  have hterm (j : Fin d) :
      |∫ y in Ω, (driftD j y * U j y) * V y| ≤ C * n ^ 2 := by
    have hpair := abs_multiplier_pairing_le (driftD j) (hdriftDMeas j) C n n hC
      (hdriftDBoundAE j) (U j) V
      (fun y => η y * PDE.hilbertVectorLpCoord Ω (2 ) j
        (gradientCLM hΩ u) y) (fun y => V y) (hUAE j) hVAE (hUNorm j) (show ‖V‖ ≤ n by
            calc
              ‖V‖ ≤ ‖gradientCLM hΩ u‖ := by
                dsimp [V, A]
                exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
                  hΩ η k h η.tsupport_subset hηshift u
              _ ≤ n := by dsimp [n]; exact norm_gradientCLM_le_graph hΩ u)
      (norm_nonneg _) (norm_nonneg _)
    have heq : (∫ y in Ω, (driftD j y * U j y) * V y) =
        ∫ y in Ω, (driftD j y *
          (η y * PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ u) y)) * V y := by
      apply integral_congr_ae
      filter_upwards [hUAE j] with y hU
      rw [hU]
    rw [heq]
    calc
      _ ≤ C * n * n := hpair
      _ = C * n ^ 2 := by ring
  have hsum := abs_sum_fin_le
    _ (C * n ^ 2) hterm
  change |∑ j : Fin d, ∫ y in Ω, (driftD j y * U j y) * V y| ≤ _
  calc
    _ ≤ (Fintype.card (Fin d) : ℝ) * (C * n ^ 2) := hsum
    _ = _ := by dsimp only [n]; ring
private def nonprincipalGammaT_fixedSliceTerm
      {Kη Kχ : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (c : PDE.TimeScalarField d)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]
  let hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let gammaT : PDE.ScalarField d := fun y => χ y * spatialTranslate k h
    (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  ∫ y in Ω, (gammaT y * V y) * V y
private theorem abs_nonprincipalGammaT_fixedSliceTerm_le
      {Kη Kχ C δ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)
    (hgammaTRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialTranslate k h
          (fun z  => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ C) :
    |nonprincipalGammaT_fixedSliceTerm r₁ hΩ c η χ k h τ hχshift u| ≤ C * ‖u‖ ^ 2 := by

  let hηshift  := hχshift.mono_left (show tsupport η.toFun ⊆ tsupport χ.toFun by
      intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy])
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let gammaT  := fun y => χ y * spatialTranslate k h
    (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  let n : ℝ := ‖u‖


  have hmeas : AEStronglyMeasurable gammaT (PDE.volumeOn Ω) := (show Continuous gammaT by
      dsimp [gammaT]
      exact continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h
        _
        (reverseTime_scalar_smoothOn_closedCylinder r₀ r₁ c hc) hτ hχshift).aestronglyMeasurable
  have hboundAE : ∀ᵐ y ∂PDE.volumeOn Ω, ‖gammaT y‖ ≤ C := Filter.Eventually.of_forall (by
      apply norm_cutoff_mul_le_of_tsupport_bound χ _ hC
      intro y hy
      exact hgammaTRaw k h τ y hh hτ hy)
  have hVAE : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y := Filter.Eventually.of_forall fun _ => rfl
  have hVNorm : ‖V‖ ≤ n := by
    calc
      ‖V‖ ≤ ‖gradientCLM hΩ u‖ := by
        dsimp [V, A]
        exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
          hΩ η k h η.tsupport_subset hηshift u
      _ ≤ n := by dsimp [n]; exact norm_gradientCLM_le_graph hΩ u
  have hpair := abs_multiplier_pairing_le gammaT hmeas C n n hC hboundAE V V
    (fun y => V y) (fun y => V y) hVAE hVAE hVNorm hVNorm (norm_nonneg _) (norm_nonneg _)
  change |∫ y in Ω, (gammaT y * V y) * V y| ≤ _
  calc
    _ ≤ C * n * n := hpair
    _ = C * ‖u‖ ^ 2 := by dsimp only [n]; ring
private def nonprincipalGammaD_fixedSliceTerm
      {Kη Kχ : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (c : PDE.TimeScalarField d)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; simp [χ.eq_one_on_inner y hy]
  let hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let ηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U₀ : PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound (valueCLM hΩ u)
  let gammaD : PDE.ScalarField d := fun y => χ y * spatialDifferenceQuotient k h
    (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  ∫ y in Ω, (gammaD y * U₀ y) * V y
private theorem abs_nonprincipalGammaD_fixedSliceTerm_le
      {Kη Kχ C δ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (hC : 0 ≤ C) (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)
    (hgammaDRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ C) :
    |nonprincipalGammaD_fixedSliceTerm r₁ hΩ c η χ k h τ hχshift u| ≤ C * ‖u‖ ^ 2 := by
  let sharedTerm_f498f7e40b := ((fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2))

  let hηshift  := hχshift.mono_left (by
      intro y hy; apply subset_tsupport; change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]; exact one_ne_zero)
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 ) := valueCLM hΩ (A u)
  let ηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U₀ : PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound (valueCLM hΩ u)
  let gammaD  := fun y => χ y * spatialDifferenceQuotient k h
    sharedTerm_f498f7e40b (τ, y)
  let n : ℝ := ‖u‖





  have hU₀AE : ⇑U₀ =ᵐ[PDE.volumeOn Ω] fun y => η y * valueCLM hΩ u y := by
    simpa only [U₀] using scalarL2Multiplier_apply_ae η.toFun ηMeas 1 zero_le_one ηBound
      (valueCLM hΩ u)


  have hpair := abs_multiplier_pairing_le gammaD (show Continuous gammaD by
      dsimp [gammaD]
      exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h
        sharedTerm_f498f7e40b
        (reverseTime_scalar_smoothOn_closedCylinder r₀ r₁ c hc) hτ hχshift).aestronglyMeasurable C n n hC (Filter.Eventually.of_forall (by
      apply norm_cutoff_mul_le_of_tsupport_bound χ _ hC
      intro y hy
      exact hgammaDRaw k h τ y hh hτ hy)) U₀ V
    (fun y => η y * valueCLM hΩ u y) (fun y => V y) hU₀AE (Filter.Eventually.of_forall fun _ => rfl) (by
        calc
          ‖U₀‖ ≤ ‖valueCLM hΩ u‖ := by
            change ‖scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound (valueCLM hΩ u)‖ ≤ _
            simpa only [one_mul] using norm_scalarL2Multiplier_apply_le η.toFun ηMeas 1
              zero_le_one ηBound (valueCLM hΩ u)
          _ ≤ n := by dsimp [n]; exact norm_valueCLM_le_graph hΩ u) (by
        calc
          ‖V‖ ≤ ‖gradientCLM hΩ u‖ := by
            dsimp [V, A]
            exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
              hΩ η k h η.tsupport_subset hηshift u
          _ ≤ n := by dsimp [n]; exact norm_gradientCLM_le_graph hΩ u)
    (norm_nonneg _) (norm_nonneg _)
  have heq : (∫ y in Ω, (gammaD y * U₀ y) * V y) =
      ∫ y in Ω, (gammaD y * (η y * valueCLM hΩ u y)) * V y := by
    apply integral_congr_ae
    filter_upwards [hU₀AE] with y hU
    rw [hU]
  change |∫ y in Ω, (gammaD y * U₀ y) * V y| ≤ _
  rw [heq]
  calc
    _ ≤ C * n * n := hpair
    _ = C * ‖u‖ ^ 2 := by dsimp only [n]; ring
variable (q D C K g n : ℝ)

private theorem a_fixedSlice_raw_to_young

    (hraw : |q| ≤ D ^ 2 * C * n * (g + K * n))
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hK : 0 ≤ K) (hg : 0 ≤ g) (hn : 0 ≤ n) :
    |q| ≤ (1 + D ^ 2 * C * K + D * C * K + D * C + 2 * C) * n ^ 2 +
      (D ^ 2 * C * (2 + K) + D * C * (2 + K)) * g * n := by
  have h₁ : 0 ≤ (1 + D * C * K + D * C + 2 * C) * n ^ 2 := by positivity
  have h₂ : 0 ≤ (D ^ 2 * C * (1 + K) + D * C * (2 + K)) * g * n := by positivity
  nlinarith
private theorem driftT_fixedSlice_raw_to_young

    (hraw : |q| ≤ D * C * n * (g + K * n))
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hK : 0 ≤ K) (hg : 0 ≤ g) (hn : 0 ≤ n) :
    |q| ≤ (1 + D ^ 2 * C * K + D * C * K + D * C + 2 * C) * n ^ 2 +
      (D ^ 2 * C * (2 + K) + D * C * (2 + K)) * g * n := by
  have h₁ : 0 ≤ (1 + D ^ 2 * C * K + D * C + 2 * C) * n ^ 2 := by positivity
  have h₂ : 0 ≤ (D ^ 2 * C * (2 + K) + D * C * (1 + K)) * g * n := by positivity
  nlinarith
variable (q D C K n : ℝ)

private theorem quadratic_fixedSlice_raw_to_young
     (hraw : |q| ≤ D * C * n ^ 2)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hK : 0 ≤ K) (_hn : 0 ≤ n) :
    |q| ≤ (1 + D ^ 2 * C * K + D * C * K + D * C + 2 * C) * n ^ 2 := by
  have h₁ : 0 ≤ (1 + D ^ 2 * C * K + D * C * K + 2 * C) * n ^ 2 := by positivity
  nlinarith
private theorem scalar_fixedSlice_raw_to_young
     (hraw : |q| ≤ C * n ^ 2)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hK : 0 ≤ K) (_hn : 0 ≤ n) :
    |q| ≤ (1 + D ^ 2 * C * K + D * C * K + D * C + 2 * C) * n ^ 2 := by
  have h₁ : 0 ≤ (1 + D ^ 2 * C * K + D * C * K + D * C + C) * n ^ 2 := by positivity
  nlinarith
section
variable {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}
variable (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
variable (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
variable (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
variable (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
variable (k : Fin d) (h τ : ℝ)
variable (hχshift : Set.MapsTo
  (fun y  => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω)
variable (hηshift : Set.MapsTo
  (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
variable (u : H10HilbertGraph hΩ)
private theorem nonprincipalA_fixedSliceTerm_eq_pointwise :
    nonprincipalA_fixedSliceTerm r₁ hΩ a η χ k h τ hχshift u =
      ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (χ y * spatialDifferenceQuotient k h
          (fun z  => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y) *
          (η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y)) *
          (PDE.hilbertVectorLpCoord Ω (2 ) i
            (gradientCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)) y +
            cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
              (valueCLM hΩ u) y) := by
  let sharedTerm_8243801546 := (Fin d → PDE.ScalarLp Ω (2 ))

  let G : sharedTerm_8243801546 := fun i =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ ((localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift) u))
  let W : sharedTerm_8243801546 := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u)

  let ηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U : sharedTerm_8243801546 := fun j =>
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  have hHAE (i : Fin d) : ⇑((fun i => G i + W i) i) =ᵐ[PDE.volumeOn Ω] fun y => G i y + W i y := by
    filter_upwards [MeasureTheory.Lp.coeFn_add (G i) (W i)] with y hy
    rw [hy]; rfl
  have hUAE (j : Fin d) : ⇑(U j) =ᵐ[PDE.volumeOn Ω] fun y =>
      η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y := by
    simpa only [U] using scalarL2Multiplier_apply_ae η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  unfold nonprincipalA_fixedSliceTerm; apply Finset.sum_congr rfl
  intro i _; apply Finset.sum_congr rfl
  intro j _; apply integral_congr_ae
  filter_upwards [hUAE j, hHAE i] with y hU hH; rw [hU, hH]
private theorem nonprincipalDriftT_fixedSliceTerm_eq_pointwise :
    nonprincipalDriftT_fixedSliceTerm r₁ hΩ a b η χ k h τ hχshift u =
      ∑ j : Fin d, ∫ y in Ω,
        (χ y * spatialTranslate k h
          (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y) *
          (PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)) y -
            cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
              (valueCLM hΩ u) y)) *
          valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u) y := by

  let G := fun i  => PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ ((localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift) u))
  let W  := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u)

  have hEAE (i : Fin d) : ⇑((fun i => G i - W i) i) =ᵐ[PDE.volumeOn Ω] fun y => G i y - W i y := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub (G i) (W i)] with y hy
    rw [hy]; rfl
  unfold nonprincipalDriftT_fixedSliceTerm; apply Finset.sum_congr rfl
  intro j _; apply integral_congr_ae
  filter_upwards [hEAE j] with y hE; rw [hE]
private theorem nonprincipalDriftD_fixedSliceTerm_eq_pointwise :
    nonprincipalDriftD_fixedSliceTerm r₁ hΩ a b η χ k h τ hχshift u =
      ∑ j : Fin d, ∫ y in Ω,
        (χ y * spatialDifferenceQuotient k h
          (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y) *
          (η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y)) *
          valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u) y := by
  let ηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U  := fun j =>
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  have hUAE (j : Fin d) : ⇑(U j) =ᵐ[PDE.volumeOn Ω] fun y =>
      η y * PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y := by
    simpa only [U] using scalarL2Multiplier_apply_ae η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  unfold nonprincipalDriftD_fixedSliceTerm; apply Finset.sum_congr rfl
  intro j _; apply integral_congr_ae
  filter_upwards [hUAE j] with y hU; rw [hU]
private theorem nonprincipalGammaD_fixedSliceTerm_eq_pointwise :
    nonprincipalGammaD_fixedSliceTerm r₁ hΩ c η χ k h τ hχshift u =
      ∫ y in Ω,
        (χ y * spatialDifferenceQuotient k h
          (fun z  => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y) *
          (η y * valueCLM hΩ u y)) *
          valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u) y := by
  let ηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]; exact η.le_one y
  let U₀ : PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound (valueCLM hΩ u)

  unfold nonprincipalGammaD_fixedSliceTerm; apply integral_congr_ae
  filter_upwards [(show ⇑U₀ =ᵐ[PDE.volumeOn Ω] fun y => η y * valueCLM hΩ u y by
      simpa only [U₀] using scalarL2Multiplier_apply_ae η.toFun ηMeas 1 zero_le_one ηBound
        (valueCLM hΩ u))] with y hU₀; rw [hU₀]
end
variable {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}

private theorem nonprincipalRemainder_bound_of_rawAmplitude

    {C δ : ℝ} (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
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
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε)
    (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hχshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)
    (hsourceRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => F (r₁ - z.1) z.2) (τ, y)| ≤ C)
    (haRaw : ∀ (i j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)| ≤ C)
    (hdriftTRaw : ∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialTranslate k h
          (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ C)
    (hdriftDRaw : ∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ C)
    (hgammaTRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialTranslate k h
          (fun z  => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ C)
    (hgammaDRaw : ∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
        |spatialDifferenceQuotient k h
          (fun z  => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ C) :
    |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
        r₁ hΩ a b c F η χ k h τ
        (hχshift.mono_left (by
          intro y hy
          apply subset_tsupport
          simp [χ.eq_one_on_inner y hy])) u| ≤
      ε * ‖gradientCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset
          (hχshift.mono_left (by
            intro y hy
            apply subset_tsupport
            simp [χ.eq_one_on_inner y hy])) u)‖ ^ 2 +
        (1 + C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun) +
          5 * (1 + (Fintype.card (Fin d) : ℝ) ^ 2 * C * Kη +
            (Fintype.card (Fin d) : ℝ) * C * Kη +
            (Fintype.card (Fin d) : ℝ) * C + 2 * C) +
          (2 * ((Fintype.card (Fin d) : ℝ) ^ 2 * C * (2 + Kη) +
            (Fintype.card (Fin d) : ℝ) * C * (2 + Kη))) ^ 2 / (4 * ε)) *
          (1 + ‖u‖ ^ 2) := by
  let D : ℝ := Fintype.card (Fin d)
  let S : ℝ := C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun)
  let B : ℝ := D ^ 2 * C * (2 + Kη) + D * C * (2 + Kη)
  let A₁ : ℝ := 1 + D ^ 2 * C * Kη + D * C * Kη + D * C + 2 * C

  let hηshift  := hχshift.mono_left (by
      intro y hy
      apply subset_tsupport
      change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]
      exact one_ne_zero)
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let g : ℝ := ‖gradientCLM hΩ (A u)‖
  let n : ℝ := ‖u‖
  let s : ℝ := ∫ y in Ω,
    (η y * spatialDifferenceQuotient k h
      (fun z  => F (r₁ - z.1) z.2) (τ, y)) * valueCLM hΩ (A u) y
  let qA : ℝ := nonprincipalA_fixedSliceTerm r₁ hΩ a η χ k h τ hχshift u
  let qT : ℝ := nonprincipalDriftT_fixedSliceTerm r₁ hΩ a b η χ k h τ hχshift u
  let qD : ℝ := nonprincipalDriftD_fixedSliceTerm r₁ hΩ a b η χ k h τ hχshift u
  let qγT : ℝ := nonprincipalGammaT_fixedSliceTerm r₁ hΩ c η χ k h τ hχshift u
  let qγD : ℝ := nonprincipalGammaD_fixedSliceTerm r₁ hΩ c η χ k h τ hχshift u
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hKη  := η.gradient_bound_nonneg
  have hg : 0 ≤ g := norm_nonneg _
  have hn : 0 ≤ n := norm_nonneg _




  have hqAraw := abs_nonprincipalA_fixedSliceTerm_le r₀ r₁ hΩ a ha η χ hC
    k h hh hχshift τ hτ u haRaw
  have hqTraw := abs_nonprincipalDriftT_fixedSliceTerm_le r₀ r₁ hΩ a b ha hb η χ hC
    k h hh hχshift τ hτ u hdriftTRaw
  have hqDraw := abs_nonprincipalDriftD_fixedSliceTerm_le r₀ r₁ hΩ a b ha hb η χ hC
    k h hh hχshift τ hτ u hdriftDRaw
  have hqγTraw := abs_nonprincipalGammaT_fixedSliceTerm_le r₀ r₁ hΩ c hc η χ hC
    k h hh hχshift τ hτ u hgammaTRaw
  have hqγDraw := abs_nonprincipalGammaD_fixedSliceTerm_le r₀ r₁ hΩ c hc η χ hC
    k h hh hχshift τ hτ u hgammaDRaw










  have hfinal := abs_six_terms_le_young s qA qT qD qγT qγD S A₁ B g n ε
    ((id (abs_source_fixedSlice_le_sq_add r₀ r₁ hΩ F hF η χ δ hC k h hh hχshift τ hτ u hsourceRaw))) (by
              dsimp only [A₁, B]
              exact a_fixedSlice_raw_to_young qA D C Kη g n (by
                  simpa only [qA, D, g, n, A, hηshift] using hqAraw) hD hC hKη hg hn) (by
              dsimp only [A₁, B]
              exact driftT_fixedSlice_raw_to_young qT D C Kη g n (by
                  simpa only [qT, D, g, n, A, hηshift] using hqTraw) hD hC hKη hg hn) (by
              dsimp only [A₁]
              exact quadratic_fixedSlice_raw_to_young qD D C Kη n (hqDraw) hD hC hKη hn) (by
              dsimp only [A₁]
              exact scalar_fixedSlice_raw_to_young qγT D C Kη n (hqγTraw) hD hC hKη hn) (by
              dsimp only [A₁]
              exact scalar_fixedSlice_raw_to_young qγD D C Kη n (hqγDraw) hD hC hKη hn) (by dsimp [S]; positivity) (by dsimp [A₁]; positivity) hε
  have hqAbridge :=
    nonprincipalA_fixedSliceTerm_eq_pointwise r₁ hΩ a η χ k h τ hχshift hηshift u
  change qA = _ at hqAbridge
  have hqTbridge :=
    nonprincipalDriftT_fixedSliceTerm_eq_pointwise r₁ hΩ a b η χ k h τ hχshift hηshift u
  change qT = _ at hqTbridge
  have hqDbridge :=
    nonprincipalDriftD_fixedSliceTerm_eq_pointwise r₁ hΩ a b η χ k h τ hχshift hηshift u
  change qD = _ at hqDbridge
  have hqγDbridge :=
    nonprincipalGammaD_fixedSliceTerm_eq_pointwise r₁ hΩ c η χ k h τ hχshift hηshift u
  change qγD = _ at hqγDbridge
  rw [hqAbridge, hqTbridge, hqDbridge, hqγDbridge] at hfinal
  simpa only [s, qA, qT, qD, qγT, qγD, g, n, A, hηshift, localizedSpatialDifferenceQuotientH10NonprincipalRemainder,
    nonprincipalGammaT_fixedSliceTerm] using hfinal

variable (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)

/-- The six nonprincipal localized commutator terms obey a uniform raw Young
bound before multiplication by the scalar time test. -/
theorem exists_smallStep_localizedSpatialDifferenceQuotientH10_nonprincipalRemainder_bound


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
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ Cε : ℝ, 0 ≤ Cε ∧
          ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
            ∀ hχshift : Set.MapsTo
              (fun y  => y + h • PDE.basisVec k)
              (tsupport χ.toFun) Ω,
            ∀ (τ : ℝ), τ ∈ Set.Icc 0 (r₁ - r₀) →
              ∀ u : H10HilbertGraph hΩ,
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
                let A := localizedSpatialDifferenceQuotientH10CLM
                  hΩ η k h η.tsupport_subset hηshift
                |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
                    r₁ hΩ a b c F η χ k h τ hηshift u| ≤
                  ε * ‖gradientCLM hΩ (A u)‖ ^ 2 +
                    Cε * (1 + ‖u‖ ^ 2) := by
  obtain ⟨δ, C, hδ, hC, _hshiftRaw, hsourceRaw, haRaw, hdriftTRaw,
    hdriftDRaw, hgammaTRaw, hgammaDRaw⟩ :=
    exists_reverseTimeSpatialRawAmplitude_bounds_of_smoothOnNeighborhood
      r₀ r₁ hΩ χ a b c F ha hb hc hF
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  let D : ℝ := Fintype.card (Fin d)
  let S : ℝ := C ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun)
  let B : ℝ := D ^ 2 * C * (2 + Kη) + D * C * (2 + Kη)
  let A₁ : ℝ := 1 + D ^ 2 * C * Kη + D * C * Kη + D * C + 2 * C
  refine ⟨1 + S + 5 * A₁ + (2 * B) ^ 2 / (4 * ε), ?_, ?_⟩
  ·
    have hKη  := η.gradient_bound_nonneg



    positivity
  intro k h hh hχshift τ hτ u
  dsimp
  simpa only [D, S, B, A₁, gradientCLM_apply, Submodule.norm_coe] using
    nonprincipalRemainder_bound_of_rawAmplitude r₀ r₁ hΩ a b c F ha hb hc hF η χ hC ε hε
      k h hh hχshift τ hτ u hsourceRaw haRaw hdriftTRaw hdriftDRaw hgammaTRaw hgammaDRaw

/-- The nonprincipal localized commutator remainder has a constant fixed
before the coefficient data, under the literal uniform spatial majorants of
the Caccioppoli estimate. -/
theorem exists_uniform_nonprincipalRemainder_bound_of_majorants


    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (δ M : ℝ) (hM : 0 ≤ M)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧
      ∀ (a : CoefficientField d) (b : PDE.TimeVectorField d)
        (c F : PDE.TimeScalarField d),
        ∀ (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
          (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
          spatialMatrixFDerivFrobeniusNorm
            (fun w  => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
          PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
          spatialVectorFDerivFrobeniusNorm
            (fun w  => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
          |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
          spatialScalarFDerivEuclideanNorm
            (fun w  => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
          spatialScalarFDerivEuclideanNorm
            (fun w  => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ),
          ∀ (τ : ℝ), τ ∈ Set.Icc 0 (r₁ - r₀) →
            ∀ u : H10HilbertGraph hΩ,
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
                  (tsupport η.toFun) Ω := hχshift.mono_left hηχ
              let A := localizedSpatialDifferenceQuotientH10CLM
                hΩ η k h η.tsupport_subset hηshift
              |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
                  r₁ hΩ a b c F η χ k h τ hηshift u| ≤
                ε * ‖gradientCLM hΩ (A u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2) := by
  let D : ℝ := Fintype.card (Fin d)
  let S : ℝ := M ^ 2 * (PDE.volumeOn Ω).real (tsupport χ.toFun)
  let B : ℝ := D ^ 2 * M * (2 + Kη) + D * M * (2 + Kη)
  let A₁ : ℝ := 1 + D ^ 2 * M * Kη + D * M * Kη + D * M + 2 * M
  refine ⟨1 + S + 5 * A₁ + (2 * B) ^ 2 / (4 * ε), ?_, ?_⟩
  ·
    have hKη  := η.gradient_bound_nonneg

    have hB : 0 ≤ B := by dsimp [B]; positivity

    positivity
  intro a b c F ha hb hc hF hA hB hBD hq hqD hfD k h hh τ hτ u
  obtain ⟨_hshiftRaw, hsourceRaw, haRaw, hdriftTRaw, hdriftDRaw,
    hgammaTRaw, hgammaDRaw⟩ :=
    reverseTimeSpatialRawAmplitude_bounds_of_majorants r₀ r₁ χ δ M hcarrier
      a b c F ha hb hc hF hA hB hBD hq hqD hfD
  let hχshift  :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  simpa only [D, S, B, A₁, hχshift] using
    nonprincipalRemainder_bound_of_rawAmplitude r₀ r₁ hΩ a b c F ha hb hc hF η χ hM ε hε
      k h hh hχshift τ hτ u hsourceRaw haRaw hdriftTRaw hdriftDRaw hgammaTRaw hgammaDRaw
end HypoellipticAleksandrov.Parabolic.Dirichlet
