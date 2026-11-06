module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Reverse-time spatial weak derivatives

This module passes the spatial weak-gradient information in a reverse-time
energy carrier to its literal reverse-time product representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} (τ : ℝ)

private theorem isClosedEmbedding_timeSlice  :
    IsClosedEmbedding (Prod.mk τ : PDE.Vec d → TimeVelocity d) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_const.prodMk continuous_id) (fun x y h => by
      simp_all) ?_
  intro s hs
  have himage : Prod.mk τ '' s = ({τ}) ×ˢ s := by
    grind
  rw [himage]
  exact isClosed_singleton.prod hs

private theorem hasCompactSupport_timeSlice
     (φ : TimeVelocity d → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun y : PDE.Vec d => φ (τ, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isClosedEmbedding_timeSlice (d := d) τ).isCompact_preimage hφ) ?_
  intro y hy
  exact subset_tsupport φ hy

private theorem tsupport_timeSlice_subset
     {Ω : Set (PDE.Vec d)} {T : ℝ} (τ : ℝ) (φ : TimeVelocity d → ℝ)
    (hφ : tsupport φ ⊆ reverseTimeOpenInterval T ×ˢ Ω) :
    tsupport (fun y : PDE.Vec d => φ (τ, y)) ⊆ Ω := by
  intro y hy
  have hclosed : IsClosed ((Prod.mk τ) ⁻¹' tsupport φ) :=
    (isClosed_tsupport φ).preimage (continuous_const.prodMk continuous_id)
  have hsupport : Function.support (fun y : PDE.Vec d => φ (τ, y)) ⊆
      (Prod.mk τ) ⁻¹' tsupport φ := by
    intro x hx
    exact subset_tsupport φ hx
  have hmem : y ∈ (Prod.mk τ) ⁻¹' tsupport φ := closure_minimal hsupport hclosed hy
  grind

private def timeSliceWeakTestFunction
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (τ : ℝ) (φ : TimeVelocity d → ℝ)
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ)
    (hφsupport : tsupport φ ⊆ reverseTimeOpenInterval T ×ˢ Ω) :
    PDE.WeakTestFunction Ω where
  toFun := fun y => φ (τ, y)
  contDiff := hφsmooth.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport := hasCompactSupport_timeSlice τ φ hφcompact
  tsupport_subset := tsupport_timeSlice_subset τ φ hφsupport

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)

private theorem velocityGradient_timeSlice_eq_partialDeriv
     {T : ℝ}
    (τ : ℝ) (φ : TimeVelocity d → ℝ)
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ)
    (hφsupport : tsupport φ ⊆ reverseTimeOpenInterval T ×ˢ Ω)
    (y : PDE.Vec d) (i : Fin d) :
    velocityGradient φ (τ, y) i =
      (timeSliceWeakTestFunction τ φ hφsmooth hφcompact hφsupport).partialDeriv i y := by
  have hslice := (hφsmooth.differentiable (by simp) (τ, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right τ y)
  change fderiv ℝ φ _ _ =
    fderiv ℝ (φ ∘ Prod.mk τ) y _
  rw [hslice.fderiv]
  rfl

private theorem h10HilbertGraph_integral_partialDeriv
    
    (v : H10HilbertGraph hΩ) (i : Fin d) (ψ : PDE.WeakTestFunction Ω) :
    (∫ y, valueCLM hΩ v y * ψ.partialDeriv i y ∂PDE.volumeOn Ω) =
      -∫ y, gradientCLM hΩ v y i * ψ y ∂PDE.volumeOn Ω := by
  let w  := PDE.H1HilbertGraph.toH1Graph (v : PDE.H1HilbertGraph Ω)
  have hzero :
      (∫ y, w.1.1 y * ψ.partialDeriv i y ∂PDE.volumeOn Ω) +
        ∫ y, w.1.2 y i * ψ y ∂PDE.volumeOn Ω = 0 := (PDE.mem_weakGradientGraph_iff_integral w.1).mp w.2 i ψ
  exact eq_neg_of_add_eq_zero_left hzero

private theorem integrable_mul_of_memLp_two_of_continuous_compact
     {W q : TimeVelocity d → ℝ}
    {S : Set (TimeVelocity d)}
    (hW : MemLp W (2 : ℝ≥0∞) (timeVelocityVolumeOn S))
    (hq : Continuous q) (hqcompact : HasCompactSupport q) :
    Integrable (fun z => W z * q z) (timeVelocityVolumeOn S) := by
  have hqLp : MemLp q (2) (timeVelocityVolumeOn S) :=
    (hq.memLp_of_hasCompactSupport hqcompact).restrict S
  simpa only [Pi.mul_def] using hW.integrable_mul hqLp

/-- Reverse-time product representatives of a spatial Sobolev curve retain
their joint raw weak velocity derivatives. -/
theorem reverseTime_hasWeakVelocityPartialDerivOn_of_product_representatives
     (T : ℝ)
    (u : ReverseTimeL2V hΩ T)
    (U : TimeVelocity d → ℝ)
    (hU : MemLp U (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)))
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume T,
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, MemLp (G j) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume T, ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j) :
    ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn
        (reverseTimeOpenInterval T ×ˢ Ω) i U (G i) := by
  intro i φ hφsmooth hφcompact hφsupport
  letI : SFinite (reverseTimeVolume T) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  let ψ  := fun τ =>
    timeSliceWeakTestFunction τ φ hφsmooth hφcompact hφsupport
  let dφ  := fun z => velocityGradient φ z i
  have hdφcontinuous : Continuous dφ := (hφsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφcompact : HasCompactSupport dφ := hφcompact.fderiv_apply (𝕜 := ℝ) _
  have hleft  :=
    integrable_mul_of_memLp_two_of_continuous_compact hU hdφcontinuous hdφcompact
  have hright  :=
    integrable_mul_of_memLp_two_of_continuous_compact (hG i) hφsmooth.continuous hφcompact
  change (∫ z, U z * velocityGradient φ z i
      ∂timeVelocityVolumeOn _) =
    -∫ z, G i z * φ z
      ∂timeVelocityVolumeOn _
  rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn] at hleft hright ⊢
  rw [integral_prod _ hleft, integral_prod _ hright, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hUslice, hGslice] with τ hUτ hGτ
  have hleftSlice :
      (∫ y, U (τ, y) * dφ (τ, y) ∂PDE.volumeOn Ω) =
        ∫ y, valueCLM hΩ (u τ) y * (ψ τ).partialDeriv i y
          ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards [hUτ] with y hy
    rw [hy]
    change valueCLM hΩ _ y * velocityGradient φ _ i =
      valueCLM hΩ _ y *
        (timeSliceWeakTestFunction τ φ hφsmooth hφcompact hφsupport).partialDeriv i y
    rw [velocityGradient_timeSlice_eq_partialDeriv]
  have hrightSlice :
      (∫ y, G i (τ, y) * φ (τ, y) ∂PDE.volumeOn Ω) =
        ∫ y, gradientCLM hΩ (u τ) y i * ψ τ y ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards [hGτ i] with y hy
    aesop
  rw [hleftSlice, hrightSlice]
  exact h10HilbertGraph_integral_partialDeriv hΩ _ i _

end HypoellipticAleksandrov.Parabolic.Dirichlet
